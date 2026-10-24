"""An expert that decides magma implications with the Vampire theorem prover.

MagmaExpert refutes an implication with a counterexample of bounded size and
otherwise accepts it, so an accepted implication may still fail in a larger
magma. VampireExpert asks Vampire (https://vprover.github.io) instead, which
tries to prove the implication in equational logic, valid in every magma by
Birkhoff's completeness theorem, and searches for a finite counterexample of
any size. An implication is then confirmed only when it is proved.

Vampire may also show an implication false by saturation, without a finite
model. A counterexample still exists: the free magma over the premise laws,
whose elements are the terms modulo the equations derivable from the premise,
satisfies exactly the derivable laws. Asking Vampire about each law in turn
gives its row, as far as Vampire decides them.

The Mace4 model finder (https://www.cs.unm.edu/~mccune/prover9/) can search
for finite counterexamples alongside Vampire; it sometimes finds models of
sizes that Vampire's model builder does not reach in time.
"""

from __future__ import annotations

import os
import re
import shutil
import subprocess
import tempfile
import threading
import time
from collections import Counter
from collections.abc import Iterable, Sequence
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from itertools import count
from pathlib import Path

from conceptual_exploration.core.context import PartialObject
from conceptual_exploration.core.implication import Implication
from conceptual_exploration.core.theory import ImplicationTheory
from conceptual_exploration.experts.base import Undecided
from explorations.equational_theories.free_semigroup import truncated_countermodels
from explorations.equational_theories.magma import Equation, Magma, MagmaExpert, Op, Term, Var


def tptp_term(term: Term) -> str:
    if isinstance(term, Var):
        return "V" + term.name
    if isinstance(term, Op):
        return f"m({tptp_term(term.left)},{tptp_term(term.right)})"
    raise TypeError(f"Unsupported term {term!r}")


def tptp_law(equation: Equation) -> str:
    """The universal closure of an equation as a TPTP formula."""
    body = f"{tptp_term(equation.lhs)} = {tptp_term(equation.rhs)}"
    if not equation.variables:
        return body
    return f"![{','.join('V' + v for v in equation.variables)}]: {body}"


def tptp_problem(premise: Iterable[Equation], conclusion: Iterable[Equation]) -> str:
    """The implication as a TPTP problem: the premise laws as axioms and the
    conjunction of the conclusion laws as the conjecture."""
    lines = [f"fof(premise{k}, axiom, {tptp_law(eq)})." for k, eq in enumerate(sorted(premise))]
    goal = " & ".join(f"({tptp_law(eq)})" for eq in sorted(conclusion))
    lines.append(f"fof(conclusion, conjecture, {goal}).")
    return "\n".join(lines) + "\n"


def ladr_term(term: Term) -> str:
    if isinstance(term, Var):
        return "x" + term.name  # LADR variables start with u to z
    if isinstance(term, Op):
        return f"({ladr_term(term.left)} * {ladr_term(term.right)})"
    raise TypeError(f"Unsupported term {term!r}")


def ladr_problem(premise: Iterable[Equation], law: Equation) -> str:
    """The implication of `law` from the premise laws as Mace4 input."""
    lines = ["formulas(assumptions)."]
    lines += [f"{ladr_term(eq.lhs)} = {ladr_term(eq.rhs)}." for eq in sorted(premise)]
    lines += ["end_of_list.", "formulas(goals).", f"{ladr_term(law.lhs)} = {ladr_term(law.rhs)}.", "end_of_list."]
    return "\n".join(lines) + "\n"


_MACE4_TABLE = re.compile(r"interpretation\(\s*(\d+).*?function\(\*\(_,_\),\s*\[([\d,\s]*)\]", re.S)


def parse_mace4_model(output: str) -> tuple[tuple[int, ...], ...] | None:
    """The Cayley table of the first model in Mace4's output, or None."""
    match = _MACE4_TABLE.search(output)
    if match is None:
        return None
    size = int(match.group(1))
    values = [int(v) for v in match.group(2).split(",")]
    return tuple(tuple(values[i * size:(i + 1) * size]) for i in range(size))


_CELL = re.compile(r"m\('?fmb_\$i_(\d+)'?,'?fmb_\$i_(\d+)'?\) = '?fmb_\$i_(\d+)'?")


def parse_model(output: str) -> tuple[tuple[int, ...], ...] | None:
    """The Cayley table of a finite model in Vampire's output, or None if
    there is none or it is incomplete."""
    cells = _CELL.findall(output)
    if not cells:
        return None
    size = max(int(v) for cell in cells for v in cell)
    table: list[list[int | None]] = [[None] * size for _ in range(size)]
    for a, b, c in cells:
        table[int(a) - 1][int(b) - 1] = int(c) - 1
    if any(v is None for row in table for v in row):
        return None
    return tuple(tuple(row) for row in table)  # type: ignore[arg-type]


# The verdicts that decide whether a law follows.
DECISIVE = ("Theorem", "CounterSatisfiable")


@dataclass(frozen=True, slots=True)
class FreeMagma:
    """The free magma over a set of laws: terms in countably many variables,
    two of them equal when the laws derive their equation.

    It satisfies a law exactly when the laws derive it, so it refutes every
    implication from them that is false; for one-variable laws, the
    submagma generated by one variable already does. It is infinite unless
    the laws make it finite, so it has no table, and its row is what Vampire
    decides about each law.
    """

    premise: frozenset[Equation]

    @property
    def name(self) -> str:
        laws = ", ".join(eq.name or str(eq) for eq in sorted(self.premise))
        return f"Free({laws})"

    def __str__(self) -> str:
        return f"Free magma over {{{', '.join(f'Eq{eq.id}' if eq.id else str(eq) for eq in sorted(self.premise))}}}"


class VampireExpert(MagmaExpert):
    """Validates implications between magma laws with Vampire.

    1. The pool of magmas is checked first, as by MagmaExpert, and so are the
       answers remembered (see below).
    2. Vampire runs its portfolio of strategies on the implication, on all
       `workers` cores at once (`first_time_limit` seconds, by default
       `prove_time_limit`); a proof confirms it.
    3. Its finite model builder briefly searches for a counterexample of any
       size (`quick_model_time_limit` seconds). A model is checked against the
       laws and joins the pool.
    4. If the conclusion has a single law and step 2 ended with
       CounterSatisfiable, the free magma over the premise violates that law
       and refutes the implication, with no further call: the rest of its
       row is decided by the context already.
    5. Otherwise Vampire is asked about every law that the premise does not
       imply by the background implications and those proved so far,
       separately and in parallel, for `prove_time_limit` seconds each if the
       law is in the conclusion and `row_time_limit` seconds otherwise (not
       at all if that is 0, which leaves the law unknown): a proof puts
       the law on the positive side of the free magma over the premise, a
       counter-satisfiable verdict on the negative side, and a timeout leaves
       it unknown. If `eprover_time_limit` is positive, the E prover is asked
       about each law of the conclusion first, for that many seconds (2 is
       enough: when E decides a law, it nearly always does so within a
       fraction of a second), and Vampire only about the laws E leaves. If
       `prover9_time_limit` is positive, Prover9 then tries to prove each law
       of the conclusion that E left, for that many seconds; it finds some
       proofs at once that Vampire needs far longer for. Only its proofs
       count, since its search failing does not show a law false. The row is then completed with the
       known implications: what the laws proved imply is proved too, and a
       law that would imply a law on the negative side is on the negative
       side. If a law of the conclusion is on the negative side, the free
       magma refutes the implication; if every law of the conclusion is
       proved, so is the implication. If step 2 ended with
       CounterSatisfiable and a single law of the conclusion is left, that
       law fails in the free magma, which refutes the implication, after
       another brief search for a finite model violating it.
    6. Otherwise, for semigroups, if `truncation_words` is positive, the
       truncated free semigroups of the premise's variety are tried first
       (see free_semigroup.py), with at most that many words: a law of the
       conclusion with up to four variables that fails in one of them at the
       generators gives a checked countermodel, which can be far larger than
       any model search reaches. Then finite models are searched for, of the
       premise and violating a law of the conclusion not proved, one law at
       a time, on all cores:
       by Vampire's model builder (`model_time_limit` seconds per law) and,
       if `mace4_time_limit` is positive, by Mace4, which sweeps the sizes in
       parallel: each of its searches is for one law at one size, and a core
       that finishes one takes the smallest size not yet started (for
       `mace4_time_limit` seconds in all). Each model found is checked and
       joins the pool, and the searches for the laws it violates stop; the
       others go on until every law is violated or the time is up. The
       smallest model refutes the implication, and the pool the next questions about
       the same premise. With `model_premise` "simplified", the searches use a
       subset of the premise whose closure under the background implications
       and those proved is the whole premise, keeping the laws every object
       satisfies, which the background assumes rather than derives; with
       "both", both premises are searched.
    7. Failing that, the answer is Undecided: the laws of the conclusion that
       were proved are accepted. If Vampire has shown the implication false
       as a whole, the rest is rejected; if it has decided nothing against
       it, the rest is accepted as unconfirmed. The partial row of the free
       magma is not added to the context: its positive side holds in every
       object satisfying the premise, and each law on its negative side is
       denied by an object of the context satisfying the premise, so it could
       refute nothing that the context does not.

    So the expert never accepts an implication it knows to be false. The verdicts
    behind a free magma's negative side rest on Vampire's saturation, which,
    unlike a finite model, cannot be checked here. `last_status` names the
    kind of the latest answer, and `answers` counts them.

    Proofs, rejections and unconfirmed answers are remembered, so that a resumed
    exploration asking the same questions again does not run Vampire again;
    refutations are remembered by the pool and the context. So is each law
    whose model search in step 6 ran out of time, with its premise, so that
    the next question about them skips that search.
    """

    def __init__(
        self,
        attributes: Sequence[Equation] | None = None,
        prove_time_limit: int = 10,
        model_time_limit: int = 10,
        quick_model_time_limit: int = 1,
        vampire: str = "vampire",
        initial_magmas: Sequence[Magma] | None = None,
        workers: int | None = None,
        background: Iterable[Implication[Equation]] = (),
        row_time_limit: int | None = None,
        mace4_time_limit: int = 0,
        mace4: str = "mace4",
        eprover_time_limit: int = 0,
        eprover: str = "eprover",
        prover9_time_limit: int = 0,
        prover9: str = "prover9",
        first_time_limit: int | None = None,
        model_premise: str = "full",
        truncation_words: int = 0,
    ) -> None:
        super().__init__(attributes=attributes, initial_magmas=initial_magmas)
        executable = shutil.which(vampire)
        if executable is None:
            raise FileNotFoundError(f"Vampire executable {vampire!r} not found")
        self.vampire = executable
        self.prove_time_limit = prove_time_limit
        self.first_time_limit = prove_time_limit if first_time_limit is None else first_time_limit
        self.model_time_limit = model_time_limit
        self.quick_model_time_limit = quick_model_time_limit
        self.row_time_limit = prove_time_limit if row_time_limit is None else row_time_limit
        self.mace4_time_limit = mace4_time_limit
        self.mace4 = None
        if mace4_time_limit > 0:
            self.mace4 = shutil.which(mace4)
            if self.mace4 is None:
                raise FileNotFoundError(f"Mace4 executable {mace4!r} not found")
        self.prover9_time_limit = prover9_time_limit
        self.prover9 = None
        if prover9_time_limit > 0:
            self.prover9 = shutil.which(prover9)
            if self.prover9 is None:
                raise FileNotFoundError(f"Prover9 executable {prover9!r} not found")
        self.eprover_time_limit = eprover_time_limit
        self.eprover = None
        if eprover_time_limit > 0:
            self.eprover = shutil.which(eprover)
            if self.eprover is None:
                raise FileNotFoundError(f"E prover executable {eprover!r} not found")
        if model_premise not in ("full", "simplified", "both"):
            raise ValueError(f"model_premise must be full, simplified or both, not {model_premise!r}")
        self.model_premise = model_premise
        # For semigroups only: laws are read as words.
        self.truncation_words = truncation_words
        self.workers = workers or os.cpu_count() or 1
        self.last_status: str | None = None
        self.answers: Counter[str] = Counter()
        self._proved: list[Implication[Equation]] = []
        # Background and proved implications, by which the free magma over a
        # premise satisfies a law without asking Vampire.
        self._known = ImplicationTheory[Equation](background)
        self._undecided: dict[Implication[Equation], Undecided] = {}
        # Premises and laws whose model search in step 6 ran out of time, and
        # those that no truncated free semigroup refuted.
        self._searched: set[tuple[frozenset[Equation], Equation]] = set()
        self._truncated: set[tuple[frozenset[Equation], Equation]] = set()

    def validate(
        self,
        implication: Implication[Equation],
        attributes: Iterable[Equation] | None = None,
    ) -> PartialObject | Undecided | None:
        result = self._validate(implication, attributes)
        self.answers[self.last_status] += 1
        return result

    def _validate(
        self,
        implication: Implication[Equation],
        attributes: Iterable[Equation] | None,
    ) -> PartialObject | Undecided | None:
        eval_attrs = attributes or self.attributes

        premise = self._mask(implication.premise)
        conclusion = self._mask(implication.conclusion)
        for k, magma in enumerate(self.cached_magmas):
            if self._holding_mask(k, premise) & premise == premise:
                if conclusion & ~self._holding_mask(k, conclusion):
                    self.last_status = "pool"
                    return self._build_counterexample(magma, eval_attrs, implication)

        # A proof of P -> C also proves P' -> C' for P' including P and C'
        # included in C.
        if any(
            proved.premise <= implication.premise and implication.conclusion <= proved.conclusion
            for proved in self._proved
        ):
            self.last_status = "proved"
            return None
        if implication in self._undecided:
            answer = self._undecided[implication]
            self.last_status = "unconfirmed" if answer.unconfirmed else "rejected"
            return answer

        problem = tptp_problem(implication.premise, implication.conclusion)
        # Alone at this point, so on every core.
        status, output = self._run(problem, ["--mode", "casc", "--cores", str(self.workers)], self.first_time_limit)
        if status == "Theorem":
            return self._prove(implication)
        magma = self._model(implication, output)
        if magma is None:
            magma = self._search_model(implication, problem, self.quick_model_time_limit)
        if magma is not None:
            return self._refute(magma, eval_attrs, implication)
        premise = frozenset(implication.premise)
        attributes = eval_attrs or implication.conclusion
        if status == "CounterSatisfiable" and len(implication.conclusion) == 1:
            # The free magma over the premise violates the one law, which no
            # other law of its row decides more about.
            self.last_status = "free magma"
            known = self._known.closure(premise) | premise
            return self._completed(premise, known, set(implication.conclusion), attributes)

        free = self._free_magma(implication, attributes)
        if free.negative & implication.conclusion:
            self.last_status = "free magma"
            return free
        if implication.conclusion <= free.positive:
            if status == "CounterSatisfiable":
                raise ValueError(
                    f"Vampire refutes {implication} as a whole but proves each law of its conclusion"
                )
            return self._prove(implication)
        rest = implication.conclusion - free.positive
        if status == "CounterSatisfiable" and len(rest) == 1:
            # Only one law can fail: a brief search for a finite model
            # violating it, and the free magma otherwise.
            magma = self._search_model(implication, tptp_problem(premise, rest), self.quick_model_time_limit)
            if magma is not None:
                return self._refute(magma, eval_attrs, implication)
            self.last_status = "free magma"
            return self._completed(premise, set(free.positive), set(free.negative) | set(rest), attributes)
        models = self._truncated_models(implication, rest) if self.truncation_words > 0 else []
        if models:
            self.cached_magmas.extend(models[1:])
            counterexample = self._refute(models[0], eval_attrs, implication)
            self.last_status = "truncated free semigroup"
            return counterexample
        models = self._search_models(implication, rest)
        if models:
            # The pool answers the next questions about the same premise.
            self.cached_magmas.extend(models[1:])
            return self._refute(models[0], eval_attrs, implication)

        # Known to be false if Vampire says so, but on which law is not known;
        # otherwise nothing speaks against the rest.
        unconfirmed = status != "CounterSatisfiable"
        self.last_status = "unconfirmed" if unconfirmed else "rejected"
        answer = Undecided(frozenset(implication.conclusion & free.positive), None, unconfirmed)
        self._undecided[implication] = answer
        return answer

    def _prove(self, implication: Implication[Equation]) -> None:
        self.last_status = "proved"
        self._proved.append(implication)
        self._known.add(implication)
        return None

    def _refute(
        self,
        magma: Magma,
        attributes: Iterable[Equation] | None,
        implication: Implication[Equation],
    ) -> PartialObject:
        self.last_status = "model"
        self.cached_magmas.append(magma)
        return self._build_counterexample(magma, attributes, implication)

    def _search_model(
        self,
        implication: Implication[Equation],
        problem: str,
        time_limit: int,
    ) -> Magma | None:
        _, output = self._run(problem, ["--saturation_algorithm", "fmb"], time_limit)
        return self._model(implication, output)

    def _search_models(
        self,
        implication: Implication[Equation],
        laws: Iterable[Equation],
    ) -> list[Magma]:
        """Step 6: finite models of the premise, each violating a law, searched
        for one law at a time, which is much faster than a search for a model
        violating their conjunction, by Vampire and, if enabled, by Mace4 at
        one size at a time. The searches for a law stop at the first model
        violating it; all models found are returned, the smallest first."""
        premise = frozenset(implication.premise)
        laws = sorted(law for law in laws if (premise, law) not in self._searched)
        if not laws:
            # Otherwise the size sweep below, having no searches, never stops.
            return []
        violated = {law: threading.Event() for law in laws}
        premises = self._model_premises(premise)
        deadline = time.monotonic() + self.mace4_time_limit

        def searches():
            for searched in premises:
                for law in laws:
                    problem = tptp_problem(searched, [law])
                    yield law, lambda problem=problem, law=law: self._model(
                        implication,
                        self._run(problem, ["--saturation_algorithm", "fmb"], self.model_time_limit, violated[law])[1],
                    )
            if self.mace4 is None:
                return
            for size in count(2):
                for searched in premises:
                    for law in laws:
                        left = int(deadline - time.monotonic())
                        if left < 1 or all(event.is_set() for event in violated.values()):
                            return
                        if not violated[law].is_set():
                            yield law, lambda searched=searched, law=law, size=size, left=left: (
                                self._search_mace4_model(implication, searched, law, size, left, violated[law])
                            )

        queue = searches()
        lock = threading.Lock()
        found: list[Magma] = []

        def work() -> None:
            while True:
                with lock:
                    law, search = next(queue, (None, None))
                if search is None:
                    return
                if violated[law].is_set():
                    continue
                magma = search()
                if magma is not None:
                    with lock:
                        found.append(magma)
                        for other in laws:
                            if not magma.holds(other):
                                violated[other].set()

        threads = [threading.Thread(target=work) for _ in range(self.workers)]
        for thread in threads:
            thread.start()
        for thread in threads:
            thread.join()
        self._searched.update((premise, law) for law in laws if not violated[law].is_set())
        # Searches at several sizes run at once, so a larger model may come first.
        return sorted(found, key=lambda magma: magma.size)

    def _truncated_models(
        self,
        implication: Implication[Equation],
        laws: Iterable[Equation],
    ) -> list[Magma]:
        """Step 6, first for semigroups: countermodels from the truncated free
        semigroups of the variety of the (simplified) premise, each checked
        against the whole premise, the smallest first."""
        premise = frozenset(implication.premise)
        laws = sorted(law for law in laws if (premise, law) not in self._truncated)
        found = truncated_countermodels(sorted(self._model_premises(premise)[-1]), laws, self.truncation_words)
        models = [
            self._checked_model(implication, magma.table, "Truncated-Free-Semigroup")
            for magma in found
            if all(magma.holds(eq) for eq in premise)
        ]
        self._truncated.update(
            (premise, law) for law in laws if all(magma.holds(law) for magma in models)
        )
        return sorted(models, key=lambda magma: magma.size)

    def _model_premises(self, premise: frozenset[Equation]) -> list[frozenset[Equation]]:
        """The premises the model searches use, by `model_premise`."""
        if self.model_premise == "full":
            return [premise]
        # The laws every object satisfies are assumed, not derived, so a
        # model of the rest need not satisfy them: they are kept.
        assumed = premise & self._known.closure(set())
        simplified = frozenset(self._known.simplify(Implication(premise - assumed, frozenset())).premise) | assumed
        if self.model_premise == "simplified" or simplified == premise:
            return [simplified]
        return [premise, simplified]

    def _search_mace4_model(
        self,
        implication: Implication[Equation],
        premise: Iterable[Equation],
        law: Equation,
        size: int,
        time_limit: int,
        cancelled: threading.Event | None = None,
    ) -> Magma | None:
        """A model of `premise` of the given size violating `law`, by Mace4,
        checked against the whole implication."""
        output = self._execute(
            [self.mace4, "-n", str(size), "-N", str(size), "-t", str(time_limit)],
            ladr_problem(premise, law),
            time_limit + 30,
            cancelled,
        )
        table = parse_mace4_model(output)
        if table is None:
            return None
        return self._checked_model(implication, table, "Mace4")

    def _free_magma(
        self,
        implication: Implication[Equation],
        attributes: Iterable[Equation],
    ) -> PartialObject[FreeMagma, Equation]:
        """The row of the free magma over the premise, law by law; the laws
        the premise implies by the known implications need no asking, and
        the laws outside the conclusion get `row_time_limit` seconds."""
        premise = frozenset(implication.premise)
        implied = self._known.closure(premise) | premise
        unknown = set(attributes) - implied
        conclusion = sorted(unknown & implication.conclusion)
        verdicts: dict[Equation, str] = {}
        if self.eprover is not None:
            # E first, briefly: when it decides a law, it nearly always does
            # so within a fraction of a second.
            with ThreadPoolExecutor(self.workers) as pool:
                problems = [tptp_problem(premise, [law]) for law in conclusion]
                verdicts.update(zip(conclusion, pool.map(self._run_eprover, problems)))
        if self.prover9 is not None:
            left = [law for law in conclusion if verdicts.get(law) not in DECISIVE]
            with ThreadPoolExecutor(self.workers) as pool:
                proofs = pool.map(lambda law: self._run_prover9(premise, law), left)
                verdicts.update((law, "Theorem") for law, proved in zip(left, proofs) if proved)
        # Vampire on the laws of the conclusion that E left, which start first,
        # and on the others.
        laws = [law for law in conclusion if verdicts.get(law) not in DECISIVE]
        if self.row_time_limit > 0:
            laws += sorted(unknown - implication.conclusion)

        def decide(law: Equation) -> str:
            limit = self.prove_time_limit if law in implication.conclusion else self.row_time_limit
            return self._run(tptp_problem(premise, [law]), ["--mode", "casc"], limit)[0]

        with ThreadPoolExecutor(self.workers) as pool:
            verdicts.update(zip(laws, pool.map(decide, laws)))
        proved = {law for law, v in verdicts.items() if v == "Theorem"}
        negative = {law for law, v in verdicts.items() if v == "CounterSatisfiable"}
        return self._completed(premise, implied | proved, negative, attributes)

    def _completed(
        self,
        premise: frozenset[Equation],
        positive: set[Equation],
        negative: set[Equation],
        attributes: Iterable[Equation],
    ) -> PartialObject[FreeMagma, Equation]:
        """The free magma's row completed with the known implications: what
        its positive side implies is positive, and a law that would imply a
        law on its negative side is negative."""
        attributes = set(attributes) | premise
        positive = (self._known.closure(positive | premise) | positive | premise) & attributes
        if positive & negative:
            raise ValueError(f"The known implications contradict the free magma over {sorted(premise)}")
        changed = True
        while changed:
            changed = False
            for law in attributes - positive - negative:
                if self._known.closure(positive | {law}) & negative:
                    negative.add(law)
                    changed = True
        return PartialObject(FreeMagma(premise), positive, negative)

    def _run_prover9(self, premise: Iterable[Equation], law: Equation) -> bool:
        """Whether Prover9 proves the law from the premise within
        `prover9_time_limit` seconds."""
        problem = f"assign(max_seconds, {self.prover9_time_limit}).\n" + ladr_problem(premise, law)
        output = self._execute([self.prover9], problem, self.prover9_time_limit + 30, None)
        return "THEOREM PROVED" in output

    def _run_eprover(self, problem: str) -> str:
        """The SZS status of the E prover on the problem, within
        `eprover_time_limit` seconds."""
        with tempfile.NamedTemporaryFile("w", suffix=".p", delete=False) as file:
            file.write(problem)
            path = Path(file.name)
        try:
            run = subprocess.run(
                [self.eprover, "--auto", f"--cpu-limit={self.eprover_time_limit}", "-s", str(path)],
                capture_output=True,
                text=True,
                timeout=self.eprover_time_limit + 30,
            )
        except subprocess.TimeoutExpired:
            return "Unknown"
        finally:
            path.unlink(missing_ok=True)
        status = re.search(r"SZS status (\w+)", run.stdout)
        return status.group(1) if status else "Unknown"

    def _run(
        self,
        problem: str,
        options: list[str],
        time_limit: int,
        cancelled: threading.Event | None = None,
    ) -> tuple[str, str]:
        with tempfile.NamedTemporaryFile("w", suffix=".p", delete=False) as file:
            file.write(problem)
            path = Path(file.name)
        try:
            output = self._execute(
                [self.vampire, *options, "--time_limit", str(time_limit), str(path)], None, time_limit + 30, cancelled
            )
        finally:
            path.unlink(missing_ok=True)
        status = re.search(r"SZS status (\w+)", output)
        return (status.group(1) if status else "Unknown"), output

    @staticmethod
    def _execute(
        command: list[str],
        given: str | None,
        timeout: float,
        cancelled: threading.Event | None,
    ) -> str:
        """The output of `command`, given `given` as input; empty if it is
        killed, when `cancelled` is set or after `timeout` seconds."""
        process = subprocess.Popen(
            command,
            stdin=subprocess.DEVNULL if given is None else subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            text=True,
        )
        give_up = time.monotonic() + timeout
        while True:
            try:
                return process.communicate(given, timeout=0.2)[0]
            except subprocess.TimeoutExpired:
                # Input is sent on the first call only.
                given = None
                if (cancelled is not None and cancelled.is_set()) or time.monotonic() > give_up:
                    process.kill()
                    process.communicate()
                    return ""

    @staticmethod
    def _model(implication: Implication[Equation], output: str) -> Magma | None:
        table = parse_model(output)
        if table is None:
            return None
        return VampireExpert._checked_model(implication, table, "Vampire")

    @staticmethod
    def _checked_model(
        implication: Implication[Equation],
        table: tuple[tuple[int, ...], ...],
        finder: str,
    ) -> Magma:
        magma = Magma(len(table), table, name=f"{finder}-Counterexample-Size{len(table)}")
        holds = all(magma.holds(eq) for eq in implication.premise)
        fails = any(not magma.holds(eq) for eq in implication.conclusion)
        if not (holds and fails):
            raise ValueError(f"{finder}'s model does not refute {implication}:\n{magma}")
        return magma
