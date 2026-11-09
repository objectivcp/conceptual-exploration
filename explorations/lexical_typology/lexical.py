"""Lexical typology by attribute exploration, with Claude as the expert.

The objects are words of one language in a semantic field, the attributes
contexts with a slot, such as "a ___ knife" or "___ апельсина", and a word
has a context when a native speaker would put it in the slot. Claude is run
through the `claude` command line in print mode, so no API key is needed:
one call proposes words that may refute a question, and others judge each
word in each context, several times, each time with a sentence as evidence.
A word has a context when it is natural there with a meaning of the field,
so that an antonym in a natural combination does not. It has the context
when every vote says yes, lacks it when every vote says no, and otherwise
it is unknown there, unless a referee, shown the votes, decides it. The
referee is asked only about the contexts of a question that a word might
refute.

`LexicalExpert` answers questions about contexts with words; `ContextExpert`
answers the dual questions about words, those of object exploration, with
new contexts, so that alternating the two lets both grow.

The expert can refute an implication but never confirm one, so every
implication it accepts is unconfirmed.
"""

from __future__ import annotations

import hashlib
import json
import subprocess
import tempfile
import threading
import tomllib
from collections.abc import Iterable
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, fields
from pathlib import Path
from typing import Protocol

from conceptual_exploration.core.context import PartialObject
from conceptual_exploration.core.implication import Implication
from conceptual_exploration.experts.base import Expert, Undecided

SLOT = "___"

GUIDELINES = (
    "Only propose words an ordinary adult native speaker uses in everyday "
    "language: no scientific or technical terms, no dialectal, archaic or rare "
    "words, no diminutives or other forms that only add an evaluative nuance to "
    "another word, and no compounds or multiword phrases."
)


@dataclass(frozen=True)
class Field:
    """A semantic field of one language: the contexts explored as attributes
    and the words judged before the exploration starts. `guidelines` say
    which words to propose, in place of `GUIDELINES`."""

    language: str
    part_of_speech: str
    description: str
    contexts: tuple[str, ...]
    words: tuple[str, ...] = ()
    guidelines: str = GUIDELINES

    @classmethod
    def load(cls, path: Path) -> "Field":
        with open(path, "rb") as f:
            data = tomllib.load(f)
        names = {f.name for f in fields(cls)}
        if unknown := data.keys() - names:
            raise ValueError(f"{path}: unknown keys {sorted(unknown)}")
        if missing := {"language", "part_of_speech", "description", "contexts"} - data.keys():
            raise ValueError(f"{path}: missing keys {sorted(missing)}")
        field = cls(**{
            key: tuple(value) if isinstance(value, list) else value
            for key, value in data.items()
        })
        if bad := [c for c in field.contexts if SLOT not in c]:
            raise ValueError(f"{path}: contexts without the slot {SLOT}: {bad}")
        if len(set(field.contexts)) != len(field.contexts):
            raise ValueError(f"{path}: repeated contexts")
        return field


class Model(Protocol):
    def ask(self, system: str, prompt: str, schema: dict) -> dict: ...


class Claude:
    """Structured answers from `claude -p`, run without tools, settings or
    MCP servers in an empty directory, so that nothing but the prompt
    reaches the model."""

    def __init__(self, model: str, retries: int = 2, timeout: float = 600):
        self.model = model
        self.retries = retries
        self.timeout = timeout
        # As `claude` reports it; a subscription does not bill it.
        self.cost = 0.0
        self.calls = 0
        self._lock = threading.Lock()
        self._directory = tempfile.mkdtemp(prefix="lexical-typology-")

    def ask(self, system: str, prompt: str, schema: dict) -> dict:
        command = [
            "claude", "-p",
            "--model", self.model,
            "--output-format", "json",
            "--tools", "",
            "--strict-mcp-config",
            "--setting-sources", "",
            "--no-session-persistence",
            "--system-prompt", system,
            "--json-schema", json.dumps(schema),
        ]
        error = ""
        for _ in range(self.retries + 1):
            try:
                result = subprocess.run(
                    command, input=prompt, capture_output=True, text=True,
                    cwd=self._directory, timeout=self.timeout,
                )
            except subprocess.TimeoutExpired:
                error = f"timed out after {self.timeout}s"
                continue
            try:
                output = json.loads(result.stdout)
            except json.JSONDecodeError:
                error = result.stderr or result.stdout[:500]
                continue
            if output.get("is_error") or "structured_output" not in output:
                error = str(output.get("result", output))[:500]
                continue
            with self._lock:
                self.cost += output.get("total_cost_usd", 0.0)
                self.calls += 1
            return output["structured_output"]
        raise RuntimeError(f"claude -p --model {self.model} failed: {error}")


def _numbered(contexts: Iterable[str]) -> str:
    return "\n".join(f"- {c}" for c in contexts)


def _system(field: Field) -> str:
    return (
        f"You are a native speaker of {field.language} and a careful lexicographer. "
        f"You give acceptability judgments for a study in lexical typology."
    )


def _judging(field: Field) -> str:
    return (
        f"Field: {field.description}\n\n"
        f"For each context below, decide whether a native speaker of {field.language} "
        f"would naturally use this word in the slot {SLOT}, inflected as needed, with "
        f"a meaning of the field.\n\n"
        f"First write the most natural sentence you can in {field.language} with the "
        f"word in that context, then give the verdict:\n"
        f"- yes: a natural combination that speakers actually use, in which the word "
        f"has a meaning of the field;\n"
        f"- no: odd or unidiomatic, possible only as wordplay or a deliberate stretch, "
        f"or natural only with a meaning outside the field, such as the opposite one;\n"
        f"- unsure: neither clearly."
    )


def _refereeing(field: Field) -> str:
    return (
        f"Field: {field.description}\n\n"
        f"Judges disagreed, or were unsure, whether a native speaker of {field.language} "
        f"would naturally use this word in the contexts below, in the slot {SLOT}, "
        f"inflected as needed, with a meaning of the field. Their sentences and "
        f"verdicts follow each context.\n\n"
        f"Weigh them against your own knowledge of {field.language} and give the final "
        f"verdict for each context, after a short reason: yes, no, or unsure only if "
        f"the combination is genuinely borderline."
    )


def _verdicts(keys, explanation: str) -> dict:
    verdict = {
        "type": "object",
        "properties": {
            explanation: {"type": "string"},
            "verdict": {"type": "string", "enum": ["yes", "no", "unsure"]},
        },
        "required": [explanation, "verdict"],
    }
    return {"type": "object", "properties": {key: verdict for key in keys}, "required": list(keys)}


class Judgments:
    """The votes on each word in each context, the referee's decisions and
    the words proposed for each question, kept in a JSON file so that
    nothing is asked twice and every verdict can be audited by its sentence
    or reason.

    A vote is {"sentence", "verdict", "model"} with the verdict "yes", "no"
    or "unsure"; a context gets `votes` of them per word. The contexts are
    the field's and those added since, which the file keeps. A decision is
    {"reason", "verdict", "model"}. The file records a fingerprint of the
    instructions the votes and decisions were given under, and one made
    under other instructions is refused rather than mixed with new votes.
    """

    def __init__(
            self,
            field: Field,
            judge: Model,
            path: Path | None = None,
            votes: int = 3,
            workers: int = 8,
            referee: Model | None = None,
    ):
        self.field = field
        self.judge = judge
        self.referee = referee
        self.path = path
        self.votes = votes
        self.workers = workers
        fingerprint = hashlib.sha256(
            "\n".join([_system(field), _judging(field), _refereeing(field)]).encode()
        ).hexdigest()[:16]
        self.data: dict = {"instructions": fingerprint, "votes": {}, "decisions": {}, "proposals": {}}
        if path is not None and path.exists():
            data = json.loads(path.read_text(encoding="utf-8"))
            if data.get("instructions") != fingerprint:
                raise ValueError(
                    f"{path} holds judgments made under other instructions; "
                    f"use another results directory"
                )
            self.data = data
        self._lock = threading.Lock()

    def words(self) -> list[str]:
        """The words judged, in the order they were first judged."""
        return list(self.data["votes"])

    @property
    def contexts(self) -> list[str]:
        """The field's contexts, then those added, in the order they were added."""
        return list(self.field.contexts) + self.data.get("contexts", [])

    def add_contexts(self, contexts: Iterable[str]) -> list[str]:
        """Add the contexts with a slot that are not known yet; return them."""
        known = set(self.contexts)
        new = [c for c in dict.fromkeys(contexts) if c.count(SLOT) == 1 and c not in known]
        self.data.setdefault("contexts", []).extend(new)
        self.save()
        return new

    def judge_words(self, words: Iterable[str]) -> None:
        """Collect the missing votes on `words` in every context."""
        calls = []
        for word in dict.fromkeys(words):
            votes = self.data["votes"].setdefault(word, {})
            for k in range(self.votes):
                contexts = [c for c in self.contexts if len(votes.get(c, ())) <= k]
                if contexts:
                    calls.append((word, contexts))
        with ThreadPoolExecutor(self.workers) as pool:
            for word, answers in pool.map(lambda call: (call[0], self._vote(*call)), calls):
                with self._lock:
                    votes = self.data["votes"][word]
                    for context, vote in answers.items():
                        votes.setdefault(context, []).append(vote)
        self.save()

    def _vote(self, word: str, contexts: list[str]) -> dict[str, dict]:
        f = self.field
        keys = {f"c{n}": c for n, c in enumerate(contexts, start=1)}
        prompt = (
            f"Word: {word} ({f.part_of_speech})\n" + _judging(f) + "\n\n"
            f"Contexts:\n" + "\n".join(f"{key}: {c}" for key, c in keys.items())
        )
        answer = self.judge.ask(_system(f), prompt, _verdicts(keys, "sentence"))
        model = getattr(self.judge, "model", None)
        return {
            context: {
                "sentence": answer[key]["sentence"],
                "verdict": answer[key]["verdict"],
                "model": model,
            }
            for key, context in keys.items()
        }

    def decide(self, cells: dict[str, Iterable[str]]) -> None:
        """Have the referee decide the contexts of each word in `cells`
        where its votes leave the value unknown and no decision is made."""
        if self.referee is None:
            return
        calls = []
        for word, contexts in cells.items():
            decided = self.data["decisions"].get(word, {})
            open_ = [
                c for c in self.contexts
                if c in set(contexts) and c not in decided and self._voted(word, c) is None
            ]
            if open_:
                calls.append((word, open_))
        with ThreadPoolExecutor(self.workers) as pool:
            for word, answers in pool.map(lambda call: (call[0], self._referee(*call)), calls):
                with self._lock:
                    self.data["decisions"].setdefault(word, {}).update(answers)
        if calls:
            self.save()

    def _referee(self, word: str, contexts: list[str]) -> dict[str, dict]:
        f = self.field
        keys = {f"c{n}": c for n, c in enumerate(contexts, start=1)}
        lines = []
        for key, context in keys.items():
            lines.append(f"{key}: {context}")
            for vote in self.data["votes"][word][context]:
                lines.append(f"  - {vote['sentence']} ({vote['verdict']})")
        prompt = (
            f"Word: {word} ({f.part_of_speech})\n" + _refereeing(f) + "\n\n"
            f"Contexts:\n" + "\n".join(lines)
        )
        answer = self.referee.ask(_system(f), prompt, _verdicts(keys, "reason"))
        model = getattr(self.referee, "model", None)
        return {
            context: {"reason": answer[key]["reason"], "verdict": answer[key]["verdict"], "model": model}
            for key, context in keys.items()
        }

    def _voted(self, word: str, context: str) -> bool | None:
        verdicts = {v["verdict"] for v in self.data["votes"].get(word, {}).get(context, ())}
        return {"yes": True, "no": False}.get(verdicts.pop()) if len(verdicts) == 1 else None

    def decided(self, word: str, context: str) -> bool:
        """Whether the value is the referee's rather than the votes'."""
        return self._voted(word, context) is None and self.value(word, context) is not None

    def value(self, word: str, context: str) -> bool | None:
        """True or False when the votes agree or, if they do not, as the
        referee decided; None otherwise."""
        voted = self._voted(word, context)
        if voted is not None:
            return voted
        decision = self.data["decisions"].get(word, {}).get(context)
        return None if decision is None else {"yes": True, "no": False}.get(decision["verdict"])

    def row(self, word: str) -> PartialObject[str, str]:
        values = {c: self.value(word, c) for c in self.contexts}
        return PartialObject(
            word,
            {c for c, v in values.items() if v is True},
            {c for c, v in values.items() if v is False},
        )

    def column(self, context: str, words: Iterable[str]) -> PartialObject[str, str]:
        """The context as an object of object exploration, over `words`."""
        values = {w: self.value(w, context) for w in words}
        return PartialObject(
            context,
            {w for w, v in values.items() if v is True},
            {w for w, v in values.items() if v is False},
        )

    def save(self) -> None:
        if self.path is None:
            return
        self.path.parent.mkdir(parents=True, exist_ok=True)
        temporary = self.path.with_suffix(".tmp")
        temporary.write_text(json.dumps(self.data, ensure_ascii=False, indent=1), encoding="utf-8")
        temporary.replace(self.path)


class _Searching(Expert[str, str]):
    """An expert that refutes with objects it judges, searching for new ones.

    Objects judged already but not yet given to the exploration are tried
    first; unless one of them refutes the question, the proposer is asked
    for up to `candidates` new ones, which are judged. An object that has
    the premise but is unknown, rather than wrong, in the conclusion is
    given as an undecided answer if no object refutes the question, an old
    one before a new one. Before an
    object is tried, the referee decides its unknown values in the
    question's attributes, unless one of the premise is known false.
    Proposals are cached by the question.

    Once there are `max_objects` objects, or `max_proposals` questions have
    been put to the proposer, nothing new is searched for: the remaining
    questions are answered from the objects judged, and those it leaves
    unrefuted are counted in `unsearched`.
    """

    cache: str

    def __init__(
            self,
            judgments: Judgments,
            proposer: Model,
            candidates: int = 2,
            max_objects: int | None = None,
            max_proposals: int | None = None,
    ):
        self.judgments = judgments
        self.proposer = proposer
        self.candidates = candidates
        self.max_objects = max_objects
        self.max_proposals = max_proposals
        # Objects in the exploration's context, which refute no question asked.
        self.given: set[str] = set()
        self.unsearched = 0

    def objects(self) -> list[str]:
        raise NotImplementedError

    def row(self, name: str) -> PartialObject[str, str]:
        raise NotImplementedError

    def _decide(self, names: list[str], attributes: frozenset[str]) -> None:
        raise NotImplementedError

    def _propose(self, implication: Implication[str]) -> list[str]:
        raise NotImplementedError

    def _add(self, names: list[str]) -> list[str]:
        """Judge the new objects; return those added."""
        raise NotImplementedError

    def validate(
            self,
            implication: Implication[str],
            attributes: frozenset[str] | None = None,
    ) -> PartialObject[str, str] | Undecided[str, str] | None:
        pending = [o for o in self.objects() if o not in self.given]
        answer = self._answer(implication, pending)
        if not isinstance(answer, PartialObject):
            new = self._search(implication)
            if new is None:
                if answer is None:
                    self.unsearched += 1
            else:
                found = self._answer(implication, self._add(new))
                if answer is None or isinstance(found, PartialObject):
                    answer = found
        if isinstance(answer, Undecided):
            self.given.add(answer.object.object)
        elif answer is not None:
            self.given.add(answer.object)
        return answer

    def is_conclusive(self) -> bool:
        return False

    def _answer(self, implication, names):
        self._decide(
            [n for n in names if not implication.premise & self.row(n).negative],
            implication.premise | implication.conclusion,
        )
        rows = [self.row(n) for n in names]
        for row in rows:
            if row.refutes(implication):
                return row
        for row in rows:
            if implication.premise <= row.positive and implication.conclusion - row.negative - row.positive:
                return Undecided(object=row)
        return None

    def _search(self, implication: Implication[str]) -> list[str] | None:
        """New objects to judge for `implication`, or None when a limit
        keeps them from being searched for."""
        known = self.objects()
        room = None if self.max_objects is None else max(self.max_objects - len(known), 0)
        key = json.dumps([sorted(implication.premise), sorted(implication.conclusion)], ensure_ascii=False)
        proposals = self.judgments.data.setdefault(self.cache, {})
        if key in proposals:
            # Searched before, if perhaps with objects left over for want of room.
            proposed = proposals[key]
        elif room == 0 or self.max_proposals is not None and len(proposals) >= self.max_proposals:
            return None
        else:
            proposed = proposals[key] = self._propose(implication)
            self.judgments.save()
        new = [o for o in proposed if o not in set(known)]
        return new if room is None else new[:room]

    def _ask(self, prompt: str) -> list[str]:
        f = self.judgments.field
        system = f"You are an expert in the lexicon of {f.language} and in lexical typology."
        schema = {
            "type": "object",
            "properties": {"items": {"type": "array", "items": {"type": "string"}}},
            "required": ["items"],
        }
        answer = self.proposer.ask(system, prompt, schema)
        return list(dict.fromkeys(i.strip() for i in answer["items"] if i.strip()))[:self.candidates]


class LexicalExpert(_Searching):
    """Refutes an implication over contexts with a word that fits every
    context of its premise and misses one of its conclusion; new words are
    judged in every context. `max_objects` limits the words."""

    cache = "proposals"

    def objects(self) -> list[str]:
        return self.judgments.words()

    def row(self, name: str) -> PartialObject[str, str]:
        return self.judgments.row(name)

    def _decide(self, names, attributes):
        self.judgments.decide({w: attributes for w in names})

    def _add(self, names):
        self.judgments.judge_words(names)
        return names

    def _propose(self, implication: Implication[str]) -> list[str]:
        f = self.judgments.field
        premise = (
            _numbered(sorted(implication.premise))
            if implication.premise
            else "(no condition: any word of the field)"
        )
        return self._ask(
            f"We are collecting {f.part_of_speech}s of {f.language} in the semantic "
            f"field: {f.description}.\n"
            f"A word fits a context when a native speaker would naturally use it in "
            f"the slot {SLOT}, inflected as needed, with a meaning of the field.\n"
            f"{f.guidelines}\n\n"
            f"Find up to {self.candidates} {f.part_of_speech}s of {f.language} that fit "
            f"every one of these contexts:\n{premise}\n"
            f"and that do not fit at least one of these:\n"
            f"{_numbered(sorted(implication.conclusion))}\n\n"
            f"Do not list these words, which are already known: "
            f"{', '.join(self.judgments.words()) or '(none)'}.\n"
            f"Give dictionary forms of real, current words as the items. Return an "
            f"empty list if there is no such word; do not stretch."
        )


class ContextExpert(_Searching):
    """Refutes an implication over `words`, a question of object
    exploration, with a context that every word of its premise fits and a
    word of its conclusion does not. New contexts are judged for `words`
    only; the other words are judged in them afterwards, before contexts
    are explored again. `max_objects` limits the contexts, the field's
    included."""

    cache = "context_proposals"

    def __init__(self, judgments: Judgments, proposer: Model, words: Iterable[str], **limits):
        super().__init__(judgments, proposer, **limits)
        self.words = list(words)

    def objects(self) -> list[str]:
        return self.judgments.contexts

    def row(self, name: str) -> PartialObject[str, str]:
        return self.judgments.column(name, self.words)

    def _decide(self, names, attributes):
        self.judgments.decide({w: names for w in attributes})

    def _add(self, names):
        new = self.judgments.add_contexts(names)
        self.judgments.judge_words(self.words)
        return new

    def _propose(self, implication: Implication[str]) -> list[str]:
        f = self.judgments.field
        premise = (
            _numbered(sorted(implication.premise))
            if implication.premise
            else "(no condition)"
        )
        return self._ask(
            f"We are collecting contexts for {f.part_of_speech}s of {f.language} in the "
            f"semantic field: {f.description}.\n"
            f"A context is a phrase or a sentence of {f.language} with the slot {SLOT} "
            f"for the word, like these, which are already known:\n"
            f"{_numbered(self.judgments.contexts)}\n"
            f"A word fits a context when a native speaker would naturally use it in "
            f"the slot, inflected as needed, with a meaning of the field.\n\n"
            f"Find up to {self.candidates} new contexts, of the same form as the known "
            f"ones, that every one of these words fits:\n{premise}\n"
            f"and that at least one of these words does not fit:\n"
            f"{_numbered(sorted(implication.conclusion))}\n\n"
            f"Prefer contexts for typical, everyday situations of the field, each narrow "
            f"enough to call for one meaning of the field. Give the contexts as the "
            f"items, each with the slot {SLOT} exactly once. Return an empty list if "
            f"there is no such context; do not stretch."
        )
