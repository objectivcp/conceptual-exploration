"""Tests for the lexical typology exploration, with stand-ins for Claude."""

import itertools
import random

import pytest

from conceptual_exploration import Implication, PartialObject, Undecided, simplified_rules
from conceptual_exploration.core.theory import ImplicationTheory
from explorations.lexical_typology.explore import FIELD_DIR, explore, table
from explorations.lexical_typology.lexical import ContextExpert, Field, Judgments, LexicalExpert

CONTEXTS = ("a ___ knife", "a ___ needle", "a ___ thorn", "a ___ nose")
GOLD = {
    "sharp": {"a ___ knife", "a ___ needle", "a ___ thorn", "a ___ nose"},
    "keen": {"a ___ knife"},
    "pointed": {"a ___ needle", "a ___ nose"},
    "prickly": {"a ___ thorn"},
    "spiky": {"a ___ thorn", "a ___ needle"},
}
# Contexts the field does not give, for object exploration to find.
HIDDEN = {"a ___ spear": {"sharp", "keen", "pointed"}, "a ___ cactus": {"prickly", "spiky"}}
FIELD = Field("English", "adjective", "sharpness", CONTEXTS, ("sharp",))


def fits(word, context):
    return context in GOLD[word] or word in HIDDEN.get(context, ())


class Judge:
    """Answers from GOLD, or "unsure" for the pairs in `unsure`."""

    def __init__(self, unsure=()):
        self.unsure = set(unsure)
        self.calls = 0

    def ask(self, system, prompt, schema):
        self.calls += 1
        word = prompt.split("\n", 1)[0].removeprefix("Word: ").split(" (")[0]
        answer = {}
        for line in prompt.splitlines():
            key, _, context = line.partition(": ")
            if key in schema["properties"]:
                verdict = (
                    "unsure" if (word, context) in self.unsure
                    else "yes" if fits(word, context) else "no"
                )
                answer[key] = {"sentence": f"{word} / {context}", "verdict": verdict}
        return answer


class Proposer:
    """Proposes every GOLD word fitting the premise and missing a conclusion
    context, and, as a model may, a word already known."""

    def __init__(self):
        self.calls = 0

    def ask(self, system, prompt, schema):
        self.calls += 1
        premise_text, conclusion_text = prompt.split("every one of these contexts:\n")[1].split(
            "and that do not fit at least one of these:\n")
        conclusion_text = conclusion_text.split("\n\n")[0]
        premise = {line[2:] for line in premise_text.splitlines() if line.startswith("- ")}
        conclusion = {line[2:] for line in conclusion_text.splitlines() if line.startswith("- ")}
        words = [w for w, cs in GOLD.items() if premise <= cs and conclusion - cs]
        return {"items": ["sharp"] + words}


class ContextProposer:
    """Proposes every context, the field's or hidden, that the premise words
    fit and a conclusion word does not."""

    def ask(self, system, prompt, schema):
        premise_text, conclusion_text = prompt.split("every one of these words fits:\n")[1].split(
            "and that at least one of these words does not fit:\n")
        conclusion_text = conclusion_text.split("\n\n")[0]
        premise = {line[2:] for line in premise_text.splitlines() if line.startswith("- ")}
        conclusion = {line[2:] for line in conclusion_text.splitlines() if line.startswith("- ")}
        contexts = [
            c for c in (*CONTEXTS, *HIDDEN)
            if all(fits(w, c) for w in premise) and not all(fits(w, c) for w in conclusion)
        ]
        return {"items": contexts}


def gold_closure(attributes):
    intents = [cs for cs in GOLD.values() if attributes <= cs]
    return set(CONTEXTS).intersection(*intents) if intents else set(CONTEXTS)


def run(tmp_path, judge, proposer, votes=1):
    judgments = Judgments(FIELD, judge, tmp_path / "judgments.json", votes=votes)
    judgments.judge_words(FIELD.words)
    expert = LexicalExpert(judgments, proposer)
    return judgments, expert, explore(judgments, expert, None, 0, report=0)[0]


def test_exploration_finds_the_implications_of_the_gold_table(tmp_path):
    judgments, _, result = run(tmp_path, Judge(), Proposer())
    theory = result.base.implications
    for n in range(len(CONTEXTS) + 1):
        for attributes in itertools.combinations(CONTEXTS, n):
            assert set(theory.closure(set(attributes))) == gold_closure(set(attributes))
    assert all(
        judgments.row(w).positive == GOLD[w]
        and judgments.row(w).negative == set(CONTEXTS) - GOLD[w]
        for w in judgments.words()
    )
    assert "\n".join(table(judgments)).count("?") == 0


def test_a_second_run_asks_claude_nothing(tmp_path):
    run(tmp_path, Judge(), Proposer())
    judge, proposer = Judge(), Proposer()
    run(tmp_path, judge, proposer)
    assert judge.calls == proposer.calls == 0


def test_votes_that_disagree_leave_the_value_unknown(tmp_path):
    class Flipping(Judge):
        def ask(self, system, prompt, schema):
            answer = super().ask(system, prompt, schema)
            if self.calls % 2 == 0:
                for value in answer.values():
                    value["verdict"] = "unsure"
            return answer

    judgments = Judgments(FIELD, Flipping(), votes=2)
    judgments.judge_words(["keen"])
    row = judgments.row("keen")
    assert row.positive == row.negative == set()
    assert all(len(judgments.data["votes"]["keen"][c]) == 2 for c in CONTEXTS)


def test_an_unknown_conclusion_gives_an_undecided_answer():
    # "pointed" fits the nose but is unsure of the needle, so it can neither
    # refute nose -> needle nor leave it unrefuted.
    judgments = Judgments(FIELD, Judge(unsure={("pointed", "a ___ needle")}))
    judgments.judge_words(["pointed"])
    expert = LexicalExpert(judgments, Proposer())
    answer = expert.validate(Implication(frozenset({"a ___ nose"}), frozenset({"a ___ needle"})))
    assert isinstance(answer, Undecided) and not answer.rejected
    assert answer.object.object == "pointed"
    assert expert.given == {"pointed"}


class Proposing:
    """Proposes the given words, whatever the question."""

    def __init__(self, *words):
        self.words = list(words)
        self.calls = 0

    def ask(self, system, prompt, schema):
        self.calls += 1
        return {"items": self.words}


def test_a_word_judged_before_that_leaves_the_question_undecided_does_not_stop_the_search():
    # "sharp" fits the nose but is unsure of the knife; "pointed", proposed,
    # refutes nose -> knife.
    judgments = Judgments(FIELD, Judge(unsure={("sharp", "a ___ knife")}))
    judgments.judge_words(["sharp"])
    proposer = Proposing("pointed")
    expert = LexicalExpert(judgments, proposer)
    answer = expert.validate(Implication(frozenset({"a ___ nose"}), frozenset({"a ___ knife"})))
    assert proposer.calls == 1
    assert isinstance(answer, PartialObject) and answer.object == "pointed"
    assert expert.given == {"pointed"}


def test_a_word_judged_before_is_the_undecided_answer_if_the_search_finds_nothing():
    judgments = Judgments(FIELD, Judge(unsure={("sharp", "a ___ knife")}))
    judgments.judge_words(["sharp"])
    proposer = Proposing("prickly")
    expert = LexicalExpert(judgments, proposer)
    answer = expert.validate(Implication(frozenset({"a ___ nose"}), frozenset({"a ___ knife"})))
    assert proposer.calls == 1
    assert isinstance(answer, Undecided) and answer.object.object == "sharp"
    assert expert.given == {"sharp"} and expert.unsearched == 0


def test_shipped_fields_load():
    for path in FIELD_DIR.glob("*.toml"):
        field = Field.load(path)
        assert field.contexts and field.words


@pytest.mark.parametrize("text, message", [
    ('language = "English"\npart_of_speech = "noun"\ndescription = "x"\ncontexts = ["a knife"]', "without the slot"),
    ('language = "English"\npart_of_speech = "noun"\ndescription = "x"\ncontexts = ["a ___"]\ncolour = 1', "unknown keys"),
    ('language = "English"\ncontexts = ["a ___"]', "missing keys"),
])
def test_bad_fields_are_rejected(tmp_path, text, message):
    path = tmp_path / "field.toml"
    path.write_text(text, encoding="utf-8")
    with pytest.raises(ValueError, match=message):
        Field.load(path)


@pytest.mark.parametrize("limits", [{"max_objects": 2}, {"max_proposals": 1}])
def test_limits_stop_the_search_for_words(tmp_path, limits):
    judge, proposer = Judge(), Proposer()
    judgments = Judgments(FIELD, judge, tmp_path / "judgments.json")
    judgments.judge_words(FIELD.words)
    expert = LexicalExpert(judgments, proposer, **limits)
    result = explore(judgments, expert, None, 0, report=0)[0]
    assert len(judgments.words()) <= limits.get("max_objects", len(GOLD))
    assert len(judgments.data["proposals"]) <= limits.get("max_proposals", len(GOLD))
    assert expert.unsearched > 0
    # What was found holds of the words judged, whatever was not searched.
    for implication in result.base.implications:
        for word in judgments.words():
            assert not judgments.row(word).refutes(implication)


@pytest.mark.parametrize("seed", range(60))
def test_no_rule_contradicts_a_word_on_its_own_and_joint_conflicts_are_reported(tmp_path, seed):
    # Unknown cells let each rule leave a word unrefuted while the rules
    # together contradict it; that is allowed, but reported. Five of these
    # seeds give such a conflict.
    rng = random.Random(seed)
    unsure = {(w, c) for w in GOLD for c in CONTEXTS if rng.random() < 0.4}
    judgments, _, result = run(tmp_path, Judge(unsure), Proposer())
    base = result.base

    def contradicts(rules, row):
        theory = ImplicationTheory(rules, index=base.index)
        return bool(set(theory.closure(set(row.positive))) & row.negative)

    rows = {word: judgments.row(word) for word in judgments.words()}
    for rule in simplified_rules(base):
        for word, row in rows.items():
            assert not contradicts([Implication(rule.premise, rule.conclusion)], row), (rule, word)
    reported = {c.original for conflict in base.joint_conflicts() for c in conflict.contradicted}
    for word, row in rows.items():
        if contradicts(list(base.implications), row):
            assert word in reported, word


class Referee:
    """Decides every context it is asked about from GOLD, and records which."""

    def __init__(self):
        self.asked = []

    def ask(self, system, prompt, schema):
        word = prompt.split("\n", 1)[0].removeprefix("Word: ").split(" (")[0]
        answer = {}
        for line in prompt.splitlines():
            key, _, context = line.partition(": ")
            if key in schema["properties"]:
                self.asked.append((word, context))
                answer[key] = {"reason": "gold", "verdict": "yes" if context in GOLD[word] else "no"}
        return answer


def test_the_referee_decides_only_the_unknown_values_in_the_question():
    unsure = {("pointed", c) for c in CONTEXTS}
    referee = Referee()
    judgments = Judgments(FIELD, Judge(unsure), referee=referee)
    judgments.judge_words(["pointed"])
    expert = LexicalExpert(judgments, Proposer())
    implication = Implication(frozenset({"a ___ nose"}), frozenset({"a ___ needle"}))
    # Decided, "pointed" fits both, and no gold word fits the nose alone.
    assert expert.validate(implication) is None
    assert sorted(referee.asked) == [("pointed", "a ___ needle"), ("pointed", "a ___ nose")]
    assert judgments.value("pointed", "a ___ nose") is True
    assert judgments.decided("pointed", "a ___ nose")
    assert judgments.value("pointed", "a ___ knife") is None


def test_the_referee_makes_an_unknown_value_refute():
    # "pointed" fits the nose and the needle, so it refutes nose -> knife
    # once the referee decides the knife, which the votes leave unknown.
    referee = Referee()
    judgments = Judgments(FIELD, Judge({("pointed", "a ___ knife")}), referee=referee)
    judgments.judge_words(["pointed"])
    expert = LexicalExpert(judgments, Proposer())
    answer = expert.validate(Implication(frozenset({"a ___ nose"}), frozenset({"a ___ knife"})))
    assert isinstance(answer, PartialObject) and answer.object == "pointed"
    assert referee.asked == [("pointed", "a ___ knife")]


def test_judgments_made_under_other_instructions_are_refused(tmp_path):
    path = tmp_path / "judgments.json"
    Judgments(FIELD, Judge(), path).judge_words(["keen"])
    other = Field(FIELD.language, FIELD.part_of_speech, "bluntness", CONTEXTS)
    with pytest.raises(ValueError, match="other instructions"):
        Judgments(other, Judge(), path)


def test_object_exploration_adds_the_contexts_that_refute_implications_between_words(tmp_path):
    judgments = Judgments(FIELD, Judge(), tmp_path / "judgments.json")
    judgments.judge_words(FIELD.words)
    words = LexicalExpert(judgments, Proposer())
    contexts = ContextExpert(judgments, ContextProposer(), (), candidates=5, max_objects=10)
    word_result, context_result = explore(judgments, words, contexts, object_words=10, report=0)

    assert set(judgments.contexts) == set(CONTEXTS) | set(HIDDEN)
    # The words imply one another as they do over every context, hidden or not.
    columns = [{w for w in GOLD if fits(w, c)} for c in judgments.contexts]
    theory = context_result.base.implications
    for n in range(len(GOLD) + 1):
        for premise in map(set, itertools.combinations(GOLD, n)):
            extents = [col for col in columns if premise <= col]
            expected = set(GOLD).intersection(*extents) if extents else set(GOLD)
            assert set(theory.closure(premise)) == expected
    # Every word is judged in the contexts added, and the contexts explored with them.
    assert all(judgments.value(w, c) is not None for w in judgments.words() for c in HIDDEN)
    assert set(word_result.base.attributes) == set(judgments.contexts)


def test_the_context_limit_stops_object_exploration(tmp_path):
    judgments = Judgments(FIELD, Judge(), tmp_path / "judgments.json")
    judgments.judge_words(FIELD.words)
    contexts = ContextExpert(
        judgments, ContextProposer(), (), candidates=5, max_objects=len(CONTEXTS) + 1
    )
    explore(judgments, LexicalExpert(judgments, Proposer()), contexts, object_words=10, report=0)
    assert len(judgments.contexts) == len(CONTEXTS) + 1
    assert contexts.unsearched > 0
