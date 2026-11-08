"""Explore a semantic field of one language with Claude as the expert.

The argument is a field file (see `lexical.py`), or the name of one shipped
in `fields/`:

    python explorations/lexical_typology/explore.py sharp_en
    python explorations/lexical_typology/explore.py my_field.toml --votes 5

The judgments and the words proposed for each question are kept in
`judgments.json` in the results directory, so an interrupted or repeated run
asks again only what it has not asked yet.

With `--max-contexts`, attribute exploration alternates with object
exploration: the words explore the contexts, then the contexts explore the
first `--object-words` words, which may add contexts, and so on until a
round adds nothing:

    python explorations/lexical_typology/explore.py sharp_en --max-contexts 16
"""

from __future__ import annotations

import argparse
import sys
import time
from pathlib import Path

# Support running directly as a script: add repo root and src to path
REPO_ROOT = Path(__file__).resolve().parent.parent.parent
if str(REPO_ROOT / "src") not in sys.path:
    sys.path.insert(0, str(REPO_ROOT / "src"))
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from conceptual_exploration import explore_in_rounds, report_every, simplified_rules
from explorations.lexical_typology.lexical import (
    Claude, ContextExpert, Field, Judgments, LexicalExpert,
)

HERE = Path(__file__).resolve().parent
FIELD_DIR = HERE / "fields"


def field_path(name: str) -> Path:
    path = Path(name)
    if path.exists():
        return path
    return FIELD_DIR / f"{name}.toml"


def settle(attributes, expert, report: int):
    """Explore `attributes` until every object the expert judged is in the
    context.

    The expert may judge objects that refute none of the questions it is
    asked but do refute an implication accepted before; such an object
    reaches the exploration only as an object of the next one, which starts
    over with every object judged, answering the questions asked before
    from the judgments and the cached proposals. Once the expert's limits
    are reached it judges no new objects, so the explorations end.
    """
    while True:
        names = expert.objects()
        expert.given = set(names)
        expert.unsearched = 0
        result = explore_in_rounds(
            attributes,
            expert,
            objects=[expert.row(n) for n in names],
            on_question=report_every(report),
            on_resume=lambda implication, name: print(
                f"\n{name} refutes the unconfirmed {implication}; resuming\n"),
        )
        missing = [n for n in expert.objects() if n not in names]
        if not missing:
            return result
        print(f"\nExploring again with the objects judged but not in the context: "
              f"{', '.join(missing)}\n")


def explore(judgments: Judgments, words: LexicalExpert, contexts: ContextExpert | None,
            object_words: int, report: int):
    """Explore the contexts with words and, if `contexts` is given, the
    first `object_words` words with contexts, in turn, until a round of the
    latter adds no context; return the last result of each."""
    round_ = 1
    while True:
        print(f"\n=== Round {round_}: contexts, refuted by words ===")
        judgments.judge_words(judgments.words())
        word_result = settle(judgments.contexts, words, report)
        if contexts is None:
            return word_result, None
        print(f"\n=== Round {round_}: words, refuted by contexts ===")
        contexts.words = judgments.words()[:object_words]
        known = len(judgments.contexts)
        context_result = settle(contexts.words, contexts, report)
        if len(judgments.contexts) == known:
            return word_result, context_result
        round_ += 1


def table(judgments: Judgments) -> list[str]:
    """The words against the contexts, + for fits, - for does not, ? for
    votes that disagree or say unsure; * marks the referee's decisions."""
    contexts = judgments.contexts
    added = len(judgments.field.contexts)
    width = max(map(len, judgments.words()), default=0)
    lines = [
        f"c{n:<3} {c}{'   (added)' if n > added else ''}"
        for n, c in enumerate(contexts, start=1)
    ]
    lines.append("")
    lines.append(" " * width + " " + " ".join(f"c{n:<3}" for n in range(1, len(contexts) + 1)))
    for word in judgments.words():
        marks = []
        for c in contexts:
            value = judgments.value(word, c)
            mark = "?" if value is None else "+" if value else "-"
            marks.append(f"{mark + ('*' if judgments.decided(word, c) else ''):<4}")
        lines.append(f"{word:<{width}} " + " ".join(marks))
    return lines


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("field", help="a field file, or the name of one in fields/")
    parser.add_argument("--results", type=Path, metavar="DIR",
                        help="where to keep the judgments and write the results "
                             "(default: results/<field>)")
    parser.add_argument("--judge-model", default="sonnet",
                        help="the model judging words in contexts (default: sonnet)")
    parser.add_argument("--propose-model", default="opus",
                        help="the model proposing words (default: opus)")
    parser.add_argument("--referee-model", default="opus",
                        help="the model deciding the values the votes leave unknown, "
                             "\"none\" to leave them unknown (default: opus)")
    parser.add_argument("--votes", type=int, default=3,
                        help="judgments per word and context; a value needs all to agree")
    parser.add_argument("--candidates", type=int, default=2,
                        help="words proposed per question (default: 2)")
    parser.add_argument("--max-words", type=int, default=60,
                        help="stop searching for words once this many are judged; "
                             "0 for no limit (default: 60)")
    parser.add_argument("--max-proposals", type=int, default=100,
                        help="stop searching for words once this many questions have "
                             "been put to the proposer; 0 for no limit (default: 100)")
    parser.add_argument("--max-contexts", type=int, default=0,
                        help="alternate with object exploration, adding contexts until "
                             "there are this many; 0 explores contexts only (default)")
    parser.add_argument("--object-words", type=int, default=8,
                        help="object exploration explores the first this many words "
                             "judged, the seed words first (default: 8)")
    parser.add_argument("--workers", type=int, default=8,
                        help="judging calls run at once")
    parser.add_argument("--report", type=int, default=1,
                        help="print every nth question; 0 prints none")
    args = parser.parse_args(argv)

    path = field_path(args.field)
    try:
        field = Field.load(path)
    except (OSError, ValueError) as error:
        parser.error(str(error))
    results = args.results or HERE / "results" / path.stem

    judge = Claude(args.judge_model)
    proposer = Claude(args.propose_model)
    referee = None if args.referee_model == "none" else Claude(args.referee_model)
    try:
        judgments = Judgments(
            field, judge, results / "judgments.json", args.votes, args.workers, referee
        )
    except ValueError as error:
        parser.error(str(error))
    expert = LexicalExpert(
        judgments, proposer, args.candidates,
        max_objects=args.max_words or None,
        max_proposals=args.max_proposals or None,
    )
    context_expert = None
    if args.max_contexts:
        context_expert = ContextExpert(
            judgments, proposer, (), candidates=args.candidates,
            max_objects=args.max_contexts,
            max_proposals=args.max_proposals or None,
        )

    print(f"Field:    {field.description} ({field.language} {field.part_of_speech}s)")
    print(f"Contexts: {len(field.contexts)}; seed words: {', '.join(field.words) or '-'}")
    print(f"Judge:    {args.judge_model}, {args.votes} votes; referee: {args.referee_model}; "
          f"proposer: {args.propose_model}, {args.candidates} words per question")
    print(f"Limits:   {args.max_words or 'no'} words, {args.max_proposals or 'no'} proposals"
          f" of each kind" + (f", {args.max_contexts} contexts, object exploration of "
                              f"{args.object_words} words" if args.max_contexts else ""))

    start = time.perf_counter()
    judgments.judge_words(field.words)
    result, context_result = explore(
        judgments, expert, context_expert, args.object_words, args.report
    )
    elapsed = time.perf_counter() - start

    rules = [str(rule) for rule in simplified_rules(result.base)]
    models = [judge, proposer] + ([referee] if referee else [])
    calls = sum(m.calls for m in models)
    cost = sum(m.cost for m in models)
    print(f"\nTime Elapsed:      {elapsed:.0f}s")
    print(f"Questions Asked:   {result.questions_asked}")
    print(f"Words Judged:      {len(judgments.words())}")
    added = judgments.contexts[len(field.contexts):]
    if context_expert is not None:
        print(f"Contexts:          {len(judgments.contexts)}, {len(added)} added")
    print(f"Claude Calls:      {calls} (estimated at list prices: ${cost:.2f})")
    if expert.unsearched:
        print(f"Not Searched:      {expert.unsearched} questions, accepted once a limit "
              f"was reached without searching for new words")
    if context_expert is not None and context_expert.unsearched:
        print(f"Not Searched:      {context_expert.unsearched} questions about words, "
              f"accepted once a limit was reached without searching for new contexts")
    print(f"\nRules ({len(rules)}, all unconfirmed):")
    for n, rule in enumerate(rules, start=1):
        print(f"  [{n}] {rule}")
    word_rules = []
    if context_result is not None:
        word_rules = [str(rule) for rule in simplified_rules(context_result.base)]
        print(f"\nRules about the words {', '.join(context_expert.words)} "
              f"({len(word_rules)}, all unconfirmed):")
        for n, rule in enumerate(word_rules, start=1):
            print(f"  [{n}] {rule}")
    lines = table(judgments)
    print()
    print("\n".join(lines))

    results.mkdir(parents=True, exist_ok=True)
    (results / "rules.txt").write_text("\n".join(rules) + "\n", encoding="utf-8")
    (results / "context.txt").write_text("\n".join(lines) + "\n", encoding="utf-8")
    if context_result is not None:
        (results / "word_rules.txt").write_text("\n".join(word_rules) + "\n", encoding="utf-8")
    print(f"\nResults written to {results}")


if __name__ == "__main__":
    main()
