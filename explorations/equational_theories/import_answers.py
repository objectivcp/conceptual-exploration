"""Add the undecided answers of earlier explorations to an answer cache.

    python explorations/equational_theories/import_answers.py RESULTS_DIR... --cache FILE

Each RESULTS_DIR is an exploration with --expert vampire. Its exploration.log
gives the questions the expert left undecided, rejected as a whole or not,
with the laws it proved, and its settings.toml the expert's settings. They
are added to FILE as explore.py --answer-cache writes them (see
VampireExpert), so that a later run with the same settings is given the same
answers to the same questions without asking Vampire. The Vampire version and
the number of cores are taken to be this machine's. The logs do not record
the premises of the model searches, so the entries have none and match any.
The proofs of the proved laws are not copied: --seed-confirmed brings them.
"""

import argparse
import json
import re
import sys
import tomllib
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
sys.path[:0] = [str(REPO), str(REPO / "src")]
from explorations.equational_theories.vampire import VampireExpert  # noqa: E402

# settings.toml keys and the VampireExpert parameters they set.
OPTIONS = {
    "vampire-prove-time-limit": "prove_time_limit",
    "vampire-first-time-limit": "first_time_limit",
    "vampire-model-time-limit": "model_time_limit",
    "vampire-quick-model-time-limit": "quick_model_time_limit",
    "vampire-row-time-limit": "row_time_limit",
    "mace4-time-limit": "mace4_time_limit",
    "model-premise": "model_premise",
    "truncation-words": "truncation_words",
    "eprover-time-limit": "eprover_time_limit",
    "prover9-time-limit": "prover9_time_limit",
}
QUESTION = re.compile(r"^Question \d+: (.*) -> (.*)$")


def ids(text: str) -> list[int]:
    return sorted({int(n) for n in re.findall(r"Eq(\d+):", text)})


def undecided_answers(directory: Path) -> list[dict]:
    settings = tomllib.loads((directory / "settings.toml").read_text(encoding="utf-8"))
    if settings.get("expert") != "vampire":
        raise ValueError(f"{directory} was not explored with --expert vampire")
    expert = VampireExpert(**{name: settings[key] for key, name in OPTIONS.items() if key in settings},
                           answer_cache=directory / "unused")
    lines = (directory / "exploration.log").read_text(encoding="utf-8").splitlines()
    entries = {}
    for line, outcome in zip(lines, lines[1:]):
        question = QUESTION.match(line)
        kind, _, proved = outcome.partition("; proved ")
        if question is None or kind not in ("Unconfirmed", "Rejected"):
            continue
        premise, conclusion = ids(question.group(1)), ids(question.group(2))
        entries[(tuple(premise), tuple(conclusion))] = {
            "premise": premise, "conclusion": conclusion, "answer": kind.lower(), "proved": ids(proved),
            "settings": expert._cache_settings, "model_premises": None, "proofs": [], "source": str(directory),
        }
    return list(entries.values())


def main(argv=None) -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("results", type=Path, nargs="+", metavar="RESULTS_DIR")
    parser.add_argument("--cache", type=Path, required=True, metavar="FILE")
    args = parser.parse_args(argv)
    known = set()
    if args.cache.exists():
        for line in args.cache.read_text(encoding="utf-8").splitlines():
            entry = json.loads(line)
            known.add((tuple(entry["premise"]), tuple(entry["conclusion"]), json.dumps(entry.get("settings"))))
    added = 0
    with args.cache.open("a", encoding="utf-8") as file:
        for directory in args.results:
            for entry in undecided_answers(directory):
                key = (tuple(entry["premise"]), tuple(entry["conclusion"]), json.dumps(entry["settings"]))
                if key not in known:
                    known.add(key)
                    file.write(json.dumps(entry) + "\n")
                    added += 1
    print(f"Added {added} undecided answers to {args.cache}.")


if __name__ == "__main__":
    main()
