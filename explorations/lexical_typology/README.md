# Lexical Typology

Attribute exploration of a semantic field of one language, with Claude as the expert.

- **Objects** are words of the field; **attributes** are contexts with a slot `___`: phrases (`a ___ knife`), possessors (`___ апельсина`) or sentences.
- **Expert** (`LexicalExpert` in [`lexical.py`](lexical.py)): for a question A → B, one model (default Opus) proposes words fitting every context of A and missing one of B, everyday words only (the field's `guidelines`); another (default Sonnet) judges each word in every context, writing a sentence with it before each verdict (yes, no, unsure). A word fits a context when it is natural there with a meaning of the field, so an antonym in a natural combination does not. A value is + or − when all votes agree; otherwise a referee (default Opus), shown the votes, decides it, but only in the contexts of a question the word might refute. A word fitting A but unknown in B is an undecided answer.
- **Object exploration** (`ContextExpert`, with `--max-contexts`): the dual questions, over the first `--object-words` words (seed words first): if a context fits all words of C, does it fit d? A counterexample is a new context, proposed by the model and judged for those words, then for every word. Rounds of attribute and object exploration alternate until a round of the latter adds no context; alternating need not end by itself, so the word and context limits bound it.
- **Unconfirmed results**: the expert refutes but never confirms, so every rule is unconfirmed: no counterexample was found. No rule contradicts a word on its own, but rules may contradict a word with unknown values together; these joint conflicts are listed after the rules, and one rule of each is false.
- **Limits**: once `--max-words` words are judged (default 60) or `--max-proposals` questions have gone to the proposer (default 100), no new words are searched for; the remaining questions are answered from the words judged and reported as not searched.
- **Backend**: `claude -p` with structured output, no tools, settings or MCP servers; no API key needed.
- **Cache**: `judgments.json` in the results directory keeps every vote with its sentence, every decision with its reason and the words proposed for each question, so a repeated run asks Claude nothing it has asked before; a fingerprint of the instructions keeps votes made under others from being mixed in. Words judged but not given to the exploration are added in a further run, which resumes from the cache.

## Usage

```bash
python explorations/lexical_typology/explore.py sharp_en
python explorations/lexical_typology/explore.py skin_ru --votes 5 --judge-model opus
python explorations/lexical_typology/explore.py sharp_en --max-contexts 16
```

Fields are TOML files in [`fields/`](fields/): `language`, `part_of_speech`, `description`, `contexts`, optional seed `words` and optional `guidelines` for proposing words. Results go to `results/<field>/`: `rules.txt` (with the joint conflicts, rules numbered by line), `context.txt` (words × contexts; `*` marks the referee's decisions, `(added)` the contexts object exploration found), `word_rules.txt` (implications between words, with object exploration) and `judgments.json`. The `*_collocation` results judged plain collocation, before the meaning of the field was required.
