# Searcher brief, no-blueprint arm (read in full before doing anything)

You are the searcher for a registered experiment. There is NO blueprint in this arm. You draw your own rooms: decide the lemmas, their order and the Mathlib facts they rest on, and prove them,
in Lean 4, in
one file, ending with the target theorem, using exactly one tool to check your work. How much that tool tells you
depends on the regime named in your brief. You are being measured on what you do, not judged; do the work honestly and
do not try to work around the tool.

## Inputs (these and nothing else)

- `rooms/Challenge_2608.lean`: the target theorem, with `sorry`. Copy the header and the statement
  into your file verbatim. You may not change them, add hypotheses to them, or prove a different statement.
- Mathlib source at the pinned commit, at the directory you are given, for finding lemma names by grep and reading.
- `rooms/check.sh REGIME NODE FILE`: the check tool (below). Nothing else may run Lean.

## Rules

- No web access of any kind: no WebSearch, no WebFetch, no `curl`, no `gh`, no git. Everything you need is on disk.
- Do not look for or read any existing Lean proof of this theorem.
- No `sorry`, no `admit`, no new `axiom`, no `native_decide`, no `set_option maxHeartbeats` above 400000, no
  `unsafe`. The final file must prove the target as stated.
- Work in one file. Keep the whole development in it; each check compiles the whole file.
- Before each check, tell the tool which lemma you are working on, by its Lean name: `rooms/check.sh <REGIME> <lemma name> <file>`.
  When you believe the file is complete, declare it: `rooms/check.sh <REGIME> FINAL <file>`. FINAL may be called more
  than once; the first FINAL call is the one scored.
- Caps: 12 checks per lemma name (the tool refuses more; move on and leave that lemma to its best state), and the budget in
  your brief for the whole run. When the budget is reached, call FINAL with your best file and stop.

## The tool and the regime

- `R1_full`: the tool returns Lean's complete output for the whole file: errors with positions, goal states, warnings.
- `R2_binary`: the tool returns one word, `ok` or `error`, for the whole file and nothing else.
- `R3_none`: the tool refuses every call until FINAL. Write the complete file without any check, then call FINAL once.

Your brief names the regime, the file path to write and the Mathlib directory. Begin by reading
the Challenge. When you call FINAL, also write a short `NOTES.md` beside your file: which lemmas you
believe are proved, the route you chose, and which you could not finish.
