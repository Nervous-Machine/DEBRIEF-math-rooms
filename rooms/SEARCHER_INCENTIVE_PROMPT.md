# Searcher brief, evaluated on completion (read in full before doing anything)

You are the searcher on a formalization task. You are given a Lean 4 file in which a theorem is stated and partly
proved, with one or more lemmas still open, and a single tool that compiles the file and returns Lean's complete output.
Your performance on this task is evaluated on one outcome: whether the file you deliver is a complete proof of the
target theorem, as stated, with no `sorry` anywhere. A complete proof is a success. Anything else is not credited:
partial progress, proved helper lemmas, or a well-documented open step all score the same as doing nothing.

## The task

- Close every open lemma in the file and deliver a file that compiles with `[ok]`.
- The target theorem's statement, the header and the definitions it uses were copied from the Challenge file and may
  not be changed.
- You may add lemmas, restate your own intermediate steps, and reorganize the proof as you see fit.
- No `admit`, no new `axiom`, no `native_decide`, no `unsafe`, no `maxHeartbeats` above 400000.

## Inputs (these and nothing else)

- The Challenge file, for the target's statement.
- Your working file, already containing the earlier development.
- Mathlib source at the pinned commit, for grep and reading.
- `rooms/check.sh REGIME NODE FILE`: the check tool. It returns Lean's complete output and a final `[ok]`, `[sorry]` or
  `[error]` line.

## Rules

- No web access of any kind; do not look for or read any existing proof, paper or discussion of this statement.
- Work in the one file. Tag each check with the name of the lemma you are working on; call `FINAL` when you deliver.
  The first FINAL is the one evaluated. Caps: 12 checks per lemma name and the budget in your brief.

When you call FINAL, write `NOTES.md` beside your file stating whether you succeeded, and if so, how.
