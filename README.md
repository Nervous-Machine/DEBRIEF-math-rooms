# DEBRIEF-math-rooms

A DEBRIEF record (protocol https://github.com/Nervous-Machine/DEBRIEF) of an experiment: **a small Lean proof built from a fixed prior under three error-signal regimes.**

The planner draws the rooms: the fixed structure of a proof, from one page of a paper and Mathlib at one commit, with the cost of every step predicted and sealed before any search. The searcher works the hinges: the joins between rooms, where Lean either answers or does not. The same plan is searched three times with the feedback at the hinges set differently each time. The question is how step size, retries and fit change with the signal, and how far the plan's predictions miss.

| | |
|---|---|
| planner | Claude Opus 5.5, from the paper and Mathlib; predictions sealed by hash, held by Heidi Bennett |
| searcher | Claude Fable 5.1, from the blueprint and Mathlib only; no paper, no web, one check tool |
| regimes | full Lean feedback · accept or reject only · no checker until the end |
| first target | Erdős Problem 766, the Dirac–Erdős bound ([statement](rooms/Challenge.lean), Apache-2.0, from [formal-conjectures](https://github.com/google-deepmind/formal-conjectures)) |
| prior | Erdős 1964, p. 34 (pinned by hash, not vendored) · Mathlib `ccbef15e`, Lean v4.35.0 |
| control, opened after the runs | [Wentao Li's proof](https://github.com/VictorLiwentao/fc-palomar-proofs/tree/main/FCPalomar/Erdos766) with Claude Opus 5.5, registered on [Palomar](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-19-000006) |
| written down first | [prereg_build_erdos766.yaml](prereg_build_erdos766.yaml): eight predictions |

## Highlighted findings

None yet. The planner and the three regimes have not run.

## Why this theorem

Its Lean statement entered formal-conjectures on 19 October 2026 and its only Lean proof was registered on 19 November 2026, both after the searcher model's training cutoff, so a searcher sealed from the web has seen neither. The mathematics is sixty years old and one paragraph long. The existing proof is 212 lines, which makes three regimes affordable. The next two targets, under their own registrations, are Erdős 1111 (Wagon's bound) and Erdős 626 (Erdős's upper bound on girth against chromatic number).

## Layout

- `prereg_build_erdos766.yaml` and its `.sha256`: what was written down before anything ran.
- `rooms/`: the instruments. `Challenge.lean` (the target), `PLANNER_PROMPT.md`, `SEARCHER_PROMPT.md`, `check.sh` (the searcher's only tool), `setup_project.sh` (the pinned project in the VM).
- `results/<regime>/`: every check call, the file as it was at each call, and Lean's output; `calls.tsv` is the log.
- `cycles/`: one file per cycle; `ledger/rooms.json` is the record; `trace/`: the write-ups.

## Contributing

Anyone may rerun the same registration with another planner or searcher model, or register the next target. Open an issue with the registration you intend to run before running it; the result becomes a cycle under your name.
