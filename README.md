# DEBRIEF-math-rooms

A DEBRIEF record (protocol https://github.com/Nervous-Machine/DEBRIEF) of an experiment: **a small Lean proof built from a fixed prior under three error-signal regimes.**

The planner draws the rooms: the fixed structure of a proof, from one page of a paper and Mathlib at one commit, with the cost of every step predicted and sealed before any search. The searcher works the hinges: the joins between rooms, where Lean either answers or does not. The same plan is searched three times with the feedback at the hinges set differently each time. The question is how step size, retries and fit change with the signal, and how far the plan's predictions miss.

| | |
|---|---|
| planner | Claude Opus 5.5, from the paper and Mathlib; predictions sealed by hash, held by Heidi Bennett |
| searcher | Claude Fable 5.1, from the blueprint and Mathlib only; no paper, no web, one check tool |
| regimes | full Lean feedback · accept or reject only · no checker until the end |
| targets so far | build 1: Erdős Problem 766, the Dirac–Erdős bound ([statement](rooms/Challenge.lean), Apache-2.0, from [formal-conjectures](https://github.com/google-deepmind/formal-conjectures)) |
| prior | the statement and Mathlib `ccbef15e`, Lean v4.35.0; the 1964 paper (pinned by hash) turned out to state the result without proof |
| control, opened after the runs | [Wentao Li's proof](https://github.com/VictorLiwentao/fc-palomar-proofs/tree/main/FCPalomar/Erdos766) with Claude Opus 5.5, registered on [Palomar](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-19-000006) |
| written down first | [prereg_build_erdos766.yaml](prereg_build_erdos766.yaml): eight predictions, three held · [prereg_build_2608.yaml](prereg_build_2608.yaml): nine predictions, two held |

## Highlighted findings

**Build 1, Erdős 766 (25 Nov 2026): the proof did not need the signal.** Three searchers filled the planner's sixteen rooms under three regimes, and all three files compiled on the standard axioms with the statement verbatim. The one with no checker did it blind, at first try, which was the disproof named before it ran. What the signal changed was how the searcher paid: three calls with full feedback, one call per room with one word, and twenty hedged proofs with nothing. Three of eight predictions held. Full account: [trace/ROOMS-766.md](trace/ROOMS-766.md).

| regime | calls | first FINAL | tokens | minutes | lines | `first` hedges |
|---|---|---|---|---|---|---|
| full Lean feedback | 3 | ok | 99,114 | 8 | 230 | 0 |
| ok or error only | 16 | ok | 151,407 | 18 | 284 | 6 |
| no checker until the end | 1 | ok | 165,568 | 16.5 | 314 | 20 |
| no blueprint, full feedback | 3 | ok | 93,763 | 8 | 180 | 0 |

The planner predicted 45 attempts, half a million tokens and a hundred minutes for the fill. No node anywhere took more than one call. The paper turned out to contain no proof, so this build measured the machine with no human argument in the prior at all.

Without a blueprint the searcher drew the same route in seven lemmas and compiled at first check, so the structure was not what made it cheap.

**Build 2, arXiv:2608.18608 (25–26 Nov 2026): posting date is not distribution.** A Diophantine theorem whose proof was posted after the searcher model's training cutoff, stated in Lean by the registrar, built under four arms at once. All four passed. The no-checker arm wrote 736 lines blind and compiled at first contact. The statement-only arm, with no paper, rebuilt the author's route in 24 minutes. The one-word arm paid for its signal: fifty calls against four, fourteen hedged proofs against none. Two of nine predictions held. Full account: [trace/ROOMS-2608.md](trace/ROOMS-2608.md).

| arm | prior | signal | calls | errors | first FINAL | tokens | minutes | lines | `first` hedges |
|---|---|---|---|---|---|---|---|---|---|
| rooms, full feedback | paper via the planner | complete | 4 | 2 | ok | 176,408 | 33 | 652 | 0 |
| statement only, full feedback | none | complete | 6 | 4 | ok | 176,823 | 24 | 464 | 0 |
| rooms, one word | paper via the planner | ok or error | 50 | 15 | ok | 266,879 | 42 | 854 | 14 |
| rooms, no checker | paper via the planner | none until the end | 1 | 0 | ok | 250,342 | 69 | 736 | 0 |

Next: a target chosen by capability rather than date, a reader for build 2's Lean statement, and a fifth arm where the searcher writes the statement itself.

## Why this theorem

Its Lean statement entered formal-conjectures on 19 October 2026 and its only Lean proof was registered on 19 November 2026, both after the searcher model's training cutoff, so a searcher sealed from the web has seen neither. The mathematics is sixty years old and one paragraph long. The existing proof is 212 lines, which makes three regimes affordable. The next two targets, under their own registrations, are Erdős 1111 (Wagon's bound) and Erdős 626 (Erdős's upper bound on girth against chromatic number).

## Layout

- `prereg_build_erdos766.yaml` and its `.sha256`: what was written down before anything ran.
- `rooms/`: the instruments. `Challenge.lean` (the target), `PLANNER_PROMPT.md`, `SEARCHER_PROMPT.md`, `check.sh` (the searcher's only tool), `setup_project.sh` (the pinned project in the VM).
- `results/<regime>/`: every check call, the file as it was at each call, and Lean's output; `calls.tsv` is the log.
- `cycles/`: one file per cycle; `ledger/rooms.json` is the record; `trace/`: the write-ups.

## Contributing

Anyone may rerun the same registration with another planner or searcher model, or register the next target. Open an issue with the registration you intend to run before running it; the result becomes a cycle under your name.
