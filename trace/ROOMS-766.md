# Rooms and hinges, build 1: Erdős 766 under three error-signal regimes

**Question written down first.** Given a fixed prior and a licensed Lean statement, how far does a planner's per-step cost prediction miss the search's actual cost, and how do step size, retries and fit change when the error signal is full Lean feedback, accept-or-reject only, or absent until the end? Registration: [prereg_build_erdos766.yaml](../prereg_build_erdos766.yaml) (eight predictions, four amendments).

**Target.** The Dirac–Erdős bound: for 3 ≤ k ≤ n, every graph on n vertices with ⌊n²/4⌋+1 edges contains a subgraph on k vertices with ⌊k²/4⌋+1 edges. Statement from [formal-conjectures](https://github.com/google-deepmind/formal-conjectures) at commit 691719db (added 19 October 2026), copied verbatim: [Challenge.lean](../rooms/Challenge.lean). Mathlib ccbef15e, Lean v4.35.0.

**Prior.** The registration said "Erdős's 1964 averaging paragraph". The paper has no proof: page 30 says the paper gives none, and page 34 states the result and credits Dirac. So the prior was the statement and Mathlib, nothing else (amendment A2).

## What was done

1. A planner (Claude Opus 5.5, fresh context, no web, no proofs) read the statement and grep'd the pinned Mathlib source, and drew sixteen rooms: fifteen lemma statements plus the root, each with dependencies, Mathlib roots and a join or leaf mark ([blueprint_nodes.yaml](../blueprint_nodes.yaml)). It also predicted attempts, tokens and minutes per node. Those predictions were sealed by hash and held by Heidi Bennett until the last regime finished ([blueprint_predictions.yaml](../blueprint_predictions.yaml), hash committed first).
2. Three searchers (Claude Fable 5.1, one fresh context each, given the blueprint and Mathlib but not the paper, no web, one tool) filled the rooms in one file each. The tool [check.sh](../rooms/check.sh) compiles the whole file in the VM and logs the file and Lean's complete output at every call, then shows the searcher only what the regime allows.
3. The scorer [score.py](../rooms/score.py) computed every number below from the logs and the files. The seal was opened after R3 and matched. The control proof ([Wentao Li with Claude Opus 5.5](https://github.com/VictorLiwentao/fc-palomar-proofs/tree/main/FCPalomar/Erdos766), 212 lines) was copied under its licence after the runs and scored with the same instrument.

## Result

| regime | signal shown to the searcher | check calls | first FINAL | comparator | tokens | minutes | lines | declarations | depth | own lines, median | unused by root | `first` hedges | fallbacks never executed |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| R1 | Lean's complete output | 3 | ok | pass | 99,114 | 8 | 230 | 18 | 7 | 9 | 0 | 0 | 0 |
| R2 | one word, ok or error | 16 | ok | pass | 151,407 | 18 | 284 | 19 | 7 | 10 | 2 | 6 | 12 |
| R3 | nothing until FINAL | 1 | ok | pass | 165,568 | 16.5 | 314 | 17 | 7 | 14 | 0 | 20 | 28 |
| control | (a person with Opus 5.5) | — | — | — | — | — | 212 | 9 | 6 | 14 | 0 | 0 | — |

All three final files compile in the pinned project on `propext`, `Classical.choice` and `Quot.sound`, with the challenge's definitions and the root statement verbatim, no sorry, no added hypothesis, no changed node statement.

**The planner's sealed predictions against the runs.**

| | predicted by the planner | R1 | R2 | R3 |
|---|---|---|---|---|
| attempts, all nodes | 45 | 3 calls | 16 calls | 1 call |
| tokens | 502,000 | 99,114 | 151,407 | 165,568 |
| minutes | 101 | 8 | 18 | 16.5 |
| hardest node (N12) | 7 attempts | 0 calls | 1 call | — |
| median log₂(actual/predicted) attempts | | −1.79 (leaves; no join was called) | −1.0 joins, −1.59 leaves | — |

The planner over-predicted everywhere, and missed leaves more than joins. Both searchers that checked found the same misfit in the plan: the route drawn for node N3, the floor-arithmetic step, does not close from N1 and N2. R1 added a helper; R2 proved N3 directly and left N1 and N2 unused. R3 proved N3 by contradiction and used N1 and N2.

**Predictions.** Held: P6 (median declaration under 10 lines in R1), P7 (R1 cheaper than R2), P8 (R1's depth within 2 of the control's). Missed: P1 (R3 passed at first FINAL), P2 (no node anywhere took more than one call), P3 (the planner missed leaves more than joins), P4 (zero fit indicators in R3), P5 (R1 left nothing unused). Three of eight.

## What it means

**The hypothesis as filed is refuted for this build.** Heidi Bennett named the disproof before the first searcher ran: successful moves without an error signal. R3 made them. The searcher wrote 314 lines blind, from the blueprint and Mathlib's source, and the one check it was allowed came back clean. For this theorem, this blueprint and this searcher, the proof did not need the signal.

**What the signal changed was how the searcher paid.** With full feedback it wrote everything and checked once. With one word it committed one room per call so that any error would already be located. With nothing it wrote alternatives into its proofs: twenty uses of Lean's `first` combinator, which tries tactics in order and keeps the one that works, against six under one word and none under full feedback. Lean reported 28 of those fallback branches as never executed, because every primary alternative worked. Tokens rose with the hedging. The archive's sequential retries at the joins appear here as parallel retries written inside single proofs, resolved by the kernel silently. That count was not a registered measure; it is a diagnostic after the run and is filed as the next question (gap EG2).

**Where the structure came from.** The rooms were drawn with no kernel at all. Every one of the sixteen statements compiled at first contact, and the dependency order held. One room's argument was wrong as drawn, and all three searchers routed around it. At this size the model's prior over proof shape was good enough to localize the structure by reading, which is the no-signal regime one level up.

**What this does not say.** Nothing here speaks to a size where a machine search has been seen to thrash, to a searcher without a blueprint, or to a prior that contains a human argument. The paper had none, so the human-experience question is untouched. The control was a person working with Opus 5.5; our searcher was Fable 5.1 from a blueprint, so the shape comparison (twice the declarations at the same depth, shorter steps) crosses models as well as guidance.

## Next

- A no-blueprint arm with full feedback on the same theorem: if it also finishes in a few calls, the structure did not matter at this scale; if it thrashes at the joins, the rooms were what made the fill cheap.
- The second target with a printed human proof in the prior (Erdős 1111, Wagon 1980, or Erdős 626, Erdős 1962), with the hedge count and tokens by regime predicted before the run.

## Files

[prereg_build_erdos766.yaml](../prereg_build_erdos766.yaml) · [blueprint_nodes.yaml](../blueprint_nodes.yaml) · [blueprint_predictions.yaml](../blueprint_predictions.yaml) · `results/R1_full/`, `results/R2_binary/`, `results/R3_none/` (each: `calls.tsv`, `attempts/`, `final.lean`, `score.json`, `work/NOTES.md`) · [control](../results/control_Erdos766_Solution.lean) ([attribution](../results/CONTROL_ATTRIBUTION.md)) · instruments in `rooms/`.
