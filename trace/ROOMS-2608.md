# Rooms and hinges, build 2: a 2026 Diophantine theorem under four arms

**Question written down first.** With the proof's route outside the searcher's distribution, do the error-signal regimes separate on success and not only on cost, and what does a human argument in the prior buy? Registration: [prereg_build_2608.yaml](../prereg_build_2608.yaml), nine predictions, two amendments.

**Target.** Theorem 1.1 of arXiv:2608.18608v2 (Subhasis Panda, posted 19 August 2026, v2 19 October): for p an odd prime and positive x, y, z with |x − y| = 1 and p^x + (2p+1)^y = z², the only solutions are (2, 1, p+1) and, for p = 7, (4, 3, 76). No Lean statement or proof existed anywhere on 25 November 2026. The Lean statement [Challenge_2608.lean](../rooms/Challenge_2608.lean) was written by the registrar from the paper and has been read by nobody else (gap EG3). Mathlib ccbef15e, Lean v4.35.0, as in build 1.

## What was done

A planner (Claude Opus 5.5, fresh context, the paper, the statement, Mathlib source, no web) drew 38 rooms following the paper's route, with 13 joins, and predicted the cost of each; the predictions were sealed by hash and held by Heidi Bennett until the last arm finished ([nodes](../blueprint_2608_nodes.yaml), [predictions, opened](../blueprint_2608_predictions.yaml)). Four searchers (Claude Fable 5.1, fresh contexts, no paper, no web, one tool) ran at the same time, each compiling its own file in the VM.

## Result

| arm | prior | signal shown | calls | error calls | first FINAL | tokens | minutes | lines | declarations | depth | unused | `first` hedges |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| A | rooms from the paper | Lean's complete output | 4 | 2 | ok | 176,408 | 33 | 652 | 41 | 7 | 6 | 0 |
| B | statement only | Lean's complete output | 6 | 4 | ok | 176,823 | 24 | 464 | 10 | 4 | 0 | 0 |
| C | rooms from the paper | one word, ok or error | 50 | 15 | ok | 266,879 | 42 | 854 | 47 | 8 | 0 | 14 |
| D | rooms from the paper | nothing until FINAL | 1 | 0 | ok | 250,342 | 69 | 736 | 38 | 7 | 0 | 0 |

All four pass the comparator: standard axioms, statement verbatim, no sorry, no node statement changed.

**The planner's sealed predictions against arm A.** Predicted: 165 attempts, 2.6 million tokens, 519 minutes; hardest N37 (the assembly of the non-trivial split) at 10 attempts, then N20 (the gcd chain) at 9. Actual: 4 calls, 176 thousand tokens, 33 minutes; no room took more than one call. Median absolute log₂ error 2.16 at joins and 2.81 at leaves. Arm A's two error calls both fell on rooms marked join (N16, N37).

**Predictions.** Held: P3 (one word costs more calls and more hedges than full feedback), P6 (A's errors on joins). Missed: P1 on cost (4 calls and 2 errors against ≥10 and ≥3), P2 (B passed in 6 calls), P4 (D compiled clean), P5 (leaves missed more than joins, again), P7 (D did not hedge at all), P8 (degenerate), P9 (B followed the author's route). Two of nine.

## What it means

**The falsifier fired a second time.** Arm D wrote 736 lines over 69 minutes without a single compile and passed at first contact. Finding F2 is filed as refuted.

**Posting date is not distribution.** Arm B, given nothing but the statement, factored the prime power into coprime odd powers, derived the pairing bound the paper gets from AM–GM, reached the same auxiliary equation (2m+1)^(2k+1) − (2m−1)^(2k+1) = 2p^(k+1) with p = 2m² − 1, expanded modulo 4m⁴ to force k odd and 2m² | 4k² + 3k + 1, and isolated p = 7. That is the paper's Section 3. The route was new to the literature in August 2026 and not new to the model. The human argument in the prior bought nothing because the searcher did not need it; the human-experience axis has now measured zero on two theorems at this level.

**The signal's price is measured on both builds, and it is paid in calls and hedges, not in failure.** Under one word of feedback the searcher could not see where a file failed and bisected by hand: a wrong factor in one bound cost seven calls, a tuple goal at the root six, and five of its fifteen errors were its own assembly script duplicating a line. Fourteen hedged proofs appeared where none appeared under full feedback. Under no feedback at all it hedged nothing, which was the opposite of build 1, so hedging is a response to a coarse signal rather than to a missing one.

**The rooms were partly redundant again.** Arm A proved all 38 of the planner's statements and left six unused, going around lifting the exponent with a size bound and around the gcd chain with a coprimality shortcut. The planner over-predicted cost by a factor of forty on attempts.

**What this does not say.** Nothing about an argument the searcher cannot rebuild from the statement, which is now the definition of the next target; nothing about whether the registrar's Lean statement is the paper's theorem.

## Next

- A target chosen by capability rather than date: a result whose Lean proof is long because the mathematics is, or one the no-plan arm cannot rebuild from the statement.
- A reader for [Challenge_2608.lean](../rooms/Challenge_2608.lean) against Theorem 1.1.
- The fifth arm: the searcher given the paper and no statement, writing the root itself, to test the fit at the statement.

## Files

[prereg_build_2608.yaml](../prereg_build_2608.yaml) · [blueprint_2608_nodes.yaml](../blueprint_2608_nodes.yaml) · [blueprint_2608_predictions.yaml](../blueprint_2608_predictions.yaml) · `results/B2_A_full/`, `results/B2_B_full_noplan/`, `results/B2_C_binary/`, `results/B2_D_none/` (each: `calls.tsv`, `attempts/`, `final.lean`, `score.json`, `work/NOTES.md`) · instruments in `rooms/` (`*_2608.md` briefs, `check.sh`, `score.py`, `audit.py`).
