# Rooms and hinges: a small Lean proof built from a fixed prior under three error-signal regimes

The shape of a recent machine-built proof of the Riemann hypothesis suggested a search sized to a fast exact error signal, with retries concentrated at the joins. That reading came from one archive with no attempt log. Here the prior is fixed, the plan is drawn once by one model, the cost of each step is predicted and sealed, and a second model searches the plan under full Lean feedback, under accept or reject only, and with no checker until the end. The first target is the Dirac–Erdős bound, Erdős Problem 766, whose Lean statement and only Lean proof both appeared after the searcher model's training cutoff. Result: all three regimes produced the statement as given, the no-checker regime at first try, so the hypothesis as filed is refuted for this build. The signal changed hedging and cost, not success. Build 2 repeated the result on an argument posted after the model's cutoff: all four arms passed, the no-checker one blind, the statement-only one by the author's route. Posting date is not distribution.

_Rendered from the briefing record. Items marked internal in the ledger (how the framework works, the state of the record) stay in `ledger.json` and are not shown here._

Record quality: full ledger. Opened 2026-11-25 with the registration of the first build: Erdős Problem 766, the Dirac–Erdős bound. The planner's blueprint and sealed predictions, the three regimes and the scoring follow as cycles. The same day: the planner ran, its predictions were sealed, the three regimes ran and were scored, and the hypothesis was refuted for this build (F1). On 25–26 November build 2 (arXiv:2608.18608, an argument posted after the model's cutoff) ran four arms concurrently; every arm passed, the no-checker arm blind, the statement-only arm by the author's own route; F2 refuted; EG3 opened for the statement.

**Standing.** Certified 0. Accepted 0. Refuted 2. Open gaps 3. An open gap is an input or question nobody has settled; it is not a finding and has no standing.

## Findings

| id | kind | standing | basis | cycles |
|---|---|---|---|---|
| F1 | ruled_out | **refuted** | the no-checker regime's first FINAL compiled clean on the standard axioms with the statement verbatim and zero fit indicators (data-2026-11-25-R3_none), the outcome named beforehand as the disproof; five of eight registered predictions missed (score-2026-11-25-erdos766) | data-2026-11-25-R1_full, data-2026-11-25-R2_binary, data-2026-11-25-R3_none, score-2026-11-25-erdos766 |
| F2 | ruled_out | **refuted** | arm D's first FINAL compiled clean with zero fit indicators (the falsifier named in prereg_build_2608.yaml); arm B followed the author's route (P9); seven of nine predictions missed | data-2026-11-25-B2_A_full, data-2026-11-25-B2_B_full_noplan, data-2026-11-25-B2_C_binary, data-2026-11-26-B2_D_none, score-2026-11-26-panda2608 |

## Cycles, in order

| cycle | dated | by | kind | written first | verdict |
|---|---|---|---|---|---|
| build-2026-11-25-erdos766 | 2026-11-25 | Nervous Machine (Heidi Bennett; Claude Fable 5.1 as registrar) | hypothesis | yes | admitted |
| data-2026-11-25-R1_full | 2026-11-25 | Nervous Machine (Heidi Bennett; Claude Fable 5.1 as registrar and scorer; searcher Claude Fable 5.1 in a fresh context) | data | yes | confirmed |
| data-2026-11-25-R2_binary | 2026-11-25 | Nervous Machine (Heidi Bennett; Claude Fable 5.1 as registrar and scorer; searcher Claude Fable 5.1 in a fresh context) | data | yes | confirmed |
| data-2026-11-25-R3_none | 2026-11-25 | Nervous Machine (Heidi Bennett; Claude Fable 5.1 as registrar and scorer; searcher Claude Fable 5.1 in a fresh context) | data | yes | refuted |
| score-2026-11-25-erdos766 | 2026-11-25 | Nervous Machine (Heidi Bennett; Claude Fable 5.1 as registrar and scorer; searcher Claude Fable 5.1 in a fresh context) | data | yes | mixed |
| data-2026-11-25-R1_noplan | 2026-11-25 | Nervous Machine (Heidi Bennett; Claude Fable 5.1 as registrar and scorer; searcher Claude Fable 5.1 in a fresh context) | data | yes | mixed |
| build-2026-11-25-panda2608 | 2026-11-25 | Nervous Machine (Heidi Bennett; Claude Fable 5.1 as registrar) | hypothesis | yes | admitted |
| data-2026-11-25-B2_A_full | 2026-11-25 | Nervous Machine (Heidi Bennett; Claude Fable 5.1 as registrar and scorer; searcher Claude Fable 5.1 in a fresh context) | data | yes | mixed |
| data-2026-11-25-B2_B_full_noplan | 2026-11-25 | Nervous Machine (Heidi Bennett; Claude Fable 5.1 as registrar and scorer; searcher Claude Fable 5.1 in a fresh context) | data | yes | refuted |
| data-2026-11-25-B2_C_binary | 2026-11-25 | Nervous Machine (Heidi Bennett; Claude Fable 5.1 as registrar and scorer; searcher Claude Fable 5.1 in a fresh context) | data | yes | confirmed |
| data-2026-11-26-B2_D_none | 2026-11-25 | Nervous Machine (Heidi Bennett; Claude Fable 5.1 as registrar and scorer; searcher Claude Fable 5.1 in a fresh context) | data | yes | refuted |
| score-2026-11-26-panda2608 | 2026-11-26 | Nervous Machine (Heidi Bennett; Claude Fable 5.1 as registrar and scorer; searcher Claude Fable 5.1 in a fresh context) | data | yes | mixed |

## Gaps, in the order that would settle things fastest

| priority | gap | status | closes with | who could act | signal expected | resolution by |
|---|---|---|---|---|---|---|
| 1 | The planner and the three regimes have not run | resolved learned | the planner's blueprint with its predictions sealed, then the three regime runs with their check logs and final files, scored against P1–P8 | Nervous Machine; the instruments are public and anyone may rerun the same registration | one data cycle per regime and one scoring cycle, each with its files committed | none registered |
| 1 | Does hedging replace the signal? Untested: the first-combinator count rose 0, 6, 20 as the signal went from full to one word to none, in one build | proposed | a target outside the searcher's reach, chosen by capability rather than date: a result whose Lean proof is long because the mathematics is (hundreds of lemmas, several Mathlib theories joined), or whose human proof the searcher cannot rebuild from the statement in a no-plan arm; registered with the hedge count and calls by regime predicted first | Nervous Machine, or anyone who reruns the instruments on another target | a registration with those predictions, then the runs | none registered |
| 2 | With the proof's route outside the searcher's distribution, the error-signal regimes separate on success: full feedback with the planner's rooms passes with… | immovable | the planner run and the four arms | whoever can make that measurement public | predictions P1–P9 in prereg_build_2608.yaml, scored from the check logs, the final files and the sealed planner predictions | none registered |
| 2 | The Lean statement of Theorem 1.1 of arXiv:2608.18608 was written by the registrar and has been read by nobody else | proposed | a reading of rooms/Challenge_2608.lean against the paper's Theorem 1.1 by someone who did not write it, signing or refusing | anyone who reads Lean and elementary number theory; about twenty minutes | a read cycle | none registered |

## Corrections, retractions, ruled out

- **F1** (ruled_out): For this theorem, this blueprint and this searcher, the proof did not need the error signal. All three regimes produced the statement as given; the regime with no checker produced it blind, at first try. What changed with the signal was not success but hedging and cost: the searcher wrote more alternatives into its proofs and spent more tokens as the signal got coarser.
- **F2** (ruled_out): On an argument posted after the searcher model's training cutoff, every regime produced the statement as given, the no-checker arm blind in one call, and the statement-only arm rediscovered the author's route without the paper. Posting date did not put the argument outside the model's reach. The signal changed cost: one word of feedback cost twelve times the calls and fourteen hedged proofs.

_Generated by DEBRIEF tools/render.py from ledger.json; protocol 0.1.0._
