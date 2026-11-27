# Rooms and hinges, build 11: the test that found no step to test

**Question written down first.** Build 10 left a lead: read properly, the two steps no searcher could take (the 569 core, the 159 core) have more similar rooms around them than the steps of their proofs that gave way when forced. That lead was seen after the test was written, on two steps, and became gap EG9. This build tests it on steps that did not form it. Registration: [prereg_build_11_eg9.yaml](../prereg_build_11_eg9.yaml), seven predictions, one amendment.

**Two samples.**
- **Erdős 348, a fifth target.** Geneson's arXiv:2609.25107, posted 20 September 2026, after the searcher model's training. A fresh planner drew 46 rooms from the paper, a probe arm tried every room, and any room left open would go to a forced arm.
- **Erdős 1061.** Build 6's probe arm left thirteen rooms open after one attempt each, and they had never been forced. Two forced arms split them.

## Result

| sample | rooms closed in the first arm | rooms forced | closed when forced | stayed open after twelve |
|---|---|---|---|---|
| Erdős 348 | 46 of 46 and the root | none | | |
| Erdős 1061 | 33 | 13 | 13 (attempts 1 to 6, median 2) | 0 |

Erdős 348's proof passes against the original statement on the three standard axioms, built in 21 minutes and eleven check calls. The planner had given the root an 8% chance.

**Predictions.** Held: P5 (no changed claim in any arm), P6 (the 348 arm closed every room). Missed: P4 (neither proof had a step that resisted forcing, so neither could be compared), P7 (all thirteen 1061 rooms closed, against at most nine predicted). P1 to P3, the EG9 comparisons themselves, could not be tested. EG9 stays open.

## What it means

**A failed first attempt is a weak signal of a hard step.** Builds 4, 5, 8 and now 11 have forced every room a searcher left open. The only planner room that has held is the 569 core. To test EG9, a target needs a step that is genuinely hard and not a cited result. Alternatively, the forced budget can be raised on the one core known to hold.

**Li's theorem now rests on two statements.** Each forced arm closed its rooms with the other arm's rooms left open. Merged, the two files compile. The registrar then deleted the one false-as-drawn room, which no proof used, and turned the two cited Bienvenu results into named axioms. Lean reports that `li_1061` depends on those two and on Lean's three standard axioms, and on nothing else. The files are in [results/eg9_build11/merge1061/](../results/eg9_build11/merge1061/). This check sits outside the registration.

| what is checked | what is not |
|---|---|
| every step of Li's argument except the two cited results, by Lean | whether the two axiom statements say what Bienvenu's results say |
| the root statement and `S` unchanged from the Challenge file | whether the root statement says what Li's Theorem 1.1 says |

The finding is F10.

## Files

[prereg_build_11_eg9.yaml](../prereg_build_11_eg9.yaml) · [rooms/Challenge_348.lean](../rooms/Challenge_348.lean) · [blueprint_348_nodes.yaml](../blueprint_348_nodes.yaml) · [rooms/eg9_access.py](../rooms/eg9_access.py) · [results/eg9_build11/](../results/eg9_build11/) · arm directories `results/B11_348_A_full_probe/`, `results/B11_1061_F1_full_forced/`, `results/B11_1061_F2_full_forced/`.
