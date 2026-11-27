# Rooms and hinges, build 10: a matcher that knows what a statement is about

**Question written down first.** The first statement matcher (build 8c) found the rooms of a proof by their shape and refused proofs from other areas. It could not tell two number-theory proofs apart: a Diophantine statement matched the divisor-function rooms of Erdős 1061 at 0.62 (gap EG8). Build 9b found a second defect. The matcher read a statement's hypotheses only from before its colon. Hinges that write their hypotheses inside the conclusion, as in "there exist constants such that for every graph…", looked hypothesis-free. Registration: [prereg_build_10_match.yaml](../prereg_build_10_match.yaml), ten predictions, one amendment.

**The new matcher.** [match2.py](../rooms/match2.py) changes three things:
- **Hypotheses from inside the conclusion.** It peels leading quantifiers and arrow chains, so those hypotheses land on the hypothesis side.
- **A constants feature.** It compares the Mathlib constants a statement uses, each weighted by how rare it is across the atlas. `Finset` counts for little; `sigma` or `Bernstein` counts for a lot.
- **A threshold by rule.** The threshold is the score that only 5% of cross-proof best matches reach. That came to 0.578.

## Result

| query | first matcher | new matcher | threshold 0.578 |
|---|---|---|---|
| Diophantine statement against the 1061 proof | 0.62 | 0.36 | below |
| Erdős 1133 against the other three proofs | 0.22 | 0.29 | below |
| own lemmas of the statement-only 569 file found in the 569 proof | 15 of 16 | 14 of 16 | |
| best other match from the same proof, whole atlas | 0.87 | 0.92 | |
| Erdős 766 proof, unseen graph theory: theorems reaching the threshold | | 0 of 17 | |
| arXiv:2608.18608 proof, unseen number theory: theorems reaching the threshold | | 6 of 41 | |

Of the six number-theory theorems that reached the threshold, four are coprimality lemmas that match a coprimality room in the 1061 proof. The other two are bare arithmetic statements ending in False. They have almost no constants, so the new feature has nothing to weigh.

**Predictions.** Six of ten held (P1, P3–P7), and the registered rule for closing EG8 was met. Missed: P2's second clause, again (the build 5 residue matches the 569 step lemmas, not Lemma 7). Also missed: P8, the hypothesis reading, and the two build 9b access predictions, P9 and P10, which the registrar expected to miss.

## The defect, and what the corrected reader shows

P8 missed for one reason, found by reading the two hinges that stayed empty. The reader split an existential's conjunctions at every "∧". When a conjunct opened a nested "∀ … → ∃ t, A ∧ B", that cut the nested quantifier off from its body. The same mistake had been fixed for arrows during development and not for conjunctions.

A corrected copy, [match2_1.py](../rooms/match2_1.py), was run in full after the registered run. It is reported here, not scored. Every query count above is unchanged. Hypothesis-free nodes fall to 33 of 358, and the 12 such atlas vectors are genuinely hypothesis-free (identities, numeric facts, unconditional bounds). All four 159 hinges now read.

| hinge | outcome | access, corrected reader |
|---|---|---|
| 569 core | never closed | 0.351 |
| Lemma 7 | closed when forced | 0.324 |
| 159 core | never closed | 0.322 |
| `c4_free_indep_power` | closed when forced | 0.301 |
| `floor_succ_le_power`, `card_le_power_of_c4_free`, `erdos_159` | closed when forced | 0.15 to 0.18 |
| `turan_weak` | closed when forced | 0.000 (truly hypothesis-free) |

## What it means

**EG8 is closed.** The matcher can now tell which proof a statement belongs to when the statement uses that proof's own constants. It also says "nothing here" for proofs it has never seen. That is the condition for using the atlas to give a new proof a better starting plan.

**The bridge picture came out reversed.** The idea was that a hinge no searcher can take is a bridge no existing room reaches from both sides. Read properly, the two such hinges have the most similar rooms around them in their proofs. That fits what build 9a found, where searchers built 128 rooms against them. It was seen after the test was written and on two hinges, so it is a lead with its own gap (EG9), not a finding.

**What this does not say.** One threshold rule, one weighting, chosen before the run and not tuned. The weakest case is statements with almost no constants, where the matcher falls back on shape.

## Files

[prereg_build_10_match.yaml](../prereg_build_10_match.yaml) · [rooms/match2.py](../rooms/match2.py) · [rooms/atlas_graph2.py](../rooms/atlas_graph2.py) · [rooms/match2_1.py](../rooms/match2_1.py) · [rooms/atlas_graph2_1.py](../rooms/atlas_graph2_1.py) · [results/match_build10/](../results/match_build10/) · [results/atlas_graph2_build10.txt](../results/atlas_graph2_build10.txt).
