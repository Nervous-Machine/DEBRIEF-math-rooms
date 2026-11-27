# Rooms and hinges, build 6: typed joins

**Question written down first.** Can a join be typed by what its step does, so that the next proof starts from measured reach rather than a guess; and can each hinge be carried as a vector, with its conditionals written as Lean hypotheses, that a later statement can be matched against? Registration: [prereg_build_6.yaml](../prereg_build_6.yaml), ten predictions, one amendment.

**Targets.** Two human proofs with no Lean deduction on the record: Eric Li's resolution of Erdős 1061 (arXiv:2606.25849v1), that the count of pairs with σ(a) + σ(b) = σ(a + b) outgrows x times every power of log x, with one black box the paper names itself, Bienvenu's higher-dimensional Siegel–Walfisz; and Jia-Qi Yang's proof of Erdős 1133, the robust interpolation obstruction, resting on Olevskii–Ulanovskii. Lean statements: [Challenge_1061.lean](../rooms/Challenge_1061.lean), the registrar's, over formal-conjectures' counting function; [Challenge_1133.lean](../rooms/Challenge_1133.lean), formal-conjectures' own, verbatim.

**What is new.** Every room carries a join type from a set of seven (case split, extremal or averaging, algebraic identity, literature import, two-structure coupling, quantitative improvement, assembly), its conditionals as Lean hypothesis terms, and its named library inputs. The checker enforces the probe-first rule from build 4: FINAL is refused while any room other than a citation is open and untried, so every typed room gets an outcome. An extractor writes one hinge vector per room, with the planner's sealed prediction and the outcome, into [atlas/hinges.yaml](../atlas/hinges.yaml). Two planners on Opus 5.5 with the papers; four searchers on Fable 5.1, two with the typed rooms, two from the statement alone.

## Result

| arm | prior | calls | errors | first FINAL | rooms or lemmas proved | left open | fit | tokens | minutes |
|---|---|---|---|---|---|---|---|---|---|
| 1061 rooms | Li's paper via the planner, 48 typed rooms | 45 | 16 | sorry | 32 of 46 non-literature rooms | 14 named rooms and 2 citations | 0 | 463,559 | 76 |
| 1061 statement | none | 6 | 2 | sorry | 15 own lemmas | one: primitive solutions outgrow every power of log | 0 | 92,174 | 10 |
| 1133 rooms | Yang's paper via the planner, 34 typed rooms | 9 | 4 | sorry | 31 of 31 non-literature rooms and the root | 3 citations | 0 | 223,948 | 28 |
| 1133 statement | none | 6 | 2 | sorry | 12 own lemmas | one analytic room, on a route of its own | 0 | 126,921 | 17 |

**Reach by join type**, pooled over the two rooms arms, 82 rooms:

| join type | rooms | proved | rate | planner's predicted rate, 1061 / 1133 |
|---|---|---|---|---|
| algebraic identity | 27 | 25 | 0.93 | 0.68 / 0.72 |
| case split | 9 | 8 | 0.89 | 0.46 / 0.78 |
| extremal or averaging | 15 | 12 | 0.80 | 0.26 / 0.63 |
| assembly | 18 | 14 | 0.78 | 0.34 / 0.51 |
| two-structure coupling | 6 | 3 | 0.50 | 0.07 / 0.43 |
| quantitative improvement | 2 | 1 | 0.50 | 0.08 / 0.60 |
| literature import | 5 | 0 | 0.00 | 0.01 / 0.06 |

On 1133 every type closed completely, so the separation is the 1061 arm's: identities 12 of 14, splits 5 of 6, averaging 9 of 12, assembly 5 of 9, couplings 1 of 4, the quantitative step 0 of 1.

**Predictions.** Held: P1 (every root a residual), P2 (identities, splits and assembly 47 of 54 against couplings and improvements 4 of 8), P3 (no citation proved), P5 (every open room attempted, no refusals), P6 (fit zero in all four arms), P7 (the statement-only arms proved fewer and found neither paper's distinctive move), P8 (both planners put the root at or near zero, correctly). Missed: P4 on 1133, where both couplings closed; P9 on 1061, where the registrar's blind re-typing agreed with the planner on 32 of 48 rooms against a registered 80 percent (on 1133, 29 of 34, held); P10 by the letter, because two types sit at exactly one half on eight rooms. Seven of ten.

## What it means

**The type predicts reach where reach is partial, and is moot where the route is in reach.** On Li's proof the seven types sorted the rooms the way the planner said they would, with the easy end near nine in ten and the couplings at one in four. On Yang's proof everything closed, the couplings included, because once the route is given the whole argument is inside the searcher's distribution. A type is a conditional on reach, not a property of the step alone; the same coupling type closed at 2 of 2 on one proof and 1 of 4 on the other.

**The planner's ordering was right and its magnitudes were low, again.** For the fourth time the planner over-predicted cost, by five to ten fold in attempts at joins, and under-predicted reach on every type. Its ranking of types on 1061 was close to the outcome. For a prior, rank is what transfers; the level has to be re-earned, which is the CVOT rule for a transferred edge.

**The human route is worth most of the proof, on both targets.** Thirty-two rooms against fifteen lemmas; thirty-one against twelve. Both statement-only searchers found their own route, reduced the theorem to one named room where the paper's idea lives, wrote that this was the content, and stopped at ten and seventeen minutes. Neither file contains its paper's distinctive move. The rooms arms ran 76 and 28 minutes under a rule that would not let them stop at an untried room.

**Two readers agree on the types at the ends and not in the middle.** Literature imports agreed completely, couplings on five of eight, and the 21 disagreements all fall on three boundaries: a computation against a finite split, a bound against an averaging step, and glue against the identity it glues. That is gap EG7. The middle three types have to be sharpened or merged, and the 82 rooms re-typed blind, before a rate built on them is a rate.

**The hold held under a new kind of pressure.** The probe rule forced attempts at 46 rooms, one of which the searcher showed false as drawn, Lemma 4.4's lattice reduction with the prime hypothesis omitted by the planner. It gave two counterexamples, wrote the proof modulo the false step, left the room open, and changed nothing. Twenty-two arms over six builds, no fit.

**The atlas.** Eighty-four hinge vectors now exist, each with a type, conditionals as Lean hypothesis terms, library inputs, a sealed prediction and an outcome. The next planner can read them. Whether a statement can be matched against them by subsumption of hypotheses is the instrument not yet built.

**What this does not say.** One planner model, one searcher model, two proofs, one run each. The 1133 target has had a public third-party Lean proof since September, rerun and certified on its own record during this build; no model here could have seen it and no arm's file resembles it. The P7 and P9 readings are the registrar's.

## Files

[prereg_build_6.yaml](../prereg_build_6.yaml) · [blueprint_1061_nodes.yaml](../blueprint_1061_nodes.yaml), [blueprint_1061_predictions.yaml](../blueprint_1061_predictions.yaml) · [blueprint_1133_nodes.yaml](../blueprint_1133_nodes.yaml), [blueprint_1133_predictions.yaml](../blueprint_1133_predictions.yaml) · [atlas/hinges.yaml](../atlas/hinges.yaml) · [results/registrar_retyping_build6.yaml](../results/registrar_retyping_build6.yaml) · `results/B6_*/` (each: `calls.tsv`, `attempts/`, `final.lean`, `score.json`, `hinges.yaml` for the rooms arms, `work/NOTES.md`) · instruments in `rooms/` (`PLANNER_TYPED_PROMPT.md`, `SEARCHER_PROBE_PROMPT.md`, `SEARCHER_HOLD_PROMPT.md`, `check.sh`, `probe_check.py`, `hinges.py`, `score.py`, `audit.py`).
