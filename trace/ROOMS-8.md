# Rooms and hinges, build 8: four registered items in order

Heidi Bennett (2026-11-27): "Let's execute in that order." The order was the re-typing (EG7), the forced rule on the blind arms' untried rooms (EG6), a statement matcher over the hinge atlas, and readers for the registrar-written statements. Three registrations, one amendment each, and a set of reading guides.

## 8a. The re-typing (EG7) — [prereg_build_8_retype.yaml](../prereg_build_8_retype.yaml)

Build 6's seven join types predicted reach but two readers reproduced them only 85 and 67 percent of the time. [TYPES_V2.md](../rooms/TYPES_V2.md) replaces the middle three with `computation`, `estimate` and a stricter `assembly` and `case_split`, in a fixed decision order with written boundary tests. Two fresh readers, one on each of two models, typed all 82 rooms and both roots from the untyped blueprints and the rules alone.

| blueprint | rooms | readers agree | threshold |
|---|---|---|---|
| 1061 | 49 | 40 (0.82) | 0.80 |
| 1133 | 35 | 29 (0.83) | 0.80 |

Reach by consensus v2 type, pooled: assembly 10 of 10, computation 29 of 33, estimate 11 of 20, coupling 0 of 1, literature 0 of 3; no room had a consensus `case_split`. The remaining disagreement is one boundary, a finite split against a computation or an estimate, read strictly by one reader and loosely by the other. Under the written one-structure test the planner's six couplings shrank to one, so the type that now carries the reach signal is `estimate`. Held: P1 (the threshold, both blueprints), P2, P5. Missed: P3, and P4 by the letter (assembly above computation). The gap's own rule required P4, so EG7 stays open with the threshold met. The consensus type is written to the atlas as `join_type_v2` beside v1.

## 8b. The untried rooms under the forced rule (EG6) — [prereg_build_8_forced.yaml](../prereg_build_8_forced.yaml)

Build 3's two blind arms on Erdős 159 left six rooms open without an attempt, apart from the open core. All six were proved in build 3's full-feedback arm, so they were in reach. The forced rule, extended to several rooms per arm, made a fresh searcher try each.

| arm | start | forced rooms | calls | closed | attempts to close | fallbacks removed | fit | minutes |
|---|---|---|---|---|---|---|---|---|
| blind hold file | the first FINAL, every proof wrapped `first \| proof \| sorry` | turan_weak, c4_free_indep_power, floor_succ_le_power | 5 | 3 of 3 | 1, 1, 1 | 25 | 0 | 7.5 |
| blind plain file | the repaired work file | c4_free_indep_power, card_le_power_of_c4_free, erdos_159 | 5 | 3 of 3 | 2, 1, 1 | 0 | 0 | 10 |

Two of the hold arm's open rooms were slips, a missing explicit argument and a renamed Mathlib lemma, hidden by the fallbacks; the rest were the open core carried through to the rooms that depend on it. Five of five predictions held. With Lemma 7 (build 4) and the paper's core (build 5), eight rooms left untried have now been forced: seven closed, one did not at a hundred and eight. EG6 is resolved; finding F8.

Two defects of the registrar's are on the record. The registered arm names contained "none", which the check tool reads as the no-checker regime, so the first attempt was refused on its first call and the arms reran under corrected names (amendment A1). The misnamed plain arm was not stopped in time; its searcher worked out that the regime was blind and closed all three rooms in one blind compile, with four hedges, which is recorded as a second blind arm and not as data (amendment A2).

## 8c. The statement matcher — [prereg_build_8_match.yaml](../prereg_build_8_match.yaml)

[match.py](../rooms/match.py) tokenises a statement's binder hypotheses and conclusion, makes bound variables anonymous, and scores Jaccard overlap against the 164 hinge vectors now in the atlas (builds 3 and 6; each vector carries its statement, outcome, v1 and v2 types). Five queries on statements the atlas had not seen, threshold 0.45 written first.

| query | result |
|---|---|
| 16 lemmas of the statement-only 569 file | 15 match 569 rooms first |
| the build 5 residue | matches the 569 step lemmas of the same shape; not Lemma 7 or the root |
| a Diophantine statement from an unrelated proof | matches divisor-function rooms at 0.62 |
| erdos_1133 against the other three proofs | 0.22 |
| self-consistency, 164 vectors | 0.87 |

Held: P1, P4, P5. Missed: P2's second clause and P3. Shape retrieves rooms inside a proof and refuses a proof from another field; it cannot tell two number-theory proofs apart. The threshold is not usable, and the next instrument is a semantic feature, which Mathlib constants and defined predicates a statement uses, weighted by rarity across the atlas. Gap EG8.

## 8d. Readers — [reading/](../reading/)

Five guides, one per statement a person is asked to sign: the registrar's Lean statements for arXiv:2608.18608 (EG3), Erdős 569 (EG4) and Erdős 1061, and the two theorems proved as by-products of build 5. Each says what the Lean text claims, what the source says, the points of care, and the one question. The register's agents cannot sign these. A reader files a `read` cycle under their own name.

## What build 8 adds to the record

The forced probe is cheap and decisive on untried rooms: eight forced, seven closed, the one that held is the one no arm could prove. A model's "I cannot" is an estimate until a rule makes it try. The join types are reproducible across two readers at the threshold the gap set, with one boundary left and the coupling type nearly gone under a written test. The hinge vectors retrieve by shape within a proof and need a semantic layer to compare proofs. And the human half of the record is now packaged for a person to pick up.

## Files

[prereg_build_8_retype.yaml](../prereg_build_8_retype.yaml) · [prereg_build_8_forced.yaml](../prereg_build_8_forced.yaml) · [prereg_build_8_match.yaml](../prereg_build_8_match.yaml) · [retype/](../retype/) (untyped blueprints, four reader files) · `results/B8_blindhold_full_forced/`, `results/B8_blindplain_full_forced/` (`calls.tsv`, `attempts/`, `final.lean`, `score.json`, `forced.json`, `work/NOTES.md`), `results/B8_159none_*` (the misnamed first attempts, record only) · `results/match_build8c/` · [atlas/hinges.yaml](../atlas/hinges.yaml) · [reading/](../reading/) · instruments in `rooms/` (`TYPES_V2.md`, `RETYPE_PROMPT.md`, `retype_score.py`, `SEARCHER_FORCED_MULTI_PROMPT.md`, `decl_sorry.py`, `match.py`, `hinges.py`, `check.sh`, `forced_score.py`).
