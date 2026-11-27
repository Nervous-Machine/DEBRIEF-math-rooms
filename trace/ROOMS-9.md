# Rooms and hinges, build 9: the rooms nobody drew, and the standing rerun

**Question written down first.** Heidi Bennett (2026-11-27): how does training flip a hinge, and does a flip leave residuals that point to missing rooms? The atlas held the planner's rooms and their outcomes and nothing about the rooms a searcher created on the way. Registration: [prereg_build_9_discovered.yaml](../prereg_build_9_discovered.yaml), six predictions, one amendment. Beside it, a standing registration for the same arms under each newer model: [prereg_longitudinal.yaml](../prereg_longitudinal.yaml).

**The extractor.** A discovered room is a declaration in an arm's scored final file that is not in its reference structure (the planner's blueprint, or the start file for arms that began from an earlier arm's file). [discovered.py](../rooms/discovered.py) records its statement, whether it was sorry-free at FINAL, the reference rooms that mention it, and, added after the first run showed the mention measure misses the main case, the room it was built for by the tag of the earliest attempt containing it.

## Result

| where the discovered rooms sit | rooms |
|---|---|
| at the two hinges that never closed (569 core at caps 12, 36, 108; 159 core forced) | 128 |
| at hinges that flipped because they needed an idea (Lemma 7; the sparse/dense reduction, twice) | 7 |
| at hinges that flipped because they were slips (two renamed or under-applied lemmas, two bookkeeping rooms) | 0 |
| in the build 6 probe arms, against 48 and 34 planner rooms | 9 and 1 |
| at the room shown false as drawn (N34) | 0 |
| total, all sorry-free at FINAL | 176 |

One room was drawn twice: the sparse-case lemma of build 3's full-feedback arm and `c4_free_indep_sparse` of build 8's blind-hold forced arm match at 1.10, two fresh contexts six builds apart building the same room for the same hinge.

**Predictions.** Held: P3 (every discovered room sorry-free), P4 (one recurrence at or above 0.9), P5 (fewer than a quarter of the blueprint's rooms in the probe arms), P6 (nothing built around the false room). Held in substance by the attempt-tag measure, missed by the registered mention measure: P2 (128 against 7, the direction predicted). Missed: P1 (three of seven closed forced rooms left a room; four predicted).

## What it means

**Flips have signatures, and the record now reads them.** A hinge that flips because it was a slip leaves no trace. A hinge that flips because an idea was found leaves two or three rooms, which are the idea written down as lemmas. A hinge that does not flip leaves rooms in proportion to the budget spent on it, and they are the residual's shape: the 86 rooms of the 108-attempt arm are the dense configuration described from every side it could be approached. That is what "a residual that points to a missing room" looks like in practice, and it was already there in the files, unindexed.

**For the training question.** The three mechanisms by which a hinge can flip, the route entering the distribution, the foundation growing, the generator widening, are now distinguishable by what the rerun arm leaves behind: the paper's own move with no paper, a literature room closing by citation, or new helper structure that is neither. The longitudinal registration fixes eight arms and eight predictions for the first newer model, and the extractor records what each flip creates so that it can be classified.

**The atlas can start to learn.** One recurrence is one data point, but it is the right kind: the same room for the same hinge from independent searchers. The next matcher, with a semantic feature (EG8), should find these across proofs, not only within one.

**What this does not say.** One searcher model. The attribution measure that works was added after the registration and is labelled. Whether a discovered room is useful beyond its arm is a reading nobody has done.

## Files

[prereg_build_9_discovered.yaml](../prereg_build_9_discovered.yaml) · [prereg_longitudinal.yaml](../prereg_longitudinal.yaml) · [atlas/discovered.yaml](../atlas/discovered.yaml) · `results/<ARM>/discovered.yaml` for the fourteen arms · [results/discovered_score_build9.txt](../results/discovered_score_build9.txt) · [rooms/discovered.py](../rooms/discovered.py).
