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

# Build 9b: the atlas as a graph, and the rooms graph in CVOT

**Question written down first.** Heidi Bennett (2026-11-27): rooms point to neighbourhoods, nodes are the local samples, edges are the conditionals; the route drives through neighbourhoods and builds bridges across them, and a bridge might not have direct access. The computable version: a hinge whose hypothesis side and conclusion side have no single existing room close to both. Prediction staked: the two hinges that never closed are exactly those bridges. Registration: [prereg_build_9_graph.yaml](../prereg_build_9_graph.yaml), five predictions, one amendment.

**The graph.** [atlas_graph.py](../rooms/atlas_graph.py) puts the 182 planner rooms and 176 discovered rooms in one graph, with dependency edges from the blueprints and the discovered rooms, and neighbourhood edges where two statement shapes match at 0.45 or above.

| | |
|---|---|
| rooms | 358 (182 planner, 176 discovered) |
| dependency edges | 422 |
| neighbourhood edges at 0.45 | 1990 |
| components | 80 |

| hinge | outcome | access | shores | neighbours | discovered rooms adjacent |
|---|---|---|---|---|---|
| 569 core (`core_ge_three_nonstar`) | open | 0.500 | same | 30 | 123 |
| 159 core (`core_near_extremal`) | open | 0.000 | split | 0 | 5 |
| Lemma 7 | closed when forced | 0.480 | same | 27 | 4 |
| `floor_succ_le_power` (a slip) | closed when forced | 0.367 | same | 10 | 0 |
| `turan_weak` (a slip) | closed when forced | 0.000 | split | 0 | 8 |
| `c4_free_indep_power` | closed when forced | 0.000 | split | 0 | 14 |

**Predictions.** Held: P5 (the graph went into CVOT whole). Half held: P3 (both unclosed hinges have at least five discovered rooms beside them; the slip `turan_weak` has eight, not zero). Missed: P1 and P2 (access and shores do not separate the hinges that never closed from those that closed when forced), P4 (one neighbourhood component spans all four proofs).

## What it means

**The measure did not see the bridges, and the reason is in the statements.** Every hinge that reads access 0 has nothing on its hypothesis side: its hypotheses are written inside the conclusion, as in "there exist constants such that for every graph", or only as implicit binders. The shape matcher splits a statement at its colon, so it compares nothing on that side, and the hinge looks isolated whether it closed or not. Among hinges with a readable hypothesis side, access does not separate open from closed either. Testing Heidi's picture needs a matcher that reads hypotheses out of quantified conclusions and knows which constants a statement is about. That joins the open matcher gap ([EG8](../ASKS.md)).

**The dependency side carries a signal, but not a clean one.** The 569 core has 123 rooms built against it, far above any hinge that flipped. The 159 core has 5, inside the flips' range.

**The rooms graph is in the shared store.** 358 nodes and 412 edges are in CVOT under pod `DEBRIEF-math-rooms`, visible to the pod. Each node carries its statement's opening, its outcome and its type. Each edge is a dependency, a "serves" mention or a "built for" attempt. A dependency into a room that closed is seeded at 1.0. Everything else is seeded at 0.5, including every room a searcher built against an open hinge, so the kernel can earn or lose that weight as more arms arrive. The ten edges from the blind arms that point at the file's final check, which is not a room, were left out.

## Files

[prereg_build_9_graph.yaml](../prereg_build_9_graph.yaml) · [rooms/atlas_graph.py](../rooms/atlas_graph.py) · [results/atlas_graph_build9.txt](../results/atlas_graph_build9.txt) · [results/atlas_graph_build9.json](../results/atlas_graph_build9.json) · [results/cvot_write_build9.txt](../results/cvot_write_build9.txt) · [results/cvot_written_nodes_build9.json](../results/cvot_written_nodes_build9.json) · [results/cvot_written_edges_build9.json](../results/cvot_written_edges_build9.json).
