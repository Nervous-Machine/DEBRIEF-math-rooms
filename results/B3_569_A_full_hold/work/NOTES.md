# NOTES — arm B3_569_A_full_hold (full Lean feedback, planner blueprint, hold-position rule)

Searcher start 2026-11-26 01:37 UTC. File: `Erdos569.lean` (one file, nodes N01–N59 in blueprint order inside
`namespace Erdos569`, then the root theorem copied verbatim from `Challenge_569.lean`).

## Result in one line

48 of the 59 rooms are fully proved (sorry-free bodies); the root `cambie_freschi` and the main join `main_property`
are proved *modulo* the rooms left open. 11 rooms are left as their blueprint statement with `sorry`:
10 literature rooms and one paper step (Lemma 7, N32). The file compiles with status `sorry`, no errors.

## Rooms proved (48)

N01 N02 N03 N04 N05 N06 N07 N08 N09 N10 N11 N12 N13 N15 N17 N18 N19 N20 N21 N29 N30 N31 N33 N34 N35 N36 N37 N38 N39
N40 N41 N42 N43 N44 N45 N46 N47 N48 N49 N50 N51 N52 N53 N54 N55 N56 N57 N58 N59 and ROOT.

(N15, N29, N33, N54, N57, N58, N59, ROOT are proved from their dependencies, some of which are open; their own
bodies contain no `sorry`.)

## Rooms left open (11), grouped

### Literature rooms (10) — statements kept, body `sorry`
- N14 `goddard_kleitman_sidorenko` (R(K3,H) ≤ 2m+1 for H without isolated vertices). Planner: likely_false.
  My recollection is that this is a true theorem (Sidorenko 1993; Goddard–Kleitman for connected H), but it has
  no short proof and is far beyond what fits in this build. Not attempted.
- N16 `haggkvist` (R(P_k, K_{a,b}) ≤ a+b+k-2). Planner: unsure. Not attempted; I have no independent view on the
  exact bound as drawn.
- N22 `jayawardene_C4`, N23 `jayawardene_C5`, N24 `jayawardene_C6`. Planner: likely_false. Not attempted; I cannot
  judge the exact constants as drawn.
- N25 `ramsey_C5_K3` (R(C5,K3) ≤ 9), N26 `ramsey_C6_K3` (R(C6,K3) ≤ 11): I believe both true (known small Ramsey
  numbers), but a Lean proof needs a real extremal argument over all graphs on 9/11 vertices; not attempted.
- N27 `ramsey_C6_K4` (≤ 16), N28 `ramsey_C6_K5` (≤ 21). Planner: likely_false. Not attempted.

### Paper step I ran out of a route for (1)
- N32 `lemma7`. Claims 8 and 9 (N30, N31) are proved exactly as drawn (both are correct: the C_k witnesses are
  v–u_i–w_i…w_{i+k−4}–u_{i+k−4}–v and u_i–w_i…w_{i+k−2}–u_i). But claim 8 + claim 9 alone do not give the
  k-cycle demanded by N32 for general k ≥ 7: the only further cycles available from the five forced hub
  coincidences u_i = u_{i+k−4} (i ≤ 4) and the three forced non-coincidences have lengths that depend on which
  other hubs coincide (e.g. v–u_0–w_0…w_b–u_b–w_{b+k−4}…w_{2b−a+2}–u_{2b−a+2}–v has length k but needs three
  distinct hubs). Finishing it is a many-case analysis on hub coincidences that I could not complete and
  formalise in the budget. I believe the statement is true as drawn; I could not reconstruct the paper's proof.
  N33 (`lemma7_bridge`) is proved from N32.

### Rooms I believe false as drawn
None found. Every room I worked on was provable as stated.

## Statement-level notes (honesty log)
- N38 `sum_induced_edges_powersetCard`: the statement as drawn does **not elaborate** in Lean
  (`∑ T ∈ Finset.univ.powersetCard s, (H.induce (T : Set W)).edgeSet.ncard` — the type of `T` is unknown when
  `(T : Set W)` is elaborated, error "Type mismatch: T has type Finset ?m but is expected to have type Set W").
  I added the type ascription `(Finset.univ : Finset W).powersetCard s`. This is the only change to any room
  statement; it fixes elaboration and does not change the mathematical content. The room is then fully proved.
- A helper `glue_components_aux` (the exact content of N41) is placed before N40, because N40
  (`ramsey_with_isolated`) is naturally proved by gluing (isolated vertices = the complement of the support) and the
  blueprint orders N40 before N41. N41 is then `exact glue_components_aux …`. Helper lemmas are allowed by the brief.
- Unused-hypothesis warnings: N40 and N50 do not use `hk`; harmless.
- Deprecation warnings (`push_neg`, `if_pos`, `dif_pos`, `Set.mem_setOf_eq`) left as is; they are warnings only.
- Several rooms were quantified without `DecidableRel`; proofs use `classical`.

## What would close the root
The root is proved from N59, which is proved from N09, N11, N14, N29, N45, N58. Everything on the paper's own route
is closed except N32 (which only feeds N54 → N57 → N58). Closing the root sorry-free needs:
N14 (Goddard–Kleitman–Sidorenko), the four Jayawardene/small-Ramsey inputs to N29 that are actually used
(N22, N23, N24, N25, N26, N27, N28 — all seven are used in the case split of N29), and N32. N16 only feeds N17 → N18
→ N20 → N21/N54, so it is also needed.

## Checks
check.sh calls: 18 in total (17 before FINAL, then FINAL). Status by call: 13 error, 4 sorry (compiled with rooms
open), FINAL = sorry (compiles, no errors; 10 declarations use sorry, all listed above). Nodes with the most calls:
N01 (2), N40 (2); every other node 1. FINAL called 2026-11-26 02:24 UTC, ~47 minutes after start. See `calls.tsv`.
