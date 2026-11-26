# NOTES — arm B3_159_H_none_hold (searcher, no checker until FINAL, hold-position rule)

Start 2026-11-26 01:31 UTC. File written blind (no compilation) from the planner's blueprint, Mathlib
source at the pinned commit (grep/read only), and nothing else. Preliminary notes written before the
single FINAL call; the section "FINAL result" is filled in after it.

## Method, stated plainly
Every room's statement is the planner's statement verbatim; the root is the Challenge statement verbatim.
Because this arm has no checker, every proof is wrapped as `first | (proof) | sorry`: if a written proof
fails to elaborate, Lean silently falls back to `sorry` for that room instead of producing an error that
would break the file. This does not change any statement; it only turns "my blind proof had a bug" into
"room left open". Which rooms are actually closed is read off Lean's `declaration uses 'sorry'` lines at
FINAL, not off my belief. N13 and N16 are written as plain `sorry` (no proof attempted).

## Rooms: what was attempted
- N01 graphRamsey_le_of_forall — proof written (Nat.sInf_le).
- N02 complete_isContained_compl_iff — proof written (not_cliqueFree_iff_top_isContained, cliqueFree_compl).
- N03 c4_free_common_nbrs — proof written via helper `c4_of_common_nbrs` (explicit injective hom Fin 4 → V,
  adjacency and injectivity by `decide` on Fin 4 followed by case analysis).
- N04 c4_free_nbhd_local_degree — proof written from N03.
- N05 greedy_indep_local — proof written via `greedy_indep_local_aux` (induction on a card bound;
  remove a vertex and its neighbours, recurse).
- N06 degree_lt_of_c4_free_indepSetFree — proof written from N04, N05 and helper
  `card_lt_of_isIndepSet_of_indepSetFree`.
- N07 card_le_quadratic_of_c4_free — proof written from N05, N06.
- N08 graphRamsey_le_of_c4_free_bound — proof written from N01, N02.
- N09 graphRamsey_c4_le_quadratic — proof written from N07, N08.  (This is the exponent-2 bound; it is NOT
  the target and is not presented as such.)
- N10 turan_weak — proof written (Markov on degrees, then N05 on the low-degree half).
- N11 exists_dense_core — proof written via helpers `filter_card_le_erase_add`, `phi_le_phi_erase_add`,
  `exists_dense_core_aux` (delete a low-degree vertex; the internal degree sum drops by at most 2·deg).
- N12 moore_bound_c4_free — proof written (neighbourhoods of the neighbours of v, minus v, are pairwise
  disjoint by N03's helper; Finset.card_biUnion).
- N13 core_near_extremal — LEFT OPEN (`sorry`), no attempt. This is the open core: it asserts that a
  C4-free graph whose core has min degree ≥ κ|s|^(1/2−δ) has an independent set of size |s|^(1/2+η) with
  η ≥ 4δ. I cannot prove it and I do not know whether it is true; it is the whole problem.
- N14 sparse_branch_arith — proof written (rpow algebra).
- N15 dense_branch_arith — proof written (rpow algebra; the exponent inequality
  1/2+η/2 ≤ (1−2δ)(1/2+η) uses δ ≤ 1/8 and η ≥ 4δ).
- N16 c4_free_indep_power — LEFT OPEN (`sorry`), no attempt. It is the join over N10–N15 and inherits
  N13; with N13 open, writing the (long, floor-heavy) reduction blind would add no closed room.
- N17 rpow_inversion — proof written (rpow algebra).
- N18 card_le_power_of_c4_free — reduction written from N16 and N17 (so it is `sorry`-dependent through N16).
- N19 floor_succ_le_power — proof written.
- ROOT erdos_159 — reduction written from N08, N18, N19 (so it is `sorry`-dependent through N18 → N16 → N13).

## Rooms I believe are false as drawn
None found. N13 is "unsure" in the planner's sense: it is a form of the open problem, not something I can
call false.

## What would close the root
A proof of N13 (or any replacement for it that gives N16: every C4-free graph on N vertices has an
independent set of size ≫ N^(1/2+ε)). Everything else in the blueprint is standard and is written here.

## FINAL result
(to be filled in after the FINAL call)
