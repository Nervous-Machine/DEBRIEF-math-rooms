# NOTES — B3_159_H_none_plain (searcher, no checker until FINAL)

Written blind: the whole file was composed without compiling; the first FINAL call is the first compile.

## Nodes I believe are proved (in blueprint order)
- N01 graphRamsey_le_of_forall — `Nat.sInf_le`.
- N02 complete_isContained_compl_iff — `not_cliqueFree_iff_top_isContained` + `cliqueFree_compl`.
- N03 c4_free_common_nbrs — two common neighbours a ≠ b of u ≠ v give the 4-cycle u-a-v-b-u, built as an explicit
  `Walk` and fed to `cycleGraph_isContained_iff`; `cons_isCycle_iff`/`cons_isPath_iff` + simp on the disequalities.
- N04 c4_free_nbhd_local_degree — filter ⊆ intersection of neighbourhoods, then N03.
- N05 greedy_indep_local — `Finset.strongInduction`: remove a vertex and its ≤ D neighbours inside `s`, recurse.
- N06 degree_lt_of_c4_free_indepSetFree — N04 + N05 with D = 1 on the neighbourhood; an independent set of size ≥ n
  would contain an n-independent set (`exists_subset_card_eq`).
- N07 card_le_quadratic_of_c4_free — N05 on `univ` with D = 2n (via N06), then |t| < n and nlinarith.
- N08 graphRamsey_le_of_c4_free_bound — N01 + N02 + `or_iff_not_imp_left`.
- N09 graphRamsey_c4_le_quadratic — N07 + N08 (classical decidability).
- N10 turan_weak — threshold D = ⌊4e/m⌋; low-degree vertices are more than half; N05 on them; the arithmetic is the
  added helper `turan_arith`.
- N11 exists_dense_core — invariant 2d|s| ≤ Σ_{v∈s} |N_s(v)|; removing a vertex of internal degree k < d loses ≤ 2k
  (lemma `hrem`, proved with `add_sum_erase`, `sum_add_distrib`, `card_filter`); strong induction on `s`, started
  at `univ` with the degree-sum formula (helper `card_filter_univ_adj`).
- N12 moore_bound_c4_free — for v ∈ s the sets N_s(w) \ {v}, w ∈ N_s(v), are pairwise disjoint by N03, so
  |N_s(v)|·(d−1) ≤ |s| via `card_biUnion`; then d·d ≤ 2|s|.
- N14 sparse_branch_arith, N15 dense_branch_arith, N17 rpow_inversion, N19 floor_succ_le_power — real-power
  arithmetic with `Real.rpow_*`, nlinarith/linarith.

## Helper lemmas added (not in the blueprint)
- `card_filter_univ_adj` : `(univ.filter (G.Adj v)).card = G.degree v`.
- `turan_arith` : the pure ℕ arithmetic behind N10.

## Statements changed
None. Every node statement and the root statement are copied verbatim from the blueprint / the Challenge file.

## Not finished
- N13 core_near_extremal — the planner's open core. It asserts that near-extremal C4-free pieces have independence
  number polynomially above √|s|; this is the content of the open problem itself and I have no proof. Left `sorry`.
- N16 c4_free_indep_power, N18 card_le_power_of_c4_free — depend on N13; left `sorry`.
- ROOT erdos_159 — an OPEN problem (research open in formal-conjectures). It cannot be proved honestly from what is
  known; left exactly as in the Challenge, with `sorry`. The provable fit N09 (R(C4,K_n) ≤ 2n²+1) is proved but does
  not give c > 0 and is not presented as the result.

So the expected best outcome of FINAL is status `sorry` (compiles, with the four open declarations using sorry).

## FINAL calls (added after the fact)
- FINAL #1 (02:06:47 UTC, scored): `error`. Exactly one error, in N19 `floor_succ_le_power`: `le_or_lt` is no longer a
  Mathlib name at this commit (renamed `le_or_gt`), so the `rcases` failed. Every other declaration compiled: N01–N12,
  N14, N15, N17 and the two helpers were accepted; N13, N16, N18 and the root reported `declaration uses sorry` as
  intended. Only warnings otherwise (unused simp args / unreachable fallback tactics / deprecated `if_pos`,
  `if_neg`, `push_neg` names).
- FINAL #2 (02:07:11 UTC, not scored): after the one-token repair `le_or_lt` → `le_or_gt`, the file compiles with
  status `sorry`; the only sorries are N13, N16, N18 and the root, i.e. the open core and what inherits it.
