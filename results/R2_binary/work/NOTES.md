# Searcher notes, regime R2_binary (Erdős 766, Dirac–Erdős bound)

File: `Rooms766.lean` (one file, begins exactly as `rooms/Challenge.lean`; lemmas inside `namespace Erdos766` after `forcingNumber`; root statement verbatim at the end).

## Nodes

All sixteen nodes (N1–N15, ROOT) are proved with their blueprint statements unchanged. No node statement was altered.

| Node | Status | Notes |
|---|---|---|
| N1 `two_mul_sq_div_four_succ_lt` | proved | parity split, `nlinarith`; not actually used downstream |
| N2 `sq_div_four_eq_pred_sq_div_four_add_half` | proved | parity split; not actually used downstream |
| N3 `low_degree_arith` | proved | parity split with `m = a + 2`; the planner's route via N1 does not close (iterating `N·d ≥ N(⌊N/2⌋+1) > 2(⌊N²/4⌋+1)` only gives `e > ⌊N²/4⌋+1`); instead: suppose `e ≤ d + ⌊(N−1)²/4⌋`, then `d ≥ ⌊N/2⌋+1` and `(N−2)·d ≤ 2⌊(N−1)²/4⌋`, contradiction for `N ≥ 4` via `Nat.mul_le_mul_left` + `nlinarith` |
| N4 `exists_card_mul_degree_le` | proved | min-degree vertex, `Finset.sum_le_sum`, degree-sum formula |
| N5 `exists_low_degree_vertex` | proved | N4 + N3 |
| N6 `card_edgeFinset_induce_compl_singleton_eq` | proved | the two Mathlib lemmas the planner named |
| N7 `card_compl_singleton_subtype` | proved | `Fintype.card_compl_set`, `Set.card_singleton` |
| N8 `exists_vertex_delete_keeps_dense` | proved | N5 + N6 + `omega` |
| N9 `induce_isContained` | proved | `⟨SimpleGraph.Copy.induce G s⟩` |
| N10 `ncard_edgeSet_eq_card_edgeFinset` | proved | `Set.ncard_eq_toFinset_card'` |
| N11 `exists_fin_copy` | proved | `overFin`/`overFinIso`; edge count transferred with `Nat.card_congr (overFinIso).mapEdgeSet.symm` (no decidability on `overFin` needed) |
| N12 `exists_dense_fin_subgraph` | proved | plain `induction N` (not `Nat.le_induction`); case `N+1 = k` uses N11, case `k ≤ N` uses N8, N7, IH on `{x}ᶜ`, N9 |
| N13 `exists_le_ncard_edgeSet_eq` | proved | `Set.exists_subset_card_eq`, `fromEdgeSet`; `[Finite W]` is not needed by the proof but kept as stated |
| N14 `dirac_erdos_exists` | proved | `Classical.decRel`, N10, N12, N13, `IsContained.mono_left` |
| N15 `forcingNumber_le_of_forall` | proved | `unfold forcingNumber; exact Nat.sInf_le h` |
| ROOT `erdos_766.variants.dirac_erdos` | proved | N15 applied to N14 |

Helper lemmas added (not in the blueprint): `sq_two_mul_div_four`, `sq_two_mul_add_one_div_four`.

## Process

Regime R2_binary: one word per whole-file compile. I added one node per check, in blueprint order, so an `error` would have been attributable to the newest node. Every check returned `ok`; no node needed a second attempt. Where a step had several plausible Mathlib spellings (N4, N7, N10, N11, N14, N15) I wrote `first | … | …` alternatives rather than spend checks.

Checks: 16 node checks (N1 covered N1+N2 together since both were written before the first check, N3 … N15, ROOT) + 1 FINAL = 17 calls. No forbidden tokens (`sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `maxHeartbeats`) in the file; the Challenge header, definitions and root statement are copied verbatim.

Hard rules kept: no web, no git, no other Lean invocation, no other `results/` directories read, no existing proof of the theorem consulted.
