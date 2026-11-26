# NOTES — build 3, arm B3_159_H_full_hold (full Lean feedback, planner's blueprint, hold-position rule)

Searcher start (first tool call): 2026-11-26 01:31:34 UTC. FINAL called 2026-11-26 01:54:29 UTC, returned `[sorry]`.
Working file: `Erdos159.lean` (one file; header, `graphRamsey` and the `erdos_159` statement copied verbatim from
`rooms/Challenge_159.lean`; all 19 nodes carry the blueprint statements verbatim, checked by a whitespace-normalised
text comparison against `blueprint_159_nodes.yaml`). No `native_decide`, `admit`, `axiom`, `unsafe` or `maxHeartbeats`.
Plain kernel `decide` is used twice, on finite statements about `Fin 4`.

## Result in one line

Everything except N13 is proved. N13 (`core_near_extremal`) is left as `sorry`. N16, N18 and the ROOT are proved
*from* N13, so the file compiles with `[sorry]` and the root `erdos_159` is reduced to N13 and nothing else.

## Rooms

| room | name | status | note |
|---|---|---|---|
| N01 | graphRamsey_le_of_forall | proved | `Nat.sInf_le` after unfolding `graphRamsey` |
| N02 | complete_isContained_compl_iff | proved | `not_cliqueFree_iff_top_isContained` + `cliqueFree_compl` |
| N03 | c4_free_common_nbrs | proved | explicit `Copy (cycleGraph 4) G` from `![u, a, v, b]`; adjacency of `cycleGraph 4` enumerated by `decide` |
| N04 | c4_free_nbhd_local_degree | proved | subset of the common neighbourhood, N03 |
| N05 | greedy_indep_local | proved | strong induction on `s`, removing a vertex and its ≤ D neighbours |
| N06 | degree_lt_of_c4_free_indepSetFree | proved | N04 + N05 with D = 1 on the neighbourhood |
| N07 | card_le_quadratic_of_c4_free | proved | N05 on `univ` with D = 2n − 1, N06 |
| N08 | graphRamsey_le_of_c4_free_bound | proved | N01 + N02 |
| N09 | graphRamsey_c4_le_quadratic | proved | N07 + N08: R(C4, K_n) ≤ 2n² + 1 (exponent 2; not the target) |
| N10 | turan_weak | proved | low-degree vertices (deg ≤ 4m/n) are ≥ n/2 of all vertices (Markov); N05 on them |
| N11 | exists_dense_core | proved | helper `dense_core_aux`: peel a vertex of internal degree < d; the internal degree sum drops by ≤ 2(d−1) |
| N12 | moore_bound_c4_free | proved | second neighbourhoods of the neighbours of v (minus v) are pairwise disjoint by N03; `card_biUnion` |
| N13 | core_near_extremal | **sorry** | the open core, see below |
| N14 | sparse_branch_arith | proved | `N² = N^(1/2+δ) · N^(3/2−δ)` and `4E + N ≤ 5 N^(3/2−δ)` |
| N15 | dense_branch_arith | proved | exponent inequality `(1−2δ)(1/2+η) ≥ 1/2 + η/2` from `δ ≤ 1/8`, `4δ ≤ η` |
| N16 | c4_free_indep_power | proved modulo N13 | `ε := δ`, `K := min (1/256) (K₁ · 8^(−(1/2+η)))`; cases N = 0, 1 ≤ N < 256 (one vertex), N ≥ 256 split on `E ≤ N^(3/2−δ)` (N10+N14) / dense (`d := ⌊N^(1/2−δ)⌋₊`, N11, N12, N13 with κ = 1/2, N15) |
| N17 | rpow_inversion | proved | raise to the power `2/(1+2ε)`; `2 − 4ε/(1+2ε) = 2/(1+2ε)` |
| N18 | card_le_power_of_c4_free | proved modulo N13 | `c := 4ε/(1+2ε)`, `C := K^(−2/(1+2ε))`; N16 + N17 |
| N19 | floor_succ_le_power | proved | `Nat.floor_le` / `Nat.floor_of_nonpos`, `one_le_rpow` |
| ROOT | erdos_159 | proved modulo N13 | `N := ⌊C n^(2−c)⌋₊ + 1` in N08, contradiction with N18, then N19 with constant `C + 1` |

Helper lemmas added (all proved): `cycleGraph_four_adj_cases`, `c4Copy`, `card_lt_of_indepSetFree`,
`indepSetFree_pos`, `filter_univ_adj_eq`, `card_filter_adj_le_degree`, `sum_filter_adj_erase_le`, `dense_core_aux`,
`sparse_case`, `dense_case`.

## Rooms left open and why

**N13 only.** As drawn, N13 asserts the existence of exponents δ, η (0 < δ ≤ 1/8, 4δ ≤ η) such that every C4-free
graph, on any finset `s` of minimum internal degree ≥ κ|s|^(1/2−δ), has an independent subset of size
≥ K|s|^(1/2+η). I did not attempt a proof: this is the open problem itself, and the brief forbids reshaping it.

The file makes the equivalence precise in one direction: N13 ⟹ ROOT (N16, N18, ROOT are proved from N13). The
other direction is also true, informally: if R(C4, K_n) ≤ C n^(2−c), then every C4-free graph on N vertices has
an independent set of size ≥ (N/C)^(1/(2−c)) = Ω(N^(1/2+c')) with c' > 0; applying this to the induced subgraph on
`s` (still C4-free, degree hypothesis unused) gives N13 with η := c' and δ := min(1/8, c'/4). So N13 is exactly
Erdős 159 in different clothing, not a lemma on the way to it. Nothing in the planner's blueprint reduces its
difficulty, and I know of no honest route to it from Mathlib at the pinned commit.

## Rooms I believe are false as drawn

None. All eighteen other rooms are proved as stated. N13 is not known to be false (that would refute the conjecture).

## What would close the root

A proof of N13 — equivalently a polynomial improvement over √N for the independence number of C4-free graphs
(on near-extremal cores or in general). The quadratic bound N09 (R(C4, K_n) ≤ 2n² + 1) is proved but has exponent 2,
so it gives no `c > 0`; I did not present it as the result.

## Checks

`check.sh` calls: 5 in total (4 node checks + FINAL). Node checks: 0001 N03 → sorry (N01–N09 all compiled first
time; the only `sorry` was the untouched root); 0002 N10 → error (two small errors: an `a ≤ a + 0` goal left after
`rw`, and `le_or_lt` no longer exists → `le_or_gt`); 0003 N16 → error (one `positivity` call needing `δ ≤ 1/8`);
0004 N16 → sorry (only N13 open). Each compile took 2–5 s.

## Tools used

Bash (date, cat, grep, sed, head/tail, python3 for splicing and the statement comparison, and `sh rooms/check.sh`
as the only way to run Lean), Read (the brief). No web access, no git, no other Lean invocation; nothing read under
DEBRIEF-math-rooms other than the five permitted inputs and this work directory. Mathlib source was grepped and
read for lemma names only.
