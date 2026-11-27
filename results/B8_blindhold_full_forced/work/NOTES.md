# B8_blindhold_full_forced — searcher notes

Start 2026-11-27 17:33:37 UTC (first tool call). Working file: Erdos159.lean (this directory).

## Fallback removal
The inherited blind-arm file wrapped 25 proofs as `first | <proof> | sorry` (N01, N02, c4_of_common_nbrs, N03, N04,
greedy_indep_local_aux, N05, card_lt_of_isIndepSet_of_indepSetFree, N06, N07, N08, N09, two_mul_le_of_markov, N10,
filter_card_le_erase_add, phi_le_phi_erase_add, exists_dense_core_aux, N11, N12, N14, N15, N17, N18, N19, erdos_159).
All 25 `| sorry` fallback branches were deleted; the proof branches (and the inner `first | A | B` alternatives, which
have no sorry) were kept. The header comment mentioning the fallbacks was rewritten. N13 and N16 were plain `sorry`.

Whole-file compile after removal (call 1, tagged N01): [error]. Two rooms had only compiled because of the fallback:
- N10 `turan_weak`: `SimpleGraph.sum_degrees_eq_twice_card_edges` used without its explicit graph argument
  (type mismatch: a `∀ G, ...` where `∑ u, G.degree u = ...` was expected).
- N19 `floor_succ_le_power`: `le_or_lt` is not a name in the pinned Mathlib (it is `le_or_gt`).
Everything else (N01–N09, N11, N12, N14, N15, N17, N18, ROOT) compiled without fallback.

## Forced rooms

### N10 `turan_weak` — CLOSED after 1 genuine attempt
- Attempt 1 (call 2): repaired the one broken step, `SimpleGraph.sum_degrees_eq_twice_card_edges G`. Lean: no
  errors; [sorry] only from N13 and N16. Room closed.

### N19 `floor_succ_le_power` — CLOSED after 1 genuine attempt
- Attempt 1 (call 3): `le_or_lt 0 x` → `le_or_gt 0 x`. Lean: no errors; [sorry] only from N13 and N16. Room closed.

### N16 `c4_free_indep_power` — CLOSED after 1 genuine attempt (rests on N13, as the rule allows)
- Attempt 1 (call 4): proof from the blueprint's join: two helper lemmas plus the join.
  * `c4_free_indep_sparse` (sparse branch): N10 gives an independent t with N² ≤ 2(4E+N)|t| in ℕ; cast to ℝ and
    feed N14 (`sparse_branch_arith`) to get N^(1/2+δ) ≤ 10|t|.
  * `c4_free_indep_dense` (dense branch, hypothesis N^(3/2-δ) < E): x := N^(1/2-δ) ≥ 1, d := ⌊x⌋₊, so 1 ≤ d,
    x/2 ≤ d ≤ x and d·N ≤ x·N = N^(3/2-δ) ≤ E (`Real.rpow_add_one`); N11 (`exists_dense_core`, Nonempty (Fin N) from
    N ≥ 1) gives a core s with min internal degree ≥ d; N12 (`moore_bound_c4_free`) gives d² ≤ 2|s|, hence
    N^(1-2δ) = x² ≤ 4d² ≤ 8|s| (`Real.rpow_mul`, `Real.rpow_two`, nlinarith); |s| ≤ N gives |s|^(1/2-δ) ≤ x ≤ 2d, so
    the N13 hypothesis holds with κ = 1/2; N13 (as a hypothesis h13 of the helper) gives t ⊆ s independent with
    K'|s|^(1/2+η) ≤ |t|; N15 (`dense_branch_arith`) turns this into K'·8^(-(1/2+η))·N^(1/2+η/2) ≤ |t|.
  * Join: obtain δ, η, h13 from `core_near_extremal`; K' from h13 at κ = 1/2; ε := δ,
    K := min (1/10) (K'·8^(-(1/2+η))). N = 0: t = ∅ and 0^(1/2+δ) = 0. N ≥ 1: split on E ≤ N^(3/2-δ); sparse branch
    uses K ≤ 1/10; dense branch uses K ≤ K'·8^(..) and N^(1/2+δ) ≤ N^(1/2+η/2) (δ ≤ η/2 since 4δ ≤ η, N ≥ 1).
  Lean: no errors; [sorry] only from N13 (line 573). Room closed.

## N13 `core_near_extremal`
Left as `sorry`, untouched, as the brief directs. This is the open core; the whole problem sits in it.

## Do I believe each forced room is true as drawn?
- N10: yes; it is a Caro–Wei/Turán-type bound proved by Markov on degrees plus the greedy lemma N05, and it compiled.
- N19: yes; elementary floor arithmetic, and it compiled.
- N16: true *conditionally on N13*; the reduction N13 → N16 is now machine-checked. Whether N16 is true
  unconditionally is exactly the open question (polynomially-above-√N independence number for C4-free graphs).

## Things I was tempted to change and did not
- Nothing in any statement was changed; N13 was not touched. I did not add hypotheses or weaken any room.
- I considered proving the dense branch with κ = 1 instead of 1/2 (would need ⌈·⌉ or N large); κ = 1/2 avoids a
  "for N large enough" case split, so no statement needed adjusting.

## Call log (check.sh)
1. N01 whole-file compile after fallback removal: [error] (N10 hsum type mismatch; N19 `le_or_lt` unknown).
2. N10 genuine attempt 1: [sorry] (only N13, N16 open) — N10 closed.
3. N19 genuine attempt 1: [sorry] (only N13, N16 open) — N19 closed.
4. N16 genuine attempt 1: [sorry] (only N13 open) — N16 closed.
5. FINAL: see below.
5. FINAL (call 5, 17:40 UTC): accepted and compiled; [sorry] with the single `declaration uses sorry` at N13
   `core_near_extremal` (line 573). No errors. N10, N16, N19 closed (N16 via N13). 5 check.sh calls, 0 refusals,
   1 [error] (the pre-forced whole-file compile).

End 2026-11-27 17:41 UTC. Tools used: Bash (date, cat, grep, sed, python3 for in-place edits, check.sh), Read.
