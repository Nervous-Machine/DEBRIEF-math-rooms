# Searcher notes, arm B4_569_F_full_forced, forced room N32 (`lemma7`)

Start 2026-11-26 18:10:07 UTC. First N32 check 18:23:50 UTC.

## Attempts at N32

1. Route: `by_contra`, then `claim8` (N30: `u i = u (k-4+i)` for `i ≤ 4`) and `claim9` (N31: `u i ≠ u (i+2)`
   for `i ≤ 2`), then a case split on which of `u 0, u 1, u 2, u 3, u 4` coincide, each case closed by an
   explicit `k`-cycle built with `cycle_of_closed_seq` (N12) through two new helper lemmas placed before
   `lemma7`:
   - `lemma7_cycle_v`: cycle `v, u a, w a … w b, u b (= u p), w p … w q, u q, v` with `q < a < b ≤ k`,
     `k = (b-a) + (q-p) + 6`, and `u a, u b, u q` pairwise distinct;
   - `lemma7_cycle_two`: cycle `u a, w a … w b, u b (= u p), w p … w q` closing through `u q = u a`, with
     `a < b < p < q ≤ k`, `k = (b-a) + (q-p) + 4`, `u a ≠ u b`.
   Cases (d = k - 4, x_i = u i; claim8 makes `u` d-periodic on 0..k, claim9 gives x0≠x2, x1≠x3, x2≠x4):
   - k = 7: `lemma7_cycle_two` with (a,b,p,q) = (0,1,4,6).
   - k ≥ 8, x4 ≠ x0 (forces k ≥ 9): `lemma7_cycle_v` (4, k-4, 0, 2).
   - x4 = x0, x1 = x4, x2 = x3: `lemma7_cycle_two` (0, 2, 3, k-3).
   - x4 = x0, x1 = x4, x2 ≠ x3: `lemma7_cycle_v` (3, k-4, 1, 2).
   - x4 = x0, x1 ≠ x4, x1 = x2, x3 = x0: `lemma7_cycle_two` (3, k-3, k-2, k).
   - x4 = x0, x1 ≠ x4, x1 = x2, x3 ≠ x0: `lemma7_cycle_v` (3, k-4, 0, 1).
   - x4 = x0, x1 ≠ x4, x1 ≠ x2: `lemma7_cycle_v` (4, k-3, 1, 2).
   Lean said: compiles, `[sorry]` (the nine literature rooms only); no error anywhere in the file.

## Belief

The room is true as drawn: the case analysis above is exhaustive and each case yields a `C_k`, and Lean
accepted it. Nothing further is needed to close it.

## Temptations not acted on

None that would have changed a statement. I considered reducing the nine-way `first | …` closer in the
injectivity proofs to explicit cases but left it since Lean accepted it; no statement of any room, of
`lemma7`, or of the target was touched, and the only additions are the two helper lemmas before `lemma7`.
