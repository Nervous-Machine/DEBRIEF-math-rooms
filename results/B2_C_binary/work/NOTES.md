# Searcher notes, build 2, arm B2_C_binary (one-word feedback, with blueprint)

Start 2026-11-25 23:25:11 UTC (first tool call). Full file returned `ok` under node label ROOT at 00:05:28 UTC
(about 40 minutes in). FINAL called immediately after writing these notes.

## Nodes

All 38 blueprint nodes (N01-N37, ROOT) are in the file, in blueprint order, with their statements copied
verbatim from `blueprint_2608_nodes.yaml`. No node statement was changed. The target theorem's header,
docstring and statement are copied verbatim from `rooms/Challenge_2608.lean` (checked by diff).

I believe every node is proved: the whole file compiled (`ok`) with the target theorem and no `sorry`.

## Helper lemmas added (not in the blueprint)

- `prime_not_dvd_both` (before N02): a prime cannot divide both members of a coprime pair. Used in N04, N05, N20.
- `lte_aux`, `val_two_mul` (N02 split in two): the LTE application `padicValNat.pow_sub_pow` and
  `padicValNat p (2p) = 1`. My first one-block proof of N02 failed (binary feedback, so I bisected by
  splitting it); the two halves each passed and N02 is their composition.
- `two_mul_le_sq_add_sq`, `amgm_pair_aux` (N26): `2uv <= u^2 + v^2` in ℕ by cases, and the `i <= b` half of
  the AM-GM pair; N26 itself reduces the `i >= b` half to it by symmetry.
- `bound6_aux` (N28): the cancellation step `(2b+1)(2M+1)^b <= M^b * M  ->  (2b+1) 2^b < M`.
- `choose_succ_two`, `choose_succ_three` (N30): `C(n+1,2) = C(n,2)+n`, `C(n+1,3) = C(n,3)+C(n,2)`.
- `choose_two_odd` (N31): `C(2b+1,2) = b(2b+1)`.

## Remarks on the mathematics as planned

- N14 (Prop 2.5): the LTE argument alone gives `v_p(2b+1) = b`, which does not exclude `b = 1, p = 3`
  (`v_3(3) = 1`); that case is closed by direct evaluation (`7^3 = 343 != 19`). N13 is used for `b >= 2`.
- N20 (Lemma 2.7): the hypotheses do not include `rs = 2p+1`, but the ModEq argument handles the prime 2
  uniformly (`k | S  <->  k | (2b+1) r^(2b)` for every prime `k | s-r`), so no parity argument was needed.
- N33: instead of `Int.ModEq` I used `Odd.add_dvd_pow_add_pow` to get `2k^2 | (2k^2-1)^(b+1) + 1` for
  `b+1` odd, then `linear_combination` to get `2k^2 | 4`, contradicting `k >= 2`.
- N37: the case `b = 0` (where the geometric sum is 1, so `S >= 3` fails) is handled first via N21;
  for `b >= 1` the sum is at least its `i = 0` term `s^(2b) >= s >= 4`.

## Check calls (from my own transcript; I did not read calls.tsv)

49 check.sh calls before FINAL, 15 returned `error`. Of those 15, five were my own file-assembly
mistakes (a duplicated `end Panda2608` from a wrong marker in my prefix-building script), not Lean
proof failures: N15 x3, N27 x1, N37 x1. Real proof errors: N01 chunk (contained the N02 bug), N02 (padicValNat
rewriting with an unresolved prime; fixed by splitting), N13 chunk and N15 (wrong factor in a
`Nat.mul_le_mul` step: `(2p+1)^b * p^b` vs `(2p+1)^b * (2p+1)^b`), N16 (compiled with the broken N15),
ROOT x4 (`simp only [Prod.mk.injEq]; omega` does not close the tuple goal; `subst; rfl` does).
Most calls: N15 (7), ROOT (6 + FINAL), N02 (4). Every other node took 1-2 calls.
No node reached the cap; nothing left unfinished.
