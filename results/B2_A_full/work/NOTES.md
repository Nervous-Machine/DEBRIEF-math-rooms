# Searcher notes, build 2, arm B2_A_full (full Lean feedback, planner's blueprint)

Start 2026-11-25 23:24:47 UTC (first tool call). File complete and `[ok]` at 23:56:48 UTC; FINAL called right after.

## Status of the nodes

All 38 blueprint nodes (N01-N37 and ROOT) are in the file, in blueprint order, with their statements exactly as
the planner wrote them. Every node is proved; the whole file compiles with no `sorry`, no `admit`, no axioms, no
`native_decide`, no `unsafe`, and no `maxHeartbeats` option. Lean reports only unused-variable warnings (below).

Checks: 3 calls to `check.sh` before FINAL (labelled N16, N37, N28), of which 2 returned `[error]` and 1 `[ok]`.
- Call 1 (N16, nodes N01-N16 written): 5 errors, all small: a `mul_comm` rewrite hitting the wrong product (N06,
  N12), `positivity` not knowing `0 < p` (N06), the nonexistent name `Nat.pos_pow_of_pos` (N12), a `pow_succ`
  rewrite hitting `2^(b+1)` instead of `p^(b+1)` (N15), and a metavariable left for `omega` (N16).
- Call 2 (N37, whole file): 1 error, in N28 (`pow_succ` rewrote `m^2` instead of `P^(b+1)`).
- Call 3 (N28): `[ok]`.

## Changed statements

None. No blueprint statement was changed, strengthened or weakened.

## Helper lemmas added (not in the blueprint)

- `caseA_pow_ne (p a m) (hp) (hodd) (hm : 1 ≤ m) : p^(2a+1) ≠ 2 (2p+1)^m + 1`. Both N09 (`lemma_2_3`) and N10
  (`lemma_2_4`) are instances of it, and N11 uses it directly: once N07 forces `p = 3` the mod-7 obstruction N08
  works for any exponent `m ≥ 1`, so the relation `b = a ∨ b = a + 1` is never needed in Case A.
- `s_sub_r_cases_aux (p u v a) (hp) (hu : u < p) (h : v * u = 2 p^a)`: N22 without the coprimality and `3 ≤ v`
  hypotheses. The point is that `u = s - r` satisfies `0 < u < p`, so `u` is coprime to `p^a` for free and
  `u ∣ 2`; Lemma 2.7 (N20) is therefore not needed on the path to the root. N22 is proved as stated by this helper
  (hence the unused `hodd`, `hcop`, `hv` warnings on N22). N37 calls the helper.
- `amgm_core (X Y m j)`: the AM-GM pair inequality with the exponents written as `m` and `m + 2j`; N26 is proved
  from it in both cases `i ≤ b` and `i ≥ b`.

## Where the proof departs from the blueprint's intended route (same statements, different proofs)

- N14 (`prop_2_5`) and N15 (`lemma_2_6`) are proved by size, not by LTE: for `b ≥ 1`,
  `(2p+1)^(2b+1) ≥ (2p+1)^(b+1) ≥ (2p)^(b+1) ≥ 4 p^(b+1) > 2 p^(b+1) + 1`, and likewise for `2 p^b + 1`.
  N02 (`lte_corollary`) and N13 (`pow_gt_two_mul_add_one`) are proved as stated (N02 via
  `padicValNat.pow_sub_pow`), but nothing downstream uses them.
- N19 (`geom_sum_modEq`) is proved by casting to `ZMod (s - r)` rather than with `Nat.ModEq.sum`. N20 uses it as
  planned, but N20 itself is off the path to the root (see `s_sub_r_cases_aux` above).
- N29 (`aux_eq_int`) uses `k` directly with `Nat.cast_sub`; N28 (`bound6`) substitutes `k = m + 2` to make the
  natural-number subtractions disappear.
- N31 takes the witness `A1 + A2` (the two truncated binomials add, since `(2k-1)^n = -(1-2k)^n` for odd `n`).

## Unused hypotheses (linter warnings, not errors)

`hodd` in N14 (`prop_2_5`), N22, N37 (`caseB_nontrivial`) and N12's dependency chain where the planner included
it; `hab` in N11 (`caseA_no_solution`); `hcop`, `hv` in N22; `ha` in N12 (`caseB_split`, `a ≥ 1` not needed since
`p^a > 0` already for `a = 0`). They are kept because the statements are the planner's.

## Mathematical route actually used for the root

Parity split (N03). Case A: N06 gives `p^(2a+1) = 2 (2p+1)^b + 1`, N07 forces `p = 3`, N08 kills it mod 7 (N11).
Case B: N12 gives `r s = 2p+1`, `z = p^a + r^n`, `s^n = r^n + 2 p^a`, `n = 2b+1`. If `r = 1`: N16 gives
`(a, b) = (1, 0)`, so `(x, y, z) = (2, 1, p+1)`. If `r > 1`: N17 gives `3 ≤ r < s < p`; `b = 0` is killed by N21;
the geometric-sum identity (N18) gives `S (s - r) = 2 p^a` with `0 < s - r < p`, so `s - r ∈ {1, 2}` (helper);
`s - r = 1` is killed by parity (N23); `s - r = 2` gives `S = p^a`, `r = 2k - 1`, `p = 2k^2 - 1` (N24); `a = b` is
killed by N25; `a = b + 1` is the auxiliary equation, closed by N28 (AM-GM bound) and N29-N35 (integer expansion,
`b` odd, `2k^2 ∣ 4b^2 + 3b + 1`) in N36: `k = 2`, `b = 1`, so `p = 7`, `(x, y, z) = (4, 3, 76)` (N37, ROOT).
