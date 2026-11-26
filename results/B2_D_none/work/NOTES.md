# NOTES — arm B2_D_none (no checker until FINAL), searcher notes

Start 2026-11-25 23:25 UTC. File written blind (no compile) from the planner's 38-node blueprint.

## Node statements
All 37 node statements (N01–N37) and the ROOT are copied from the blueprint verbatim; no node
statement was changed. No helper lemmas were added (small `have`s inside proofs only).

## Proof sketch per node (what I believe is proved, pending the single FINAL compile)
- N01 coprime_mul_right_add_right. N02 padicValNat.pow_sub_pow (LTE) with x=2p+1, y=1, plus
  padicValNat.mul/self and p∤2. N03 Nat.even_or_odd' + omega. N04 Nat.coprime_of_dvd: a prime k
  dividing u-v and u+v divides 2v, is odd (divides w), so divides v and w, contradiction with
  Nat.eq_one_of_dvd_coprimes. N05 Nat.dvd_prime_pow on both factors.
- N06 z^2-q^(2b) factorisation written as (z-q)(z+q) via z = q+d and nlinarith; N04+N05 give
  z-q = 1. N07 Nat.ModEq: 3 ≡ 0 [MOD p]. N08 induction, residues {3,6,5}. N09/N10 via N07, N08.
- N12 exists_eq_pow_of_mul_eq_pow (GCDMonoid ℕ, Nat.isUnit_iff) on the coprime factorisation,
  Nat.pow_left_injective, coprime_pow_left/right_iff, lt_of_pow_lt_pow_left₀.
- N13 Nat.le_induction. N14 LTE (N02) gives v_p(2b+1)=b, so p^b ≤ 2b+1; N13 for b≥2, b=1 ⇒ p=3
  checked by norm_num. N15 size comparison with omega. N16 from N14/N15.
- N17 parity + omega. N18 geom_sum₂_mul_of_le. N19 Finset.sum_nat_mod + Nat.modEq_sub.
  N20 prime k | (s-r) and | S ⇒ k | 2p^a ⇒ k=2 (parity contradiction via N19) or k=p (k ≤ s-r < p).
- N21–N25 elementary. N26 two_mul_le_add_sq with b = i+t (or symmetric). N27 Finset.sum_range_reflect
  + sum_le_sum. N28 N27 + Nat.pow_lt_pow_left. N29 N18 zified. N30 induction with Nat.choose_succ_succ'.
  N31/N32 from N30 at t = ±2k, -2k^2. N33 Int.ModEq mod 2k^2 ⇒ 2k^2 | 4. N34 linear_combination.
  N35 Nat.le_induction. N36 combine N28, N29, N33, N34, N35. N37 nine-node bookkeeping.
- ROOT: parity split, case A ⇒ False (N11), case B ⇒ N12, r=1 ⇒ N16, r>1 ⇒ N37.

## Result of the first FINAL call
First and only FINAL call at 2026-11-26 00:32:34 UTC: the tool printed `[ok]`.
Lean output contained no errors; only warnings: two style hints (`haveI` -> `have`, in N02 and N14),
one `push_neg` deprecation hint (N36), and unused-variable warnings for hypotheses that the blueprint
statements carry but the proofs do not need: `hodd`, `ha` in N12 (caseB_split); `hodd` in N20
(lemma_2_7); `hodd`, `hcop`, `hv` in N22 (s_sub_r_cases); `hz : 0 < z` in the root theorem.
None of these affect correctness.

All 37 nodes and the root theorem compile with no `sorry`, no `axiom`, no `native_decide`, no
`maxHeartbeats` option. No node statement was changed. No second FINAL call was made.
End of work 2026-11-26 00:34 UTC (about 69 minutes of the 180-minute budget).
