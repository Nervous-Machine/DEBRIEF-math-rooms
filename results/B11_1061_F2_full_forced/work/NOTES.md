# B11_1061_F2_full_forced: searcher notes

All six forced rooms closed. Every closure is relative to the statements of the rooms allowed to stay open
(N01, N02 literature imports; N21 local_witness, N22 projected_index, N23 lattice_coords,
N25 sqfree_progression_count, N29 local_density, N30 large_prime_tail, N31 parameter_sieve; N34 untouched).
No statement was changed. The file has sorry only in those allowed rooms.

## N38 local_denominator: closed, 2 attempts
1. Route: two explicit integer solutions of the homogeneous plane system, e = (31Cq, -465AB, -15Bq, -465AC, 0, e5)
   and f (with v4 = -465·508·AC, v0 = -508·31·C(15A+462C), ...). c + e and c + f lie on the plane, so by hsurj
   e and f are values of L·n. If p divides c_i and every L_ij, it divides e_i and f_i. Each e_i or f_i is a product
   of a divisor of W with one factor of the Good product, which gives the contradiction. Lean: `simp only at h0` made no progress.
2. Removed that line. Compiled.

## N42 singular_series_lower: closed, 2 attempts
1. Route: the rows are pairwise linearly independent (fc_lattice minor plus LinearIndependent.pair_iff), so
   bienvenu_lemma12 gives Multipliable. Then compare termwise against ap_product's factors through partial
   products (le_of_tendsto_of_tendsto' on HasProd). Lean: Finset.prod_le_prod needs MulLeftMono ℝ (monoid version).
2. Used Finset.prod_le_prod₀. Compiled.

## N46 threshold_lemma: closed, 4 attempts
1. Route: k = ⌈κ⌉, ℓ = log Y, κ log ℓ ≤ ℓ/18 eventually (isLittleO_log_id_atTop), and exp(ℓ/3) ≥ Kℓ^(10k+6)
   from pow_div_factorial_le_exp. Lean: Real.one_le_exp argument shape was wrong, and the gcongr/nlinarith on the last line timed out.
2. Fixed both. Lean: pow_div_factorial_le_exp takes x explicitly.
3. Fixed. Lean: `ring` could not match (1/3)^n against 3⁻¹^n.
4. Used `rw [div_pow]; ring`. Compiled.

## N47 two_height_core: closed, 3 attempts
1. Route: the full assembly. c0 = ch/Ch from region_bounds_int (the earlier arm's 1/2 replaced inside the body).
   Truncate the good denominators and the sieve triples to ⌈·⌉ elements. The planes form a sigma finset, with per-plane
   primes from plane_prime_count at τ = κ+1. union_card_bound and planes_meet_once give ≥ Σ − C(#planes, 2).
   The pair term is ≤ half the main term by threshold_lemma clause 9 (ε = M/(2K1²)). Then natAbs to ℕ sextuples,
   core_fiber_le_eight, core_from_sextuple, and perimeter 508 p4 p5 ∈ [(ch/Ch)Y, Y] via T² = Y/(Ch Z³).
   Lean: push_cast turned natAbs casts into |x|, and nlinarith timed out.
2. Used explicit casts and lemmas. Lean: `ring` after field_simp had no goals (3×).
3. Removed those lines. Compiled.

## N48 S_lower_bound: closed, 2 attempts
1. Route: apply two_height_core at exponent κ+1/3 (the room is stated for every κ > 0) with Q = Z = (log Y)^(κ+1/3)
   and Y = x/3600. That gives ≫ Y (log Y)^(3κ-5) cores, and each core (u,v) gives the ordered pair (3600u, 3600v)
   counted by S x (S_ge_card). (log(x/3600))^(3κ-5) ≥ 2^(-|3κ-5|) (log x)^(3κ-5). No dyadic shells or
   multipliers are needed. Lean: unknown identifier le_or_lt.
2. Used le_or_gt. Compiled.

## N45 plane_prime_count: closed, 6 attempts
1. Route: lattice_coords gives c, L, δ, K (vol = 3T²/(10⁵·465 q² δ), box C1 T). Apply bienvenu_prop21_uniform with
   d=2, t=6, A0 = 2τ, B0 = 4τ, L0 = 18|C2|+1, cV = k0/C1'², ε = 1/2 at N = C1'T.
   - Forms ≥ N^{9/10}: archimedean_bounds on the real point c + Lv. The real plane equations come from the integer
     equations at n = 0, e1, e2.
   - singular_series_lower gives ∏β ≥ c*.
   - prime_weight_to_count with V = Cu' Z² T, and log V ≤ 2 log T.
   - Remove collisions with collision_line on ≤ 36 pairs (pair rows differ by fc_lattice).
   - Thresholds come from isLittleO_log_rpow_rpow_atTop.
   Lean: "no goals" after field_simp, an nlinarith timeout, and the whole declaration hit maxHeartbeats 200000.
2. Added `set_option maxHeartbeats 400000 in`. Lean: a precedence slip (∏' p, β p / 2 parsed as the product of β p/2), and timeouts.
3. Parenthesised it. Lean: a final linarith failed, a rpow literal 6 vs Nat 6 rewrite failed, and timeouts remained.
4. Fixed those. Lean: only heartbeat timeouts remained, at the tail.
5. Split into helper lemmas ppc_lowK (real-plane lower bound) and ppc_collision (collision count), both sorry-free.
   Lean: one unsolved goal (ℓ vs Real.log T in hmain).
6. Fixed. Compiled.

## Truth as drawn
All six rooms are now proved from the rooms' statements, so none is open. Their truth is only as good as the open rooms
they rest on (N01/N02 literature; N21–N23, N25, N29–N31 forced elsewhere).

## Tempted to change and did not
- No statement was changed. N34 lattice_reduction was left exactly as it was.
- I did not touch the other arm's rooms.
- In N48 I used the room's uniformity in κ (κ+1/3) instead of the planner's dyadic sum. This uses the statement as
  drawn and does not change it. It does mean N47 as drawn, if true for all κ, absorbs the extra log factor by itself.
- The only additions are two helper lemmas for N45 and `set_option maxHeartbeats 400000 in` on plane_prime_count.
