# B11_1061_F1_full_forced: searcher notes

Start 21:13:35Z, FINAL called at about 22:10Z. All seven forced rooms closed. No room statement, definition or target was changed.
The only edits were to proof bodies and to new helper lemmas (tagged `-- N2x helper`) placed just before their rooms.

## Attempts per forced room

### N21 local_witness: closed, 1 attempt
- 0001: explicit witness. Take x0 = x4 = -q n and x2 = x4 + q v, with v = 3918 + W k. Here k comes from IsCoprime(31·C·W, q), so q n = 1 + 31 C v. Then n ≡ 1 mod W, and every coordinate is ≡ -1, 3917 or (for x5 = 239 + (W/508)·E) 239, all units mod rad W. Helper `lw_unit`. Lean: compiled, closed.

### N22 projected_index: closed, 1 attempt
- 0002: Γ = kernel of (u,v) ↦ ((15Aq + 6930BC)u + 14322C²v mod q², 15u + 31v mod 508), δ = 508. The index comes from `index_ker` plus surjectivity (CRT witness with u = 0). The iff is proved by explicit lifts: Q·x4 from the third equation, the q-divisibility of the first equation from C being a unit mod q, and the 508-divisibility from A, B, C ≡ 0 and q ≡ 1 mod W. Lean: compiled, closed.

### N25 sqfree_progression_count: closed, 2 attempts
- 0003: q = 1 + W k with k ∈ [K, 2K-2). A non-squarefree q has p² | q for a prime 13 ≤ p ≤ √N with p ∤ W, which puts k in one class mod p², so at most L/p² + 1 of them (helper `sq_class_card`). Then ∑ 1/p² ≤ 2/13 via `sum_Ioo_inv_sq_le`. Lean: errors. `Nat.prime_iff` misuse (the hypothesis was already `Nat.Prime`), unknown `Nat.dvd_sub'`, "no goals" after `interval_cases ... norm_num at`, unknown `Nat.Coprime.mul`, and max recursion in `nlinarith` with big numerals.
- 0004: same route with those steps repaired (`Nat.dvd_add_right`, `revert; norm_num`, `Nat.coprime_mul_iff_left`, plain `linarith` steps). Closed.

### N29 local_density: closed, 2 attempts
- 0005: CRT route. T = (primes of q) ∪ (primes ≤ P off Wq), so m = ∏_T p, and `ZMod.prodEquivPi` gives ZMod m ≃ Π_p ZMod p. Ω is the preimage of the product of the local good sets. Local counts are ≥ p³e^{-12/p} for p | q (six nonzero forms) and ≥ p³e^{-6/p²} otherwise (three two-condition systems), via 1-y ≥ e^{-2y}. Then ϑ = e^{-(12 M0 + 1)}. Lean: two errors. `rw [← card]` hit a motive error in the P-count, and the `Finset.prod_le_prod` signature had changed.
- 0006: used `le_trans` instead of the rewrite, and `prod_le_prod₀`. Closed.

### N30 large_prime_tail: closed, 3 attempts
- 0007: union over primes P < p ≤ 40qZ², p ∤ Wq. Each bad system is a product, or a fibred product over a, of single residue classes in intervals (helper `lpt_class`). Then ∑1/p² ≤ 2/P, ∑1/p ≤ 1 + log N ≤ 3 log(qZ) (`harmonic_le_one_add_log`, helper `lpt_log`), and #p ≤ N; Ct = 10⁶. Lean: unknown `Int.ediv_add_emod`, a missing cast normalisation in a `linarith`, the `462 ∣ W*q` side goal, and a heartbeat timeout from `nlinarith` calls.
- 0008: replaced the `nlinarith` calls with explicit steps and added maxHeartbeats 400000. Lean: unknown `Int.emod_add_ediv`, and one `linarith` lacked qZ ≤ qZ².
- 0009: `Int.emod_add_mul_ediv` and the missing inequality. Closed.

### N31 parameter_sieve: closed, 2 attempts
- 0010: `residue_blocks` on the box a ∈ [⌈qZ²/W⌉, +⌊qZ²/W⌋-1), b, c ∈ [⌈qZ/W⌉, +⌊qZ/W⌋-1), with Ω from `local_density`. This gives ≥ ϑq³Z⁴/(8W³), using m ≤ q·∏_{p≤P} p and Z ≥ 4W(1+M_P). Then the large-prime tail (via `large_prime_tail`) is removed, with P = ⌈4C'/K⌉+1, q0 = 4C'/K + 2 and Z0 ≥ (8C'/K)², and log x ≤ 2√x. Lean: a DecidablePred failure for the tail filter.
- 0011: added `classical`. Closed.

### N23 lattice_coords: closed, 2 attempts
- 0012: no Gauss reduction is needed. The projected lattice is {(u,v): v ≡ -ρu mod 508q²}, with ρ from CRT and 0 ≤ ρ < 508q². So the basis (1,-ρ), (0,508q²) has an inverse with entries ≤ 1. c is the plane point over (0,t0), 0 ≤ t0 < 508q². Lifts, uniqueness and size bounds come from the plane equations (helpers `lc_hlift`, `lc_proj`, `lc_zero`, `lc_bound`). K becomes {v0 ∈ [-2T/15,-T/15], v1 in an interval of length (30/3100000)|v0|/(508q²)}. Its area comes from finTwoArrow, `Measure.prod_apply` and an interval integral (`lc_volume`); convexity is direct (`lc_convex`), and |v_j| ≤ T (`lc_bounded`). Constants C0 = 2, C1 = 1, C2 = 10⁹, δ = 508. Lean: a single error, where `rw [abs_mul]` rewrote the wrong subterm in `lc_convex`.
- 0013: `abs_mul a`, `abs_mul b`. Closed.

## Truth as drawn
All seven forced rooms are now proved as drawn, so they are true as drawn. I made no judgement on the allowed-open rooms (N01, N02, lattice_reduction, and the six rooms another arm is forcing); they were left exactly as given.

## Tempted to change and did not
- In N23 I was tempted to use `projected_index` as a black box and extract a basis from an abstract finite-index subgroup. Instead I recomputed the lattice explicitly inside the proof. I did not change N22's statement to expose Γ.
- The earlier arm had fixed constants inside the bodies: ϑ = e^{-14M0}/2 in N29, csf = 1/(2W) in N25, Ct = 10⁶, and N31's Z0/q0/c2. I chose my own witnesses where needed (for example ϑ = e^{-(12M0+1)} and csf = 1/(10W)). These are existential witnesses inside proofs, not statement changes.
- I did not touch `lattice_reduction` (N34), even though it is reported false as drawn.
