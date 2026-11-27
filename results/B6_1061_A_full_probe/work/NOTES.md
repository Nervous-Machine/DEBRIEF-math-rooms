# NOTES — B6_1061_A_full_probe (searcher)

Arm: full Lean feedback, planner blueprint (48 rooms + ROOT), hold-position rule, probe-first rule.
Start 2026-11-27 02:26:02 UTC; FINAL called 03:41:55 UTC, accepted, returned [sorry] (16 declarations use sorry: N01 N02 N21 N22 N23 N25 N29 N30 N31 N34 N38 N42 N45 N46 N47 N48; the dependents N27 N36 N40 and li_1061 inherit it) (budget 180 min, 2M tokens; stopped early because the remaining
rooms were all out of reach, see "What would close the rest").

## Summary

File: `Erdos1061.lean` (one file, `namespace Erdos1061`, rooms in blueprint order before the target). Header, `S`
and the root statement are verbatim from `rooms/Challenge_1061.lean`; every room statement is verbatim from
`blueprint_1061_nodes.yaml` (checked by script before FINAL). No statement was changed, no hypothesis added,
no axiom / admit / native_decide / unsafe; three rooms carry `set_option maxHeartbeats 400000 in` (N16, N24, N32).

Root: NOT proved. The target's body is a complete proof **from N48** (κ = (R+6)/3 gives S x ≥ c·x·(log x)^{R+1},
so S x/(x (log x)^R) ≥ c log x → ∞), but N48 is open, so `li_1061` still "uses sorry" transitively.

### Rooms closed (body has no `sorry`; may cite open rooms as black boxes) — 32 of 46 non-literature rooms

| join type | closed | open |
|---|---|---|
| algebraic_identity | N03 N04 N05 N09 N10 N13 N14 N17 N18 N19 N32 N39 | N21 N34 |
| assembly | N06 N12 N24 N36 N40 ROOT-step | N31 N42 N46 N47 |
| case_split | N07 N08 N15 N20 N43 | N29 |
| extremal_averaging | N11 N16 N26 N28 N33 N35 N41 N44 | N23 N25 N30 |
| two_structure_coupling | N37 | N22 N38 N45 |
| quantitative_improvement | — | N48 |
| literature_import | — | N01 N02 (not attempted, as instructed) |

Dependencies used as black boxes by closed rooms: N36 uses N21; N40 uses N35 N36 N37 N38 N20; N24 uses N16 N18;
N27 uses N25 N26; N19 uses N18 N13; N07 uses N06; N06 uses N03 N04 N05; N39 uses N18 N14 N15; ROOT uses N48.
Rooms proved with no open dependency at all: N03–N05, N06–N20 (all), N24, N26, N28, N32, N33, N35, N37, N39, N41,
N43, N44, N11. Only N27 (via N25), N36 (via N21), N40 (via N38) and the ROOT step (via N48) rest on open rooms.

### Rooms left open (14), with the obstacle and a real partial attempt in the file

- N21 local_witness — CRT construction: u = 0, v = q·v' with 31Cv' ≡ −1 (mod q) makes the first three equations
  integral; 508 ∣ (…) and units mod every p ∣ W force further congruences on v' mod 8·127² and mod 3·5·7·11·31.
  Set up, the CRT choice left open.
- N22 projected_index — needs the exact index q²δ of the projected lattice (structure of the solution set of the three
  divisibility conditions); only the witness point from N21 is produced.
- N23 lattice_coords — needs Gauss reduction, an exact pullback volume and a box containment; none in Mathlib.
- N25 sqfree_progression_count — needs #{q ≡ 1 (W), p² ∣ q, q ≤ 2Q} ≤ 2Q/(W p²) + 1 (one class mod p² since (W,p)=1)
  summed over p ≥ 13 (p ∣ W is impossible); Legendre-type count not formalised in time. Constants fixed.
- N29 local_density — CRT over q·∏_{p≤P} p with per-prime densities; not attempted beyond the statement of ϑ.
- N30 large_prime_tail — union bound over primes P < p ≤ 2qZ² of residue-class counts, with ∑1/p² ≤ 1/P and the
  harmonic bound; not formalised.
- N31 parameter_sieve — assembly of N28, N29, N30; constants fixed, bookkeeping open.
- N34 lattice_reduction — **FALSE as drawn** (see below). Proof written modulo the Bezout step `IsCoprime m p`.
- N38 local_denominator — p ∣ q case needs a CRT witness with x4 ≢ 0 (mod p) (q = p·q' squarefree); open.
- N42 singular_series_lower — first conjunct (β_p > 0) proved from N40; Multipliable needs the admissibility input to
  N02 (pairwise linear independence from N39, `LinearIndependent.pair_iff`), and the bound c* ≤ ∏'β_p needs a
  comparison of infinite products of positive reals. Mathlib's `Multipliable.tprod_le_tprod` needs an ordered monoid
  (not ℝ under ×), and I found no `Multipliable → Summable log` lemma; the log route also needs an upper bound
  β_p ≤ 1 + O(1/p²) that the hypotheses do not give. Left open after the first conjunct.
- N45 plane_prime_count — assembly through N01 (Bienvenu) with (log T)^{O(1)} uniformity; open.
- N46 threshold_lemma — nine "polylog ≤ ε·Y^{1/2}"-type inequalities with an explicit Y0; needs
  isLittleO_log_rpow_rpow_atTop manipulations; only log T = (log Y − log Ch − 3 log Z)/2 proved.
- N47 two_height_core — big assembly; constants fixed, open.
- N48 S_lower_bound — shells Y_j = c0^j x with multipliers g ≤ x/(3600 Y_j); the (log x) gain needs the sum over
  ≍ log x shells; open.

### Statements I believe are false as drawn

- **N34 lattice_reduction**: `p : ℕ` is not assumed prime. With p = 0, `¬ 0 ∣ L'.relIndex L` just says the index is
  finite, and conclusion (1) says every x ∈ L is y + 0•z ∈ L', i.e. L ≤ L' — false for L = ⊤, L' = 2ℤ (ι = Fin 1).
  With p = 4, L = ℤ, L' = 2ℤ (index 2, ¬ 4 ∣ 2): 1 = y + 4z with y even is impossible. The intended statement needs
  `p.Prime` (then `IsCoprime m p` follows and the written proof closes).
- N17 zero_form_criteria is true but the hypotheses 2,3,7,11 ≠ 0 are not needed: all three iffs are ring identities
  (third pair: E1 = −15u + 31v, E2 = −u − βE1, E3 = v − γE1 with u = 31α−462β−1, v = 15α+462γ+1).

### Join types: which gave way

- algebraic_identity: 12 of 14 closed; the two open ones (N21, N34) are not identities at all (a CRT construction and a
  false statement).
- extremal_averaging: 8 of 11 closed (incl. the Legendre sieve N11 and the convergent product N41); open ones are the
  genuine sieve/lattice-volume rooms N23 N25 N30.
- case_split: 5 of 6; assembly: 5 of 9 (the big assemblies N31 N42 N46 N47 open); two_structure_coupling: 1 of 4
  (N37 closed by evaluating the vanishing coordinate at three points of (ZMod p)²; N22 N38 N45 open);
  quantitative_improvement: 0 of 1.
- The planner predicted two_structure_coupling as the first type to fail and N23 as the hardest provable room; both
  held up (N23 untouched beyond its setup, N22/N38/N45 open).

### What would close the root

N01 (Bienvenu's uniform theorem) is a literature import and sits under N45 → N47 → N48 → ROOT, so the root cannot be
reached in this arm regardless. Below the imports, the missing pieces are the lattice/sieve rooms (N22 N23 N25 N29
N30 N31), the two CRT witnesses (N21 N38), the singular-series comparison (N42), the asymptotic threshold (N46), and
the two big assemblies (N45 N47) plus the shell summation (N48).

### Proof routes worth recording

- N37: no lattice reduction needed. Over ZMod p (p ∤ Wq) the plane equations hold for every m : Fin 2 → ZMod p
  (lift m to ℤ); the map m ↦ (x0−x4, x2−x4) is onto because 465·det = ±465q²δ and 465·508 ∣ W; evaluating the
  vanishing coordinate at (u,v) = (0,0),(1,0),(0,1) gives exactly the excluded divisibility pairs of `Good`.
  W = 2³·3·5·7·11·31·127².
- N39: integral_lift at n = 0, e₀, e₁ gives L i j = a_i·15(L0j−L4j) + b_i·31(L2j−L4j) over ℝ, so the L-minor is
  (a_i b_j − b_i a_j)·D; N15 gives the a/b minors.
- N32: subtracting the two plane systems gives a rank-2 skew system in (u,v,w); case split on which of Δα,Δβ,Δγ is
  nonzero pins w, then u, v; if all Δ = 0, coprimality forces (q,A,B,C) = (q',A',B',C').
- N11: Legendre count with error 2^|P|−1 by induction on the prime set; ∏(1−1/p) ≥ 2^{-11}.
- N41: |log f_p| ≤ 72/p² for p ≥ 13 from log x ≤ x−1, log x ≥ 1−1/x; p ∣ W ⇒ p ≤ 127; K = 2·10⁷.
- N16: c = 1/2, C = 4000; all twelve bounds by linarith over product atoms after bounding βu, γs, β²u, … separately.

### Lean/Mathlib pitfalls met (pinned commit)

`Nat.Coprime.mul` absent (use symm + mul_right); `Finset.prod_le_prod₀`; `card_insert_of_notMem`;
`card_filter_add_card_filter_not`; `pow_le_pow_left₀`; `Set.mem_ofPred_eq`; `Π` is a reserved token (hypothesis
names like hΠ break parsing); `rw … at h1 h2` fails if the pattern is missing in one of them; linarith treats `N / p`
and `N * (1/p)` as different atoms; `linear_combination` needs the coefficient of `hΔα`-style definitional equations;
whole-declaration heartbeat budget (200000) exhausted by nlinarith in big contexts — clear hypotheses first.

## Call log (check.sh), 44 calls before FINAL + FINAL = 45, 0 refused, 16 returned [error], FINAL [sorry]

- 02:29 call 1 (N03): skeleton, all 48 statements + target elaborate as drawn; [sorry].
- 02:34 call 2 (N06): batch N03,N04,N05,N06,N09,N10,N12,N13,N14,N17,N33,N43,N44 → errors (names: card_insert_of_notMem, prod_le_prod₀, cast forms).
- 02:39 call 3 (N16): + N07,N15,N16,N18,N19,N20; N15/N16 heartbeat timeouts (big nlinarith), N07 Coprime.mul name, N18 rw, N20 gcd args.
- 02:45 call 4 (N08): + N08 (fiber ≤ 8 via injection into Bool³), N40 (assembly from N35–N38 + N20), ROOT (from N48 at κ=(R+6)/3). Only N07 and N16 (4 of 12 goals) still erroring.
- 02:46 call 5 (N16): same file, read all errors.
- 02:49 call 6 (N24): + N24 (from N16+N18), N27 (Markov from N25+N26), N36 (from N21). N07, N16 now compile.
- 02:53 call 7 (N35): + N35 (p²−6p count via projection) with helper zero_set_card_le, N34 attempt. Helper got clobbered by my edit script.
- 02:55 call 8 (N27): all errors fixed → [sorry]. Closed (no sorry in body): N03–N10, N12–N20, N24, N27, N33, N35, N36, N40, N43, N44, ROOT.
  Rooms still open: N11 N21 N22 N23 N25 N26 N28 N29 N30 N31 N32 N34 N37 N38 N39 N41 N42 N45 N46 N47 N48 (+ N01, N02 literature).
- N34 lattice_reduction is FALSE as drawn: p is any natural, not assumed prime. Counterexamples: p = 0 (¬ 0 ∣ m iff m ≠ 0, then claim 1 says L ⊆ L'); p = 4, L = ℤ, L' = 2ℤ (index 2, ¬ 4 ∣ 2, but 1 ≠ y + 4z with y even). Proof written modulo the Bezout step `IsCoprime m p` which is the false part.
- N17 zero_form_criteria: the hypotheses (2 ≠ 0, 3 ≠ 0, 7 ≠ 0, 11 ≠ 0) are not needed; the iffs are ring identities (third pair: E1 = -15u + 31v, E2 = -u - βE1, E3 = v - γE1).
- 02:58–03:04 calls 9–29: attempt sweep. Real partial attempts (setup + sorry at the open core, obstacle stated in a comment) for N11 N21 N22 N23 N25 N26 N28 N29 N30 N31 N32 N37 N38 N39 N41 N42 N45 N46 N47 N48; one tagged call each; all [sorry]. Every non-literature room now has a tagged call.
- Next: finish N28 (injection Ω × range × range × range → box), then N37 (coefficient extraction mod p at (u,v) ≡ (0,0),(1,0),(0,1); W = 2^3·3·5·7·11·31·127^2 so p ∤ W ⟹ p ∤ 465·508·462).
- 03:06 call 30 (N28): N28 closed (injection Ω × range³ → box via lift a ω k = a + ((ω.val - a) mod m) + m k).
- 03:10–03:13 calls 31–32 (N37): N37 closed. Route: work in ZMod p; the plane equations hold for every m : Fin 2 → ZMod p (lift m to ℤ by ZMod.cast); the map m ↦ (u,v) = (x0−x4, x2−x4) is surjective because its determinant d satisfies 465·d = ±465q²δ and p ∤ 465·508·q (465, 508 ∣ W); evaluate the vanishing coordinate at (u,v) = (0,0), (1,0), (0,1) and read off p ∣ A ∧ p ∣ 462B+q (i=1), p ∣ A ∧ p ∣ 462C+q (i=3), p ∣ 31A−462B−q ∧ p ∣ 15A+462C+q (i=5), or q ≡ 0 / 1 ≡ 0 (i=0,2,4). No lattice reduction needed.
- Next: N39 (fc_lattice) via integral_lift at n = 0, e0, e1: L i j = a_i·15(L0j−L4j) + b_i·31(L2j−L4j) over ℝ, so the L-minor is (a_i b_j − b_i a_j)·D with D ≠ 0, and N15 gives the a/b minors.
- 03:17 call 33 (N39): N39 closed (minors of L = (a_i b_j − b_i a_j)·D over ℝ via integral_lift at n = 0, e₀, e₁; N15 for the a/b minors).
- 03:20 call 34 (N26): N26 closed with CH = 2, Q1 = 1: swap sums, #{q ≤ ⌊2Q⌋ : p ∣ q} = ⌊2Q⌋/p (Nat.Ioc_filter_dvd_card_eq_div), ∑_{p} 1/p² ≤ ∑_{i∈Ioo 1 N} 1/i² ≤ 1 (sum_Ioo_inv_sq_le).
- Next: N11 via Legendre induction (|cnt_P(N) − N∏(1−1/p)| ≤ 2^|P| − 1), then ∏ ≥ 2^{-11}; c6 = 2^{-12}, X0 = 2^24.
- 03:25 calls 35–37 (N11): N11 closed. Helper legendre_count: |#{g ≤ N : P-free} − N∏(1−1/p)| ≤ 2^|P| − 1 by induction on P (the p-divisible P-free g ≤ N are p·h with h ≤ N/p P-free); then ∏_{p|n}(1−1/p) ≥ 2^{-11}; c6 = 2^{-12}, X0 = 2^24. Pitfall met: linarith treats `N / p` and `N * (1/p)` as different atoms.
- Next: N41 (ap_product): |log f_p| ≤ 72/p² for p ∤ W via log x ≤ x−1 and log x ≥ 1−1/x; p ∣ W ⇒ p ≤ 127 and |log f_p| ≤ 8p; Summable.of_norm_bounded with K/p², K = 2·10^7; Real.multipliable_of_summable_log, Real.rexp_tsum_eq_tprod.
- 03:30 calls 38–40 (N41): N41 closed as planned (K = 2·10^7; p ∣ W ⇒ p ≤ 127 by factoring W; p ∤ W ⇒ p ≥ 13).
- Next: N42 (needs Summable log β from Multipliable β (N02), tsum_le_tsum on logs, LinearIndependent.pair_iff from N39 minors).
- 03:30–03:36 calls 41–44 (N32): N32 closed (rank-2 skew system; coincident planes excluded by coprimality).
- 03:38 verification script: all 48 statements + header + target verbatim; no admit/axiom/native_decide/unsafe; maxHeartbeats ≤ 400000.
- 03:41:55 FINAL → [sorry] (accepted; first FINAL).
