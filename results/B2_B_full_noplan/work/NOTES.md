# NOTES — arm B2_B_full_noplan (full Lean feedback, no blueprint, no paper)

Target: `Panda2608.consecutive_exponents` (Theorem 1.1 of arXiv:2608.18608v2 as stated by the registrar).
Start 23:18 UTC, file complete and `[ok]` at 23:41 UTC, FINAL `[ok]` at 23:42 UTC (2026-11-25).
check.sh calls: 5 before FINAL (4 error, 1 ok) + 1 FINAL (ok) = 6 total.

## Route (my own; no blueprint, no paper)

Write q = 2p+1. Since |x−y| = 1, exactly one exponent is even, giving two shapes, each handled by one lemma:

1. **Even power of q** (`no_sol_pow_p`): p^(2k+1) + q^(2c) = z² with c ≥ 1. Then (z − q^c)(z + q^c) = p^(2k+1); both
   factors are powers of p (`Nat.dvd_prime_pow`) and p cannot divide both (it would divide 2q^c), so z − q^c = 1 and
   2q^c + 1 = p^(2k+1). Reducing mod p (q ≡ 1) gives p ∣ 3, so p = 3, q = 7, and 2·7^c + 1 = 3^(2k+1) is impossible
   mod 7 because an odd power of 3 is never 1 mod 7 (`three_pow_odd_mod_seven`). Covers x = y+1 with y even, and
   y = x+1 with x odd. No solutions.

2. **Even power of p** (`factor_pow_q`): p^(2c) + q^(2k+1) = z². Then (z − p^c)(z + p^c) = q^(2k+1) with coprime
   factors (their gcd divides 2p^c and q^(2k+1)), so by `exists_eq_pow_of_mul_eq_pow` they are u^(2k+1), v^(2k+1)
   with uv = q, u < v, and v^(2k+1) − u^(2k+1) = 2p^c.
   - y = x+1, x = 2c even (c ≥ 1): the pairing bound `pow_sub_pow_ge`
     ((2k+1)(v−u)(uv)^k ≤ v^(2k+1) − u^(2k+1)) gives (2c+1)p^c ≤ 2p^c, impossible. No solutions.
   - x = y+1, y = 2k+1 odd, c = k+1:
     - k = 0: u(u+2p) = 2p+1 forces u = 1, z = p+1: the solution (2, 1, p+1).
     - k ≥ 1: u, v odd, v − u = 2e with e ∣ p^(k+1) and e ≤ p, so e ∈ {1, p}. e = p forces u = 1 and the pairing
       bound kills it. e = 1 gives v = u+2, u = 2a+1 ≥ 3, m := a+1 ≥ 2, p = 2m² − 1 and
       (2m+1)^(2k+1) − (2m−1)^(2k+1) = 2p^(k+1): the **hard case** (`hard_case`).

3. **Hard case**: expand both sides. `expansion_odd` (via `expansion_even`, a two-term induction with explicit
   witnesses) gives LHS = 2 + 2k(2k+1)(2m)² + (2m)⁴R; `pow_sub_one_expansion` gives
   p^(k+1) = (2m²−1)^(k+1) = (−1)^(k+1) + (−1)^k(k+1)·2m² + 4m⁴T. Comparing modulo 4m⁴:
   - k even forces m² ∣ 1, contradiction (m ≥ 2);
   - k odd forces 2m² ∣ 4k² + 3k + 1, so 2m² ≤ 4k² + 3k + 1.
   Then k = 1 gives 8m⁴ = 32m², m = 2, p = 7, (u, v) = (3, 5), z = 27 + 49 = 76: the solution (4, 3, 76).
   k ≥ 3: pairing bound ⇒ (2k+1)(4m²−1)^k ≤ p^(k+1) ⇒ (2k+1)2^k ≤ p = 2m² − 1 ≤ 4k² + 3k, but
   2^k ≥ 2k+1 for k ≥ 3 (`two_mul_add_one_le_two_pow`) makes (2k+1)2^k ≥ 4k²+4k+1. Contradiction.

## Lemmas written (all proved, in file order)

- `pow_sub_pow_ge` — pairing/AM-GM bound (2k+1)(a−b)(ab)^k ≤ a^(2k+1) − b^(2k+1) for 0 ≤ b ≤ a in ℤ (induction).
- `two_mul_add_one_le_two_pow` — 2k+1 ≤ 2^k for k ≥ 3.
- `three_pow_odd_mod_seven` — 3^(2k+1) % 7 ≠ 1.
- `expansion_even`, `expansion_odd` — binomial-type expansions of (w±1)^n modulo w⁴, with explicit witnesses.
- `pow_sub_one_expansion` — (c−1)^(n+1) modulo c².
- `hard_case` — the k = 1 ∧ m = 2 conclusion above.
- `no_sol_pow_p` — shape 1.
- `factor_pow_q` — shape 2 factorization.
- `consecutive_exponents` — the target, assembled from the above.

## Not finished

Nothing: every lemma compiles without `sorry`; the first FINAL is the file as of 23:41 UTC.
Only Lean output is an `unusedVariables` warning on `hz` in the target statement, which is part of the verbatim
statement and so kept.
