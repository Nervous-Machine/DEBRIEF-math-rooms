/-
Copyright 2026 Nervous Machine. Licensed under the Apache License, Version 2.0.

The statement of Theorem 1.1 of arXiv:2608.18608v2 (Subhasis Panda, "On the Diophantine equation
p^x + (2p+1)^y = z^2 with consecutive exponents", 19 October 2026), written in Lean 4 by the registrar of the
rooms experiment on 2026-11-25 from the paper's statement alone. Nobody else has read this statement against the
paper; that reading is an open gap of the record.

Theorem 1.1. Let p be an odd prime and suppose p^x + (2p+1)^y = z^2 where x, y, z are positive integers with
|x - y| = 1. Then (i) if p ≠ 7 the only solution is (x, y, z) = (2, 1, p+1); (ii) if p = 7 the only solutions are
(2, 1, 8) and (4, 3, 76).

Stated here in the form "every solution is one of the listed ones"; (2, 1, 8) is (2, 1, p+1) at p = 7.
-/
module

public import Mathlib

@[expose] public section

namespace Panda2608

/-! ## Elementary bounds -/

/-- Pairing bound: for `0 ≤ b ≤ a`, `a^(2k+1) - b^(2k+1) ≥ (2k+1)(a-b)(ab)^k`. -/
theorem pow_sub_pow_ge (a b : ℤ) (hb : 0 ≤ b) (hab : b ≤ a) (k : ℕ) :
    (2 * (k : ℤ) + 1) * (a - b) * (a * b) ^ k ≤ a ^ (2 * k + 1) - b ^ (2 * k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hab0 : 0 ≤ a * b := mul_nonneg (hb.trans hab) hb
    have hd : 0 ≤ a - b := sub_nonneg.mpr hab
    have hamgm : 2 * (a ^ (k + 1) * b ^ (k + 1)) ≤ a ^ (2 * k + 2) + b ^ (2 * k + 2) := by
      have e1 : a ^ (2 * k + 2) = (a ^ (k + 1)) ^ 2 := by ring
      have e2 : b ^ (2 * k + 2) = (b ^ (k + 1)) ^ 2 := by ring
      rw [e1, e2]
      nlinarith [sq_nonneg (a ^ (k + 1) - b ^ (k + 1))]
    have hid : a ^ (2 * (k + 1) + 1) - b ^ (2 * (k + 1) + 1)
        = a * b * (a ^ (2 * k + 1) - b ^ (2 * k + 1))
          + (a - b) * (a ^ (2 * k + 2) + b ^ (2 * k + 2)) := by ring
    rw [hid]
    have h1 := mul_le_mul_of_nonneg_left ih hab0
    have h2 := mul_le_mul_of_nonneg_left hamgm hd
    push_cast
    linear_combination h1 + h2

/-- `2k+1 ≤ 2^k` for `k ≥ 3`. -/
theorem two_mul_add_one_le_two_pow (k : ℕ) (hk : 3 ≤ k) : 2 * k + 1 ≤ 2 ^ k := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge k 3 with h | h
    · have : k = 2 := by omega
      subst this
      norm_num
    · have := ih h
      rw [pow_succ]
      omega

/-- An odd power of 3 is never `1 mod 7`. -/
theorem three_pow_odd_mod_seven (k : ℕ) : 3 ^ (2 * k + 1) % 7 ≠ 1 := by
  have key : ∀ k : ℕ, 3 ^ (2 * k + 1) % 7 = 3 ∨ 3 ^ (2 * k + 1) % 7 = 6 ∨ 3 ^ (2 * k + 1) % 7 = 5 := by
    intro k
    induction k with
    | zero => left; norm_num
    | succ k ih =>
      have e : 3 ^ (2 * (k + 1) + 1) = 9 * 3 ^ (2 * k + 1) := by ring
      rw [e]
      omega
  rcases key k with h | h | h <;> omega

/-! ## Algebraic expansions -/

/-- Expansion of `(w+1)^(2k) ∓ (w-1)^(2k)` modulo `w^3`, resp. `w^4`. -/
theorem expansion_even (w : ℤ) (k : ℕ) : ∃ R S : ℤ,
    (w + 1) ^ (2 * k) - (w - 1) ^ (2 * k) = 4 * k * w + w ^ 3 * R ∧
    (w + 1) ^ (2 * k) + (w - 1) ^ (2 * k) = 2 + 2 * k * (2 * k - 1) * w ^ 2 + w ^ 4 * S := by
  induction k with
  | zero => exact ⟨0, 0, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨R, S, hA, hB⟩ := ih
    refine ⟨4 * k + w ^ 2 * R + R + 4 * k * (2 * k - 1) + 2 * w ^ 2 * S,
      2 * k * (2 * k - 1) + w ^ 2 * S + S + 2 * R, ?_, ?_⟩
    · have e1 : (w + 1) ^ (2 * (k + 1)) = (w + 1) ^ 2 * (w + 1) ^ (2 * k) := by ring
      have e2 : (w - 1) ^ (2 * (k + 1)) = (w - 1) ^ 2 * (w - 1) ^ (2 * k) := by ring
      rw [e1, e2]
      push_cast
      linear_combination (w ^ 2 + 1) * hA + 2 * w * hB
    · have e1 : (w + 1) ^ (2 * (k + 1)) = (w + 1) ^ 2 * (w + 1) ^ (2 * k) := by ring
      have e2 : (w - 1) ^ (2 * (k + 1)) = (w - 1) ^ 2 * (w - 1) ^ (2 * k) := by ring
      rw [e1, e2]
      push_cast
      linear_combination (w ^ 2 + 1) * hB + 2 * w * hA

/-- Expansion of `(w+1)^(2k+1) - (w-1)^(2k+1)` modulo `w^4`. -/
theorem expansion_odd (w : ℤ) (k : ℕ) : ∃ R : ℤ,
    (w + 1) ^ (2 * k + 1) - (w - 1) ^ (2 * k + 1) = 2 + 2 * k * (2 * k + 1) * w ^ 2 + w ^ 4 * R := by
  obtain ⟨R, S, hA, hB⟩ := expansion_even w k
  refine ⟨R + S, ?_⟩
  have e1 : (w + 1) ^ (2 * k + 1) = (w + 1) * (w + 1) ^ (2 * k) := by ring
  have e2 : (w - 1) ^ (2 * k + 1) = (w - 1) * (w - 1) ^ (2 * k) := by ring
  rw [e1, e2]
  linear_combination w * hA + hB

/-- Expansion of `(c-1)^(n+1)` modulo `c^2`. -/
theorem pow_sub_one_expansion (c : ℤ) (n : ℕ) : ∃ T : ℤ,
    (c - 1) ^ (n + 1) = (-1) ^ (n + 1) + (-1) ^ n * (n + 1) * c + c ^ 2 * T := by
  induction n with
  | zero => exact ⟨0, by ring⟩
  | succ n ih =>
    obtain ⟨T, hT⟩ := ih
    refine ⟨(-1) ^ n * (n + 1) + c * T - T, ?_⟩
    rw [pow_succ, hT]
    push_cast
    ring

/-! ## The hard case: `(2m+1)^(2k+1) - (2m-1)^(2k+1) = 2 p^(k+1)` with `p = 2m^2 - 1` -/

theorem hard_case (m : ℤ) (k : ℕ) (p : ℤ) (hm : 2 ≤ m) (hk : 1 ≤ k) (hp : p = 2 * m ^ 2 - 1)
    (heq : (2 * m + 1) ^ (2 * k + 1) = (2 * m - 1) ^ (2 * k + 1) + 2 * p ^ (k + 1)) :
    k = 1 ∧ m = 2 := by
  obtain ⟨R, hR⟩ := expansion_odd (2 * m) k
  obtain ⟨T, hT⟩ := pow_sub_one_expansion (2 * m ^ 2) k
  rw [← hp] at hT
  have hE : 2 + 2 * (k : ℤ) * (2 * k + 1) * (2 * m) ^ 2 + (2 * m) ^ 4 * R = 2 * p ^ (k + 1) := by
    linear_combination heq - hR
  rw [hT] at hE
  have hp0 : 0 < p := by rw [hp]; nlinarith
  rcases Nat.even_or_odd k with hke | hko
  · -- k even: impossible
    exfalso
    have h1 : ((-1 : ℤ)) ^ (k + 1) = -1 := Odd.neg_one_pow hke.add_one
    have h2 : ((-1 : ℤ)) ^ k = 1 := Even.neg_one_pow hke
    rw [h1, h2] at hE
    have h4 : (4 : ℤ) * 1 = 4 * (m ^ 2 * ((k + 1) - 2 * k * (2 * k + 1) + 2 * m ^ 2 * (T - 2 * R))) := by
      linear_combination hE
    have hdvd : m ^ 2 ∣ 1 := ⟨_, mul_left_cancel₀ (by norm_num) h4⟩
    have := Int.eq_one_of_dvd_one (by positivity) hdvd
    nlinarith
  · -- k odd
    have h1 : ((-1 : ℤ)) ^ (k + 1) = 1 := Even.neg_one_pow hko.add_one
    have h2 : ((-1 : ℤ)) ^ k = -1 := Odd.neg_one_pow hko
    rw [h1, h2] at hE
    have h4 : (4 * m ^ 2) * (4 * (k : ℤ) ^ 2 + 3 * k + 1) = (4 * m ^ 2) * (2 * m ^ 2 * (T - 2 * R)) := by
      linear_combination hE
    have h5 : (4 * (k : ℤ) ^ 2 + 3 * k + 1) = 2 * m ^ 2 * (T - 2 * R) :=
      mul_left_cancel₀ (by positivity) h4
    have hle : 2 * m ^ 2 ≤ 4 * (k : ℤ) ^ 2 + 3 * k + 1 :=
      Int.le_of_dvd (by positivity) ⟨_, h5⟩
    obtain ⟨j, hj⟩ := hko
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · -- k = 1
      subst hj0
      have hk1 : k = 1 := by omega
      subst hk1
      refine ⟨rfl, ?_⟩
      rw [hp] at heq
      have h8 : (8 : ℤ) * (m ^ 2 * (m ^ 2 - 4)) = 8 * 0 := by linear_combination -heq
      have h9 := mul_left_cancel₀ (by norm_num : (8 : ℤ) ≠ 0) h8
      rcases mul_eq_zero.mp h9 with h | h
      · nlinarith
      · have : (m - 2) * (m + 2) = 0 := by linear_combination h
        rcases mul_eq_zero.mp this with h' | h'
        · linarith
        · linarith
    · -- k ≥ 3: size contradiction
      exfalso
      have hk3 : 3 ≤ k := by omega
      have hbound := pow_sub_pow_ge (2 * m + 1) (2 * m - 1) (by linarith) (by linarith) k
      have e1 : (2 * m + 1) - (2 * m - 1) = 2 := by ring
      have e2 : (2 * m + 1) * (2 * m - 1) = 4 * m ^ 2 - 1 := by ring
      rw [e1, e2, heq] at hbound
      have hb2 : 2 * ((2 * (k : ℤ) + 1) * (4 * m ^ 2 - 1) ^ k) ≤ 2 * p ^ (k + 1) := by
        linear_combination hbound
      have hb3 : (2 * (k : ℤ) + 1) * (4 * m ^ 2 - 1) ^ k ≤ p ^ (k + 1) :=
        le_of_mul_le_mul_left hb2 (by norm_num)
      have h3 : (2 * p) ^ k ≤ (4 * m ^ 2 - 1) ^ k :=
        pow_le_pow_left₀ (by linarith) (by rw [hp]; linarith) k
      rw [mul_pow] at h3
      have h4 : (2 * (k : ℤ) + 1) * (2 ^ k * p ^ k) ≤ p * p ^ k := by
        rw [← pow_succ']
        exact (mul_le_mul_of_nonneg_left h3 (by positivity)).trans hb3
      rw [← mul_assoc] at h4
      have h5 : (2 * (k : ℤ) + 1) * 2 ^ k ≤ p := le_of_mul_le_mul_right h4 (pow_pos hp0 k)
      have hB : (2 * (k : ℤ) + 1) ≤ 2 ^ k := by exact_mod_cast two_mul_add_one_le_two_pow k hk3
      have hBB := mul_le_mul_of_nonneg_left hB (by positivity : (0 : ℤ) ≤ 2 * (k : ℤ) + 1)
      nlinarith

/-! ## The two factorization shapes -/

/-- `p^(2k+1) + (2p+1)^(2c) = z^2` has no solutions with `c ≥ 1`. -/
theorem no_sol_pow_p (p z c k : ℕ) (hp : p.Prime) (hodd : Odd p) (hc : 0 < c)
    (h : p ^ (2 * k + 1) + (2 * p + 1) ^ (2 * c) = z ^ 2) : False := by
  have hp2 : 2 ≤ p := hp.two_le
  have hqc : 0 < (2 * p + 1) ^ c := by positivity
  have hpk : 0 < p ^ (2 * k + 1) := by positivity
  have hzgt : (2 * p + 1) ^ c < z := by
    have e : ((2 * p + 1) ^ c) ^ 2 = (2 * p + 1) ^ (2 * c) := by ring
    have : ((2 * p + 1) ^ c) ^ 2 < z ^ 2 := by rw [e]; omega
    exact lt_of_pow_lt_pow_left₀ 2 (by omega) this
  obtain ⟨a, ha⟩ : ∃ a, z = (2 * p + 1) ^ c + a + 1 := ⟨z - (2 * p + 1) ^ c - 1, by omega⟩
  subst ha
  have hfac : (a + 1) * (2 * (2 * p + 1) ^ c + a + 1) = p ^ (2 * k + 1) := by
    have e : ((2 * p + 1) ^ c + a + 1) ^ 2
        = (2 * p + 1) ^ (2 * c) + (a + 1) * (2 * (2 * p + 1) ^ c + a + 1) := by ring
    omega
  -- both factors are powers of p
  obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow hp).mp (Dvd.intro _ hfac)
  obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow hp).mp (Dvd.intro_left _ hfac)
  have hi0 : i = 0 := by
    by_contra hne
    have hpi : p ∣ a + 1 := by
      rw [hi']; exact dvd_pow_self p hne
    have hj0 : j ≠ 0 := by
      intro hj0
      rw [hj0, pow_zero] at hj'
      omega
    have hpj : p ∣ 2 * (2 * p + 1) ^ c + a + 1 := by
      rw [hj']; exact dvd_pow_self p hj0
    have hp2q : p ∣ 2 * (2 * p + 1) ^ c := by
      have := Nat.dvd_sub hpj hpi
      rwa [show 2 * (2 * p + 1) ^ c + a + 1 - (a + 1) = 2 * (2 * p + 1) ^ c by omega] at this
    rcases (Nat.Prime.dvd_mul hp).mp hp2q with h2 | h2
    · have := Nat.le_of_dvd (by norm_num) h2
      have : p = 2 := by omega
      subst this
      exact absurd hodd (by decide)
    · have := hp.dvd_of_dvd_pow h2
      have h1 : p ∣ 1 := by
        have := Nat.dvd_sub this (dvd_mul_left p 2)
        rwa [show 2 * p + 1 - 2 * p = 1 by omega] at this
      exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  subst hi0
  rw [pow_zero] at hi'
  have ha0 : a = 0 := by omega
  subst ha0
  have hmain : 2 * (2 * p + 1) ^ c + 1 = p ^ (2 * k + 1) := by omega
  -- mod p : p ∣ 3, so p = 3
  have hdvd3 : p ∣ 3 := by
    have h1 : p ∣ p ^ (2 * k + 1) := dvd_pow_self p (by omega)
    rw [← hmain] at h1
    have h2 : 2 * p ∣ (2 * p + 1) ^ c - 1 := by
      have := Nat.sub_dvd_pow_sub_pow (2 * p + 1) 1 c
      rwa [one_pow, show 2 * p + 1 - 1 = 2 * p by omega] at this
    have h3 : p ∣ 2 * ((2 * p + 1) ^ c - 1) := dvd_mul_of_dvd_right (dvd_trans (dvd_mul_left p 2) h2) 2
    have := Nat.dvd_sub h1 h3
    rwa [show 2 * (2 * p + 1) ^ c + 1 - 2 * ((2 * p + 1) ^ c - 1) = 3 by omega] at this
  have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hdvd3
  subst hp3
  -- mod 7
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  have h7 : 3 ^ (2 * k + 1) % 7 = 1 := by
    rw [← hmain, pow_succ]
    omega
  exact three_pow_odd_mod_seven k h7

/-- `p^(2c) + (2p+1)^(2k+1) = z^2` forces a coprime factorization of `2p+1`. -/
theorem factor_pow_q (p z c k : ℕ) (hp : p.Prime)
    (h : p ^ (2 * c) + (2 * p + 1) ^ (2 * k + 1) = z ^ 2) :
    ∃ u v : ℕ, u * v = 2 * p + 1 ∧ u < v ∧ v ^ (2 * k + 1) = u ^ (2 * k + 1) + 2 * p ^ c ∧
      z = u ^ (2 * k + 1) + p ^ c := by
  have hp2 : 2 ≤ p := hp.two_le
  have hpc : 0 < p ^ c := by positivity
  have hqk : 0 < (2 * p + 1) ^ (2 * k + 1) := by positivity
  have hzgt : p ^ c < z := by
    have e : (p ^ c) ^ 2 = p ^ (2 * c) := by ring
    have : (p ^ c) ^ 2 < z ^ 2 := by rw [e]; omega
    exact lt_of_pow_lt_pow_left₀ 2 (by omega) this
  obtain ⟨a, ha0, ha⟩ : ∃ a, 0 < a ∧ z = p ^ c + a := ⟨z - p ^ c, by omega, by omega⟩
  subst ha
  have hfac : a * (2 * p ^ c + a) = (2 * p + 1) ^ (2 * k + 1) := by
    have e : (p ^ c + a) ^ 2 = p ^ (2 * c) + a * (2 * p ^ c + a) := by ring
    omega
  -- coprimality of the two factors
  have hcop : Nat.Coprime a (2 * p ^ c + a) := by
    have hcq : Nat.Coprime ((2 * p + 1) ^ (2 * k + 1)) (2 * p ^ c) := by
      apply Nat.Coprime.pow_left
      apply Nat.Coprime.mul_right
      · exact Nat.coprime_two_right.mpr ⟨p, rfl⟩
      · apply Nat.Coprime.pow_right
        have : Nat.Coprime p (1 + p * 2) :=
          (Nat.coprime_add_mul_left_right p 1 2).mpr (Nat.coprime_one_right p)
        rw [show 2 * p + 1 = 1 + p * 2 by ring]
        exact this.symm
    apply Nat.eq_one_of_dvd_coprimes hcq.symm
    · have := Nat.dvd_sub (Nat.gcd_dvd_right a (2 * p ^ c + a)) (Nat.gcd_dvd_left a (2 * p ^ c + a))
      rwa [show 2 * p ^ c + a - a = 2 * p ^ c by omega] at this
    · rw [← hfac]
      exact dvd_mul_of_dvd_left (Nat.gcd_dvd_left _ _) _
  have hunit : IsUnit (gcd a (2 * p ^ c + a)) := by
    rw [gcd_eq_nat_gcd, hcop.gcd_eq_one]; exact isUnit_one
  obtain ⟨u, hu⟩ := exists_eq_pow_of_mul_eq_pow hunit hfac
  have hunit' : IsUnit (gcd (2 * p ^ c + a) a) := by
    rw [gcd_eq_nat_gcd, hcop.symm.gcd_eq_one]; exact isUnit_one
  obtain ⟨v, hv⟩ := exists_eq_pow_of_mul_eq_pow hunit' (by rw [mul_comm]; exact hfac)
  have hn : 2 * k + 1 ≠ 0 := by omega
  refine ⟨u, v, ?_, ?_, ?_, ?_⟩
  · apply Nat.pow_left_injective hn
    simp only
    rw [mul_pow, ← hu, ← hv, hfac]
  · have : u ^ (2 * k + 1) < v ^ (2 * k + 1) := by rw [← hu, ← hv]; omega
    exact lt_of_pow_lt_pow_left₀ _ (by omega) this
  · rw [← hu, ← hv]; omega
  · rw [← hu]; omega

/-! ## Main theorem -/

/-- Theorem 1.1 of arXiv:2608.18608v2: the only positive solutions of `p^x + (2p+1)^y = z^2` with `p` an odd
prime and `|x - y| = 1` are `(x, y, z) = (2, 1, p+1)`, and, when `p = 7`, also `(4, 3, 76)`. -/
theorem consecutive_exponents (p x y z : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : x = y + 1 ∨ y = x + 1)
    (h : p ^ x + (2 * p + 1) ^ y = z ^ 2) :
    (x, y, z) = (2, 1, p + 1) ∨ (p = 7 ∧ (x, y, z) = (4, 3, 76)) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hp0Z : (0 : ℤ) < p := by exact_mod_cast hp.pos
  rcases hxy with rfl | rfl
  · -- Case A: x = y + 1
    rcases Nat.even_or_odd' y with ⟨c, hc | hc⟩
    · -- y = 2c, c ≥ 1
      exfalso
      subst hc
      exact no_sol_pow_p p z c c hp hodd (by omega) h
    · -- y = 2k + 1, x = 2k + 2
      subst hc
      have h' : p ^ (2 * (c + 1)) + (2 * p + 1) ^ (2 * c + 1) = z ^ 2 := by
        rw [show 2 * (c + 1) = 2 * c + 1 + 1 by ring]; exact h
      obtain ⟨u, v, huv, hlt, hv, hzeq⟩ := factor_pow_q p z (c + 1) c hp h'
      have hu0 : 0 < u := by
        rcases Nat.eq_zero_or_pos u with h0 | h0
        · rw [h0] at huv; omega
        · exact h0
      have hvle : v ≤ 2 * p + 1 := Nat.le_of_dvd (by omega) (Dvd.intro_left u huv)
      rcases Nat.eq_zero_or_pos c with hc0 | hc0
      · -- k = 0 : the solution (2, 1, p+1)
        subst hc0
        simp only [mul_zero, zero_add, pow_one] at hv hzeq
        have hu1 : u = 1 := by
          by_contra hne
          have : 2 ≤ u := by omega
          nlinarith
        subst hu1
        have hz' : z = p + 1 := by omega
        left
        rw [hz']
      · -- k ≥ 1 : the hard case
        -- u, v odd
        have hodd_uv : Odd (u * v) := by rw [huv]; exact ⟨p, rfl⟩
        obtain ⟨hu_odd, hv_odd⟩ := Nat.odd_mul.mp hodd_uv
        have hu2 : u % 2 = 1 := Nat.odd_iff.mp hu_odd
        have hv2 : v % 2 = 1 := Nat.odd_iff.mp hv_odd
        obtain ⟨e, he⟩ : ∃ e, v = u + 2 * e := ⟨(v - u) / 2, by omega⟩
        -- the pairing bound, cast to ℤ
        have hvZ : (v : ℤ) ^ (2 * c + 1) = (u : ℤ) ^ (2 * c + 1) + 2 * (p : ℤ) ^ (c + 1) := by
          exact_mod_cast hv
        have huvZ : (v : ℤ) * u = 2 * p + 1 := by rw [mul_comm]; exact_mod_cast huv
        have hltZ : (u : ℤ) ≤ v := by exact_mod_cast hlt.le
        have hbound := pow_sub_pow_ge (v : ℤ) (u : ℤ) (by positivity) hltZ c
        rw [hvZ, huvZ] at hbound
        have hQ : (p : ℤ) ^ c ≤ (2 * p + 1) ^ c := pow_le_pow_left₀ (by positivity) (by linarith) c
        -- e divides p^(c+1), hence e = 1 or e = p
        have hdvd : v - u ∣ v ^ (2 * c + 1) - u ^ (2 * c + 1) := Nat.sub_dvd_pow_sub_pow v u (2 * c + 1)
        rw [hv, show u ^ (2 * c + 1) + 2 * p ^ (c + 1) - u ^ (2 * c + 1) = 2 * p ^ (c + 1) by omega,
          show v - u = 2 * e by omega] at hdvd
        have hedvd : e ∣ p ^ (c + 1) := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd
        obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow hp).mp hedvd
        have hele : e ≤ p := by omega
        have hj1 : j ≤ 1 := by
          have : p ^ j ≤ p ^ 1 := by rw [pow_one]; omega
          exact (pow_le_pow_iff_right₀ hp.one_lt).mp this
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj1 with hj0 | hj0
        · -- e = 1 : v = u + 2
          rw [hj0, pow_zero] at hj'
          subst hj'
          have hve : v = u + 2 := by omega
          -- u ≥ 3 since u = 1 would give p = 1
          have hu3 : 3 ≤ u := by
            by_contra hlt3
            have hu1 : u = 1 := by omega
            rw [hu1, hve, hu1] at huv
            omega
          obtain ⟨a, hua⟩ := hu_odd
          have ha1 : 1 ≤ a := by omega
          have hpZ : (p : ℤ) = 2 * ((a : ℤ) + 1) ^ 2 - 1 := by
            have := huvZ
            rw [hve, hua] at this
            push_cast at this
            nlinarith
          have e1 : (v : ℤ) = 2 * ((a : ℤ) + 1) + 1 := by rw [hve, hua]; push_cast; ring
          have e2 : (u : ℤ) = 2 * ((a : ℤ) + 1) - 1 := by rw [hua]; push_cast; ring
          rw [e1, e2] at hvZ
          obtain ⟨hc1, hm2⟩ := hard_case ((a : ℤ) + 1) c p (by omega) hc0 hpZ hvZ
          have ha : a = 1 := by omega
          subst ha
          subst hc1
          have hp7 : p = 7 := by
            have : (p : ℤ) = 7 := by rw [hpZ]; norm_num
            exact_mod_cast this
          right
          refine ⟨hp7, ?_⟩
          rw [hzeq, hua, hp7]
          norm_num
        · -- e = p : v = u + 2p, forcing u = 1, impossible by size
          exfalso
          rw [hj0, pow_one] at hj'
          rw [hj'] at he
          have hu1 : u = 1 := by
            by_contra hne
            have : 2 ≤ u := by omega
            rw [he] at huv
            nlinarith
          subst hu1
          have hvp : (v : ℤ) - 1 = 2 * p := by
            have : v = 1 + 2 * p := he
            rw [this]; push_cast; ring
          push_cast at hbound
          rw [hvp] at hbound
          have hpc : 0 < (p : ℤ) ^ c := pow_pos hp0Z c
          have hcZ : (1 : ℤ) ≤ c := by exact_mod_cast hc0
          have h1 : (2 * (c : ℤ) + 1) * (2 * p) * p ^ c ≤ (2 * (c : ℤ) + 1) * (2 * p) * (2 * p + 1) ^ c :=
            mul_le_mul_of_nonneg_left hQ (by positivity)
          have h2 := h1.trans hbound
          rw [pow_succ] at h2
          nlinarith [mul_pos hp0Z hpc]
  · -- Case B: y = x + 1
    rcases Nat.even_or_odd' x with ⟨c, hc | hc⟩
    · -- x = 2c, c ≥ 1, y = 2c + 1
      exfalso
      subst hc
      obtain ⟨u, v, huv, hlt, hv, hzeq⟩ := factor_pow_q p z c c hp h
      have hc0 : 0 < c := by omega
      have hvZ : (v : ℤ) ^ (2 * c + 1) = (u : ℤ) ^ (2 * c + 1) + 2 * (p : ℤ) ^ c := by
        exact_mod_cast hv
      have huvZ : (v : ℤ) * u = 2 * p + 1 := by rw [mul_comm]; exact_mod_cast huv
      have hltZ : (u : ℤ) + 1 ≤ v := by exact_mod_cast hlt
      have hbound := pow_sub_pow_ge (v : ℤ) (u : ℤ) (by positivity) (by linarith) c
      rw [hvZ, huvZ] at hbound
      have hQ : (p : ℤ) ^ c ≤ (2 * p + 1) ^ c := pow_le_pow_left₀ (by positivity) (by linarith) c
      have hpc : 0 < (p : ℤ) ^ c := pow_pos hp0Z c
      have hcZ : (1 : ℤ) ≤ c := by exact_mod_cast hc0
      have h1 : (2 * (c : ℤ) + 1) * (1 * p ^ c) ≤ (2 * (c : ℤ) + 1) * (((v : ℤ) - u) * (2 * p + 1) ^ c) :=
        mul_le_mul_of_nonneg_left (mul_le_mul (by linarith) hQ (by positivity) (by linarith)) (by positivity)
      have h2 : (2 * (c : ℤ) + 1) * (((v : ℤ) - u) * (2 * p + 1) ^ c) ≤ 2 * p ^ c := by
        linear_combination hbound
      nlinarith
    · -- x = 2c + 1, y = 2c + 2
      exfalso
      subst hc
      have h' : p ^ (2 * c + 1) + (2 * p + 1) ^ (2 * (c + 1)) = z ^ 2 := by
        rw [show 2 * (c + 1) = 2 * c + 1 + 1 by ring]; exact h
      exact no_sol_pow_p p z (c + 1) c hp hodd (by omega) h'

end Panda2608
