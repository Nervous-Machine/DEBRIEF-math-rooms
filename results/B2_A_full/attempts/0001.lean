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

/-! ### Case A (x odd) -/

theorem coprime_p_q (p : ℕ) : Nat.Coprime p (2 * p + 1) :=
  (Nat.coprime_mul_right_add_right p 1 2).mpr (Nat.coprime_one_right p)

theorem lte_corollary (p : ℕ) (hp : p.Prime) (hodd : Odd p) (b : ℕ) :
    padicValNat p ((2 * p + 1) ^ (2 * b + 1) - 1) = 1 + padicValNat p (2 * b + 1) := by
  haveI := Fact.mk hp
  have h1 : (1 : ℕ) < 2 * p + 1 := by have := hp.two_le; omega
  have hdvd : p ∣ 2 * p + 1 - 1 := by simp
  have hnd : ¬ p ∣ 2 * p + 1 := by
    intro hd
    have h1' : p ∣ 1 := (Nat.dvd_add_right (dvd_mul_left p 2)).mp hd
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1')
  have key := padicValNat.pow_sub_pow (p := p) hodd h1 hdvd hnd (n := 2 * b + 1) (by omega)
  rw [one_pow] at key
  rw [key]
  have h2 : 2 * p + 1 - 1 = 2 * p := by omega
  rw [h2, padicValNat.mul (by norm_num) hp.ne_zero, padicValNat_self,
    padicValNat.eq_zero_of_not_dvd]
  intro h3
  have h4 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3
  subst h4
  obtain ⟨m, hm⟩ := hodd
  omega

theorem parity_split (x y : ℕ) (hxy : x = y + 1 ∨ y = x + 1) :
    (∃ a b : ℕ, x = 2 * a + 1 ∧ y = 2 * b ∧ (b = a ∨ b = a + 1)) ∨
    (∃ a b : ℕ, x = 2 * a ∧ y = 2 * b + 1 ∧ (a = b + 1 ∨ a = b)) := by
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' x
  · right
    rcases hxy with h | h
    · exact ⟨k, k - 1, hk, by omega, by omega⟩
    · exact ⟨k, k, hk, by omega, by omega⟩
  · left
    rcases hxy with h | h
    · exact ⟨k, k, hk, by omega, by omega⟩
    · exact ⟨k, k + 1, hk, by omega, by omega⟩

theorem coprime_sub_add_of_odd (u v w : ℕ) (hvu : v < u) (hw : Odd w)
    (h : (u - v) * (u + v) = w) (hcop : Nat.Coprime v w) :
    Nat.Coprime (u - v) (u + v) := by
  apply Nat.coprime_of_dvd
  intro k hk hk1 hk2
  have hkw : k ∣ w := h ▸ Dvd.dvd.mul_right hk1 _
  have hk2v : k ∣ 2 * v := by
    have e : (u + v) - (u - v) = 2 * v := by omega
    rw [← e]; exact Nat.dvd_sub hk2 hk1
  have hkodd : Odd k := Odd.of_dvd_nat hw hkw
  have hk2' : ¬ k ∣ 2 := by
    intro h2
    have e := (Nat.prime_dvd_prime_iff_eq hk Nat.prime_two).mp h2
    subst e; obtain ⟨m, hm⟩ := hkodd; omega
  have hkv : k ∣ v := ((Nat.Prime.dvd_mul hk).mp hk2v).resolve_left hk2'
  have hg : k ∣ Nat.gcd v w := Nat.dvd_gcd hkv hkw
  rw [hcop.gcd_eq_one] at hg
  exact hk.one_lt.ne' (Nat.dvd_one.mp hg)

theorem prime_pow_coprime_split (p m n k : ℕ) (hp : p.Prime) (h : m * n = p ^ k)
    (hc : Nat.Coprime m n) : m = 1 ∨ n = 1 := by
  obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).mp (Dvd.intro _ h)
  obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow hp).mp (Dvd.intro_left _ h)
  rcases Nat.eq_zero_or_pos i with hi0 | hi0
  · left; simp [hi0]
  rcases Nat.eq_zero_or_pos j with hj0 | hj0
  · right; simp [hj0]
  exfalso
  have h1 := (Nat.coprime_pow_left_iff hi0 _ _).mp hc
  have h2 := (Nat.coprime_pow_right_iff hj0 _ _).mp h1
  have h3 := h2.gcd_eq_one
  rw [Nat.gcd_self] at h3
  exact hp.one_lt.ne' h3

theorem caseA_reduce (p a b z : ℕ) (hp : p.Prime) (hodd : Odd p)
    (h : p ^ (2 * a + 1) + (2 * p + 1) ^ (2 * b) = z ^ 2) :
    p ^ (2 * a + 1) = 2 * (2 * p + 1) ^ b + 1 := by
  set v := (2 * p + 1) ^ b with hv
  have hv2 : (2 * p + 1) ^ (2 * b) = v ^ 2 := by rw [hv, ← pow_mul, mul_comm]
  rw [hv2] at h
  have hppos : 0 < p ^ (2 * a + 1) := by positivity
  have hvpos : 0 < v := by positivity
  have hvz : v < z := by
    by_contra hc
    push_neg at hc
    have := Nat.pow_le_pow_left hc 2
    omega
  have hfac : (z - v) * (z + v) = p ^ (2 * a + 1) := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hvz
    have e : v + d + 1 - v = d + 1 := by omega
    rw [e]
    nlinarith [h]
  have hcop : Nat.Coprime (z - v) (z + v) :=
    coprime_sub_add_of_odd z v _ hvz (Odd.pow hodd) hfac
      (Nat.Coprime.pow _ _ (coprime_p_q p).symm)
  rcases prime_pow_coprime_split p _ _ _ hp hfac hcop with h1 | h1
  · rw [h1, one_mul] at hfac
    omega
  · omega

theorem caseA_mod_p (p n m : ℕ) (hp : p.Prime) (hn : 1 ≤ n)
    (h : p ^ n = 2 * (2 * p + 1) ^ m + 1) : p = 3 := by
  have hq : 2 * p + 1 ≡ 1 [MOD p] := ((Nat.modEq_iff_dvd' (by omega)).mpr (by simp)).symm
  have h2 : 2 * (2 * p + 1) ^ m + 1 ≡ 2 * 1 ^ m + 1 [MOD p] := ((hq.pow m).mul_left 2).add_right 1
  have h3 : p ^ n ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr (dvd_pow_self p (by omega))
  rw [h] at h3
  have h4 : 3 ≡ 0 [MOD p] := by
    have h5 := h2.symm.trans h3
    simpa using h5
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (Nat.modEq_zero_iff_dvd.mp h4)

theorem three_pow_odd_mod_seven (a : ℕ) : 3 ^ (2 * a + 1) % 7 ≠ 1 := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    rcases lt_or_ge a 3 with ha | ha
    · interval_cases a <;> decide
    · have ih' := ih (a - 3) (by omega)
      have e : 2 * a + 1 = 2 * (a - 3) + 1 + 6 := by omega
      rw [e, pow_add, Nat.mul_mod]
      norm_num
      omega

/-- Helper (not in the blueprint): the Case A equation has no solution with a positive power of `2p+1`. -/
theorem caseA_pow_ne (p a m : ℕ) (hp : p.Prime) (hodd : Odd p) (hm : 1 ≤ m) :
    p ^ (2 * a + 1) ≠ 2 * (2 * p + 1) ^ m + 1 := by
  intro h
  have h3 := caseA_mod_p p (2 * a + 1) m hp (by omega) h
  subst h3
  have e : (2 * 3 + 1 : ℕ) = 7 := by norm_num
  rw [e] at h
  obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le' hm
  apply three_pow_odd_mod_seven a
  rw [h, pow_succ]
  omega

theorem lemma_2_3 (p a : ℕ) (hp : p.Prime) (hodd : Odd p) :
    p ^ (2 * a + 1) ≠ 2 * (2 * p + 1) ^ (a + 1) + 1 :=
  caseA_pow_ne p a (a + 1) hp hodd (by omega)

theorem lemma_2_4 (p a : ℕ) (hp : p.Prime) (hodd : Odd p) (ha : 1 ≤ a) :
    p ^ (2 * a + 1) ≠ 2 * (2 * p + 1) ^ a + 1 :=
  caseA_pow_ne p a a hp hodd ha

theorem caseA_no_solution (p a b z : ℕ) (hp : p.Prime) (hodd : Odd p) (hb : 1 ≤ b)
    (hab : b = a ∨ b = a + 1)
    (h : p ^ (2 * a + 1) + (2 * p + 1) ^ (2 * b) = z ^ 2) : False :=
  caseA_pow_ne p a b hp hodd hb (caseA_reduce p a b z hp hodd h)

/-! ### Case B (x even): the split -/

theorem caseB_split (p a b z : ℕ) (hp : p.Prime) (hodd : Odd p) (ha : 1 ≤ a)
    (h : p ^ (2 * a) + (2 * p + 1) ^ (2 * b + 1) = z ^ 2) :
    ∃ r s : ℕ, r * s = 2 * p + 1 ∧ Nat.Coprime r s ∧ r < s ∧
      z = p ^ a + r ^ (2 * b + 1) ∧ s ^ (2 * b + 1) = r ^ (2 * b + 1) + 2 * p ^ a := by
  set v := p ^ a with hv
  have hv2 : p ^ (2 * a) = v ^ 2 := by rw [hv, ← pow_mul, mul_comm]
  rw [hv2] at h
  have hqpos : 0 < (2 * p + 1) ^ (2 * b + 1) := by positivity
  have hvpos : 0 < v := by rw [hv]; exact Nat.pos_pow_of_pos _ hp.pos
  have hvz : v < z := by
    by_contra hc
    push_neg at hc
    have := Nat.pow_le_pow_left hc 2
    omega
  have hfac : (z - v) * (z + v) = (2 * p + 1) ^ (2 * b + 1) := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hvz
    have e : v + d + 1 - v = d + 1 := by omega
    rw [e]
    nlinarith [h]
  have hqodd : Odd ((2 * p + 1) ^ (2 * b + 1)) := Odd.pow ⟨p, rfl⟩
  have hcop : Nat.Coprime (z - v) (z + v) :=
    coprime_sub_add_of_odd z v _ hvz hqodd hfac (Nat.Coprime.pow _ _ (coprime_p_q p))
  have hn : 2 * b + 1 ≠ 0 := by omega
  have hnpos : 0 < 2 * b + 1 := by omega
  obtain ⟨r, hr⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr hcop) hfac
  obtain ⟨s, hs⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr hcop.symm)
    (by rw [mul_comm]; exact hfac)
  have hrs : r * s = 2 * p + 1 := by
    apply Nat.pow_left_injective hn
    simp only [mul_pow]
    rw [← hr, ← hs, hfac]
  rw [hr, hs] at hcop
  have hcop' : Nat.Coprime r s :=
    (Nat.coprime_pow_right_iff hnpos _ _).mp ((Nat.coprime_pow_left_iff hnpos _ _).mp hcop)
  have hlt : r < s := by
    have : r ^ (2 * b + 1) < s ^ (2 * b + 1) := by omega
    exact (Nat.pow_lt_pow_iff_left hn).mp this
  exact ⟨r, s, hrs, hcop', hlt, by omega, by omega⟩

/-! ### Case B, trivial split -/

theorem pow_gt_two_mul_add_one (p b : ℕ) (hp : 3 ≤ p) (hb : 2 ≤ b) : 2 * b + 1 < p ^ b := by
  induction b, hb using Nat.le_induction with
  | base => nlinarith
  | succ n hn ih =>
    rw [pow_succ]
    nlinarith [Nat.mul_le_mul_right (p ^ n) hp]

theorem prop_2_5 (p b : ℕ) (hp : p.Prime) (hodd : Odd p)
    (h : (2 * p + 1) ^ (2 * b + 1) = 2 * p ^ (b + 1) + 1) : b = 0 := by
  by_contra hb
  have hb1 : 1 ≤ b := Nat.pos_of_ne_zero hb
  have hp2 := hp.two_le
  have h1 : (2 * p + 1) ^ (b + 1) ≤ (2 * p + 1) ^ (2 * b + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : (2 * p) ^ (b + 1) ≤ (2 * p + 1) ^ (b + 1) := Nat.pow_le_pow_left (by omega) _
  have h3 : (2 * p) ^ (b + 1) = 2 ^ (b + 1) * p ^ (b + 1) := mul_pow _ _ _
  have h4 : 4 ≤ 2 ^ (b + 1) := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (b + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h5 : 1 ≤ p ^ (b + 1) := Nat.one_le_pow _ _ hp.pos
  have h6 := Nat.mul_le_mul_right (p ^ (b + 1)) h4
  omega

theorem lemma_2_6 (p b : ℕ) (hp : p.Prime) :
    (2 * p + 1) ^ (2 * b + 1) ≠ 2 * p ^ b + 1 := by
  intro h
  have hp2 := hp.two_le
  have h1 : (2 * p + 1) ^ (b + 1) ≤ (2 * p + 1) ^ (2 * b + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : (2 * p) ^ (b + 1) ≤ (2 * p + 1) ^ (b + 1) := Nat.pow_le_pow_left (by omega) _
  have h3 : (2 * p) ^ (b + 1) = 2 ^ (b + 1) * (p ^ b * p) := by rw [mul_pow, pow_succ]
  have h4 : 2 ≤ 2 ^ (b + 1) := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (b + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h5 : 1 ≤ p ^ b := Nat.one_le_pow _ _ hp.pos
  have h6 := Nat.mul_le_mul h4 (Nat.mul_le_mul_left (p ^ b) hp2)
  omega

theorem caseB_trivial (p a b : ℕ) (hp : p.Prime) (hodd : Odd p) (hab : a = b + 1 ∨ a = b)
    (h : (2 * p + 1) ^ (2 * b + 1) = 1 + 2 * p ^ a) : a = 1 ∧ b = 0 := by
  rcases hab with rfl | rfl
  · have hb := prop_2_5 p b hp hodd (by omega)
    subst hb
    exact ⟨rfl, rfl⟩
  · exact absurd (by omega) (lemma_2_6 p _ hp)

theorem consecutive_exponents (p x y z : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : x = y + 1 ∨ y = x + 1)
    (h : p ^ x + (2 * p + 1) ^ y = z ^ 2) :
    (x, y, z) = (2, 1, p + 1) ∨ (p = 7 ∧ (x, y, z) = (4, 3, 76)) := by
  sorry

end Panda2608
