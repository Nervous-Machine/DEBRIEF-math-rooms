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
  have := Fact.mk hp
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
  have hv2 : (2 * p + 1) ^ (2 * b) = v ^ 2 := by rw [hv, ← pow_mul, mul_comm 2 b]
  rw [hv2] at h
  have hppos : 0 < p ^ (2 * a + 1) := pow_pos hp.pos _
  have hvpos : 0 < v := by positivity
  have hvz : v < z := by
    by_contra hc
    have hc' : z ≤ v := not_lt.mp hc
    have := Nat.pow_le_pow_left hc' 2
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
  have hv2 : p ^ (2 * a) = v ^ 2 := by rw [hv, ← pow_mul, mul_comm 2 a]
  rw [hv2] at h
  have hqpos : 0 < (2 * p + 1) ^ (2 * b + 1) := by positivity
  have hvpos : 0 < v := pow_pos hp.pos a
  have hvz : v < z := by
    by_contra hc
    have hc' : z ≤ v := not_lt.mp hc
    have := Nat.pow_le_pow_left hc' 2
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
  have h3 : (2 * p) ^ (b + 1) = 2 ^ (b + 1) * (p ^ b * p) := by rw [mul_pow, pow_succ p]
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
  · exact absurd (by omega : (2 * p + 1) ^ (2 * a + 1) = 2 * p ^ a + 1) (lemma_2_6 p a hp)

/-! ### Case B, nontrivial split -/

theorem nontrivial_bounds (p r s : ℕ) (hrs : r * s = 2 * p + 1) (hr : 1 < r) (hlt : r < s) :
    3 ≤ r ∧ s < p := by
  have hodd : Odd (r * s) := by rw [hrs]; exact ⟨p, rfl⟩
  have hr3 : 3 ≤ r := by
    rcases Nat.even_or_odd r with he | ho
    · exact absurd (he.mul_right s) (Nat.not_even_iff_odd.mpr hodd)
    · obtain ⟨m, hm⟩ := ho; omega
  refine ⟨hr3, ?_⟩
  have h3 : 3 * s ≤ r * s := Nat.mul_le_mul_right s hr3
  omega

theorem geom_identity (r s n : ℕ) (hrs : r ≤ s) :
    (∑ i ∈ Finset.range n, r ^ i * s ^ (n - 1 - i)) * (s - r) = s ^ n - r ^ n :=
  geom_sum₂_mul_of_le hrs n

theorem geom_sum_modEq (r s n : ℕ) (hrs : r ≤ s) :
    (∑ i ∈ Finset.range n, r ^ i * s ^ (n - 1 - i)) ≡ n * r ^ (n - 1) [MOD (s - r)] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  have hs : ((s : ℕ) : ZMod (s - r)) = (r : ZMod (s - r)) := by
    rw [ZMod.natCast_eq_natCast_iff]
    exact ((Nat.modEq_iff_dvd' hrs).mpr dvd_rfl).symm
  push_cast
  rw [hs]
  rw [Finset.sum_congr rfl (g := fun _ => (r : ZMod (s - r)) ^ (n - 1))]
  · simp
  · intro i hi
    rw [Finset.mem_range] at hi
    rw [← pow_add]
    congr 1
    omega

theorem lemma_2_7 (p r s a b : ℕ) (hp : p.Prime) (hodd : Odd p) (hcop : Nat.Coprime r s)
    (hr : 3 ≤ r) (hlt : r < s) (hsp : s < p)
    (h : (∑ i ∈ Finset.range (2 * b + 1), r ^ i * s ^ (2 * b - i)) * (s - r) = 2 * p ^ a) :
    Nat.Coprime (s - r) (∑ i ∈ Finset.range (2 * b + 1), r ^ i * s ^ (2 * b - i)) := by
  have hmod := geom_sum_modEq r s (2 * b + 1) hlt.le
  simp only [Nat.add_sub_cancel] at hmod
  apply Nat.coprime_of_dvd
  intro k hk hk1 hk2
  have hS0 : (∑ i ∈ Finset.range (2 * b + 1), r ^ i * s ^ (2 * b - i)) ≡ 0 [MOD k] :=
    Nat.modEq_zero_iff_dvd.mpr hk2
  have hmodk := Nat.ModEq.of_dvd hk1 hmod
  have hk3 : k ∣ (2 * b + 1) * r ^ (2 * b) := Nat.modEq_zero_iff_dvd.mp (hmodk.symm.trans hS0)
  have hkr : ¬ k ∣ r := by
    intro hkr
    have hks : k ∣ s := by
      have e : s = (s - r) + r := by omega
      rw [e]; exact dvd_add hk1 hkr
    have hg := Nat.dvd_gcd hkr hks
    rw [hcop.gcd_eq_one] at hg
    exact hk.one_lt.ne' (Nat.dvd_one.mp hg)
  have hkn : k ∣ 2 * b + 1 := by
    rcases (Nat.Prime.dvd_mul hk).mp hk3 with h1 | h1
    · exact h1
    · exact absurd (hk.dvd_of_dvd_pow h1) hkr
  have hk2p : k ∣ 2 * p ^ a := by rw [← h]; exact Dvd.dvd.mul_left hk1 _
  rcases (Nat.Prime.dvd_mul hk).mp hk2p with h1 | h1
  · have e := (Nat.prime_dvd_prime_iff_eq hk Nat.prime_two).mp h1
    subst e; omega
  · have e := (Nat.prime_dvd_prime_iff_eq hk hp).mp (hk.dvd_of_dvd_pow h1)
    subst e
    have := Nat.le_of_dvd (by omega) hk1
    omega

theorem nontrivial_b_pos (p r s a : ℕ) (hsp : s < p) (ha : 1 ≤ a)
    (h : s = r + 2 * p ^ a) : False := by
  have : p ≤ p ^ a := Nat.le_self_pow (by omega) p
  omega

/-- Helper (not in the blueprint): `s_sub_r_cases` without the coprimality hypothesis. -/
theorem s_sub_r_cases_aux (p u v a : ℕ) (hp : p.Prime) (hu : u < p) (h : v * u = 2 * p ^ a) :
    (u = 1 ∧ v = 2 * p ^ a) ∨ (u = 2 ∧ v = p ^ a) := by
  have hpa : 0 < p ^ a := pow_pos hp.pos a
  have hu0 : 0 < u := by
    rcases Nat.eq_zero_or_pos u with h0 | h0
    · subst h0; omega
    · exact h0
  have hcop : Nat.Coprime u p := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    exact absurd (Nat.le_of_dvd hu0 hd) (not_le.mpr hu)
  have hdvd : u ∣ 2 * p ^ a := ⟨v, by rw [← h, mul_comm]⟩
  have hu2 : u ∣ 2 := (Nat.Coprime.pow_right a hcop).dvd_of_dvd_mul_right hdvd
  have hle : u ≤ 2 := Nat.le_of_dvd (by norm_num) hu2
  interval_cases u
  · left; omega
  · right; omega

theorem s_sub_r_cases (p u v a : ℕ) (hp : p.Prime) (hodd : Odd p) (hcop : Nat.Coprime u v)
    (hv : 3 ≤ v) (hu : u < p) (h : v * u = 2 * p ^ a) :
    (u = 1 ∧ v = 2 * p ^ a) ∨ (u = 2 ∧ v = p ^ a) :=
  s_sub_r_cases_aux p u v a hp hu h

theorem s_ne_r_add_one (p r : ℕ) (h : r * (r + 1) = 2 * p + 1) : False := by
  obtain ⟨m, hm⟩ := Nat.even_mul_succ_self r
  omega

theorem k_param (p r : ℕ) (hr : 3 ≤ r) (h : r * (r + 2) = 2 * p + 1) :
    ∃ k : ℕ, 2 ≤ k ∧ r = 2 * k - 1 ∧ p = 2 * k ^ 2 - 1 := by
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' r
  · exfalso
    subst hm
    have e : 2 * m * (2 * m + 2) = 2 * (m * (2 * m + 2)) := by ring
    omega
  · subst hm
    refine ⟨m + 1, by omega, by omega, ?_⟩
    have h2 : p + 1 = 2 * (m + 1) ^ 2 := by nlinarith [h]
    omega

theorem remark_2_8 (p r s b : ℕ) (hb : 1 ≤ b) (hrs : r * s = 2 * p + 1)
    (hS : ∑ i ∈ Finset.range (2 * b + 1), r ^ i * s ^ (2 * b - i) = p ^ b) : False := by
  have hterm : r ^ b * s ^ (2 * b - b) ≤ ∑ i ∈ Finset.range (2 * b + 1), r ^ i * s ^ (2 * b - i) :=
    Finset.single_le_sum (f := fun i => r ^ i * s ^ (2 * b - i)) (fun i _ => Nat.zero_le _)
      (Finset.mem_range.mpr (by omega))
  have e : 2 * b - b = b := by omega
  rw [e, ← mul_pow, hrs, hS] at hterm
  have : p ^ b < (2 * p + 1) ^ b := Nat.pow_lt_pow_left (by omega) (by omega)
  omega

/-- Helper (not in the blueprint): the AM-GM pair inequality in normalized exponents. -/
theorem amgm_core (X Y m j : ℕ) :
    2 * (Y ^ (m + j) * X ^ (m + j)) ≤ Y ^ m * X ^ (m + 2 * j) + Y ^ (m + 2 * j) * X ^ m := by
  have h1 := two_mul_le_add_sq (X ^ j) (Y ^ j)
  have h2 := Nat.mul_le_mul_left (Y ^ m * X ^ m) h1
  have e1 : Y ^ (m + j) * X ^ (m + j) = (Y ^ m * X ^ m) * (X ^ j * Y ^ j) := by ring
  have e2 : Y ^ m * X ^ (m + 2 * j) + Y ^ (m + 2 * j) * X ^ m
      = (Y ^ m * X ^ m) * ((X ^ j) ^ 2 + (Y ^ j) ^ 2) := by ring
  rw [e1, e2]
  linarith [h2]

theorem amgm_pair (X Y b i : ℕ) (hi : i ≤ 2 * b) :
    2 * (Y ^ b * X ^ b) ≤ Y ^ i * X ^ (2 * b - i) + Y ^ (2 * b - i) * X ^ i := by
  rcases le_total i b with hib | hbi
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hib
    have e : 2 * (i + j) - i = i + 2 * j := by omega
    rw [e]
    exact amgm_core X Y i j
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hbi
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (show j ≤ b by omega)
    have e1 : 2 * (j + m) - (j + m + j) = m := by omega
    have e2 : j + m + j = m + 2 * j := by omega
    have e3 : j + m = m + j := by omega
    rw [e1, e2, e3, add_comm (Y ^ (m + 2 * j) * X ^ m)]
    exact amgm_core X Y m j

theorem geom_sum_lower (X Y b : ℕ) :
    (2 * b + 1) * (Y ^ b * X ^ b) ≤ ∑ i ∈ Finset.range (2 * b + 1), Y ^ i * X ^ (2 * b - i) := by
  have key : ∀ i ∈ Finset.range (2 * b + 1),
      2 * (Y ^ b * X ^ b) ≤ Y ^ i * X ^ (2 * b - i) + Y ^ (2 * b - i) * X ^ i :=
    fun i hi => amgm_pair X Y b i (by rw [Finset.mem_range] at hi; omega)
  have h2 := Finset.sum_le_sum key
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul] at h2
  have h3 : ∑ i ∈ Finset.range (2 * b + 1), Y ^ (2 * b - i) * X ^ i
      = ∑ i ∈ Finset.range (2 * b + 1), Y ^ i * X ^ (2 * b - i) := by
    rw [← Finset.sum_range_reflect (fun i => Y ^ i * X ^ (2 * b - i)) (2 * b + 1)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have e1 : 2 * b + 1 - 1 - i = 2 * b - i := by omega
    have e2 : 2 * b - (2 * b - i) = i := by omega
    simp only [e1, e2]
  rw [h3] at h2
  linarith [h2]

theorem bound6 (k b : ℕ) (hk : 2 ≤ k) (hb : 1 ≤ b)
    (hS : ∑ i ∈ Finset.range (2 * b + 1), (2 * k - 1) ^ i * (2 * k + 1) ^ (2 * b - i)
      = (2 * k ^ 2 - 1) ^ (b + 1)) :
    (2 * b + 1) * 2 ^ b < 2 * k ^ 2 - 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have e1 : 2 * (m + 2) - 1 = 2 * m + 3 := by omega
  have e2 : 2 * (m + 2) ^ 2 - 1 = 2 * m ^ 2 + 8 * m + 7 := by
    have : 2 * (m + 2) ^ 2 = 2 * m ^ 2 + 8 * m + 8 := by ring
    omega
  rw [e1, e2] at hS
  rw [e2]
  have hlow := geom_sum_lower (2 * (m + 2) + 1) (2 * m + 3) b
  rw [hS, ← mul_pow] at hlow
  have e3 : (2 * m + 3) * (2 * (m + 2) + 1) = 2 * (2 * m ^ 2 + 8 * m + 7) + 1 := by ring
  rw [e3] at hlow
  have h1 : (2 * (2 * m ^ 2 + 8 * m + 7)) ^ b < (2 * (2 * m ^ 2 + 8 * m + 7) + 1) ^ b :=
    Nat.pow_lt_pow_left (by omega) (by omega)
  have h2 : (2 * b + 1) * (2 * (2 * m ^ 2 + 8 * m + 7)) ^ b
      < (2 * b + 1) * (2 * (2 * m ^ 2 + 8 * m + 7) + 1) ^ b :=
    Nat.mul_lt_mul_of_pos_left h1 (by omega)
  have h3 : (2 * b + 1) * 2 ^ b * (2 * m ^ 2 + 8 * m + 7) ^ b
      < (2 * m ^ 2 + 8 * m + 7) * (2 * m ^ 2 + 8 * m + 7) ^ b := by
    have h4 := lt_of_lt_of_le h2 hlow
    rw [mul_pow, pow_succ] at h4
    linarith [h4]
  exact Nat.lt_of_mul_lt_mul_right h3

theorem aux_eq_int (k b : ℕ) (hk : 2 ≤ k)
    (hS : ∑ i ∈ Finset.range (2 * b + 1), (2 * k - 1) ^ i * (2 * k + 1) ^ (2 * b - i)
      = (2 * k ^ 2 - 1) ^ (b + 1)) :
    (2 * (k : ℤ) + 1) ^ (2 * b + 1) - (2 * (k : ℤ) - 1) ^ (2 * b + 1)
      = 2 * (2 * (k : ℤ) ^ 2 - 1) ^ (b + 1) := by
  have hk1 : 1 ≤ 2 * k := by omega
  have hk2 : 1 ≤ 2 * k ^ 2 := by nlinarith
  have hid := geom_identity (2 * k - 1) (2 * k + 1) (2 * b + 1) (by omega)
  simp only [Nat.add_sub_cancel] at hid
  rw [hS] at hid
  have e3 : 2 * k + 1 - (2 * k - 1) = 2 := by omega
  rw [e3] at hid
  have hle : (2 * k - 1) ^ (2 * b + 1) ≤ (2 * k + 1) ^ (2 * b + 1) :=
    Nat.pow_le_pow_left (by omega) _
  have hz : (((2 * k ^ 2 - 1) ^ (b + 1) * 2 : ℕ) : ℤ)
      = (((2 * k + 1) ^ (2 * b + 1) - (2 * k - 1) ^ (2 * b + 1) : ℕ) : ℤ) := by
    rw [hid]
  rw [Nat.cast_sub hle] at hz
  push_cast [Nat.cast_sub hk1, Nat.cast_sub hk2] at hz
  linarith [hz]

theorem trunc_binom (t : ℤ) (n : ℕ) :
    ∃ A : ℤ, (t + 1) ^ n = 1 + n * t + (n.choose 2 : ℤ) * t ^ 2 + (n.choose 3 : ℤ) * t ^ 3 + t ^ 4 * A := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨A, hA⟩ := ih
    have c2 : (n + 1).choose 2 = n.choose 1 + n.choose 2 := Nat.choose_succ_succ n 1
    have c3 : (n + 1).choose 3 = n.choose 2 + n.choose 3 := Nat.choose_succ_succ n 2
    refine ⟨A + (n.choose 3 : ℤ) + t * A, ?_⟩
    rw [pow_succ, hA, c2, c3, Nat.choose_one_right]
    push_cast
    ring

theorem lhs_expansion (k : ℤ) (b : ℕ) :
    ∃ A : ℤ, (2 * k + 1) ^ (2 * b + 1) - (2 * k - 1) ^ (2 * b + 1)
      = 2 + 8 * (b : ℤ) * (2 * b + 1) * k ^ 2 + 16 * k ^ 4 * A := by
  obtain ⟨A1, hA1⟩ := trunc_binom (2 * k) (2 * b + 1)
  obtain ⟨A2, hA2⟩ := trunc_binom (-(2 * k)) (2 * b + 1)
  have hodd : Odd (2 * b + 1) := ⟨b, rfl⟩
  have e1 : (2 * k - 1) ^ (2 * b + 1) = -((-(2 * k) + 1) ^ (2 * b + 1)) := by
    rw [← Odd.neg_pow hodd]
    congr 1
    ring
  have c2 : ((2 * b + 1).choose 2 : ℤ) = b * (2 * b + 1) := by
    rw [Nat.choose_two_right]
    have e : (2 * b + 1) * (2 * b + 1 - 1) / 2 = b * (2 * b + 1) := by
      rw [Nat.add_sub_cancel, show (2 * b + 1) * (2 * b) = (b * (2 * b + 1)) * 2 by ring,
        Nat.mul_div_cancel _ (by norm_num)]
    rw [e]
    push_cast
    ring
  refine ⟨A1 + A2, ?_⟩
  rw [e1, hA1, hA2, c2]
  push_cast
  ring

theorem rhs_expansion (k : ℤ) (b : ℕ) (hb : Odd b) :
    ∃ D : ℤ, (2 * k ^ 2 - 1) ^ (b + 1) = 1 - 2 * ((b : ℤ) + 1) * k ^ 2 + 4 * k ^ 4 * D := by
  obtain ⟨A, hA⟩ := trunc_binom (-(2 * k ^ 2)) (b + 1)
  have heven : Even (b + 1) := hb.add_one
  have e1 : (2 * k ^ 2 - 1) ^ (b + 1) = (-(2 * k ^ 2) + 1) ^ (b + 1) := by
    rw [← Even.neg_pow heven]
    congr 1
    ring
  refine ⟨((b + 1).choose 2 : ℤ) - 2 * k ^ 2 * ((b + 1).choose 3 : ℤ) + 4 * k ^ 4 * A, ?_⟩
  rw [e1, hA]
  push_cast
  ring

theorem aux_b_odd (k : ℤ) (b : ℕ) (hk : 2 ≤ k)
    (h : (2 * k + 1) ^ (2 * b + 1) - (2 * k - 1) ^ (2 * b + 1) = 2 * (2 * k ^ 2 - 1) ^ (b + 1)) :
    Odd b := by
  rcases Nat.even_or_odd b with he | ho
  · exfalso
    obtain ⟨A, hA⟩ := lhs_expansion k b
    rw [hA] at h
    have h1 : (2 * k ^ 2 - 1) ^ (b + 1) ≡ (-1) ^ (b + 1) [ZMOD 2 * k ^ 2] := by
      apply Int.ModEq.pow
      exact Int.modEq_iff_dvd.mpr ⟨-1, by ring⟩
    rw [(he.add_one).neg_one_pow] at h1
    obtain ⟨c, hc⟩ := Int.modEq_iff_dvd.mp h1
    have h3 : (4 : ℤ) * 1 = 4 * (k ^ 2 * (-c - 2 * b * (2 * b + 1) - 4 * k ^ 2 * A)) := by
      linear_combination h - 2 * hc
    have h4 : (k ^ 2 : ℤ) ∣ 1 := ⟨_, mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) h3⟩
    have h5 := Int.le_of_dvd one_pos h4
    nlinarith
  · exact ho

theorem aux_div (k : ℤ) (b : ℕ) (hk : 2 ≤ k)
    (h : (2 * k + 1) ^ (2 * b + 1) - (2 * k - 1) ^ (2 * b + 1) = 2 * (2 * k ^ 2 - 1) ^ (b + 1)) :
    2 * k ^ 2 ∣ 4 * (b : ℤ) ^ 2 + 3 * b + 1 := by
  have hb := aux_b_odd k b hk h
  obtain ⟨A, hA⟩ := lhs_expansion k b
  obtain ⟨D, hD⟩ := rhs_expansion k b hb
  rw [hA, hD] at h
  refine ⟨D - 2 * A, ?_⟩
  have hk0 : (k : ℤ) ≠ 0 := by omega
  have h3 : (4 * k ^ 2 : ℤ) * (4 * b ^ 2 + 3 * b + 1) = (4 * k ^ 2) * (2 * k ^ 2 * (D - 2 * A)) := by
    linear_combination h
  exact mul_left_cancel₀ (mul_ne_zero (by norm_num) (pow_ne_zero 2 hk0)) h3

theorem two_pow_ge (b : ℕ) (hb : 3 ≤ b) : 2 * b + 2 ≤ 2 ^ b := by
  induction b, hb using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ]; omega

theorem aux_solution (k b : ℕ) (hk : 2 ≤ k) (hb : 1 ≤ b)
    (hS : ∑ i ∈ Finset.range (2 * b + 1), (2 * k - 1) ^ i * (2 * k + 1) ^ (2 * b - i)
      = (2 * k ^ 2 - 1) ^ (b + 1)) :
    k = 2 ∧ b = 1 := by
  have h6 := bound6 k b hk hb hS
  have hint := aux_eq_int k b hk hS
  have hkz : (2 : ℤ) ≤ k := by exact_mod_cast hk
  have hodd := aux_b_odd (k : ℤ) b hkz hint
  have hdiv := aux_div (k : ℤ) b hkz hint
  have hdiv' : 2 * k ^ 2 ∣ 4 * b ^ 2 + 3 * b + 1 := by exact_mod_cast hdiv
  have hle : 2 * k ^ 2 ≤ 4 * b ^ 2 + 3 * b + 1 := Nat.le_of_dvd (by omega) hdiv'
  have hk2 : 1 ≤ 2 * k ^ 2 := by nlinarith
  have h6' : (2 * b + 1) * 2 ^ b + 1 < 2 * k ^ 2 := by omega
  have hb2 : b ≤ 2 := by
    by_contra hc
    have h35 := two_pow_ge b (by omega)
    have h7 : (2 * b + 1) * (2 * b + 2) ≤ (2 * b + 1) * 2 ^ b := Nat.mul_le_mul_left _ h35
    nlinarith
  obtain ⟨m, hm⟩ := hodd
  have hb1 : b = 1 := by omega
  subst hb1
  have hk3 : k ≤ 2 := by nlinarith
  exact ⟨by omega, rfl⟩

theorem caseB_nontrivial (p a b r s : ℕ) (hp : p.Prime) (hodd : Odd p) (ha : 1 ≤ a)
    (hab : a = b + 1 ∨ a = b) (hrs : r * s = 2 * p + 1) (hcop : Nat.Coprime r s)
    (hr : 1 < r) (hlt : r < s) (h : s ^ (2 * b + 1) = r ^ (2 * b + 1) + 2 * p ^ a) :
    p = 7 ∧ a = 2 ∧ b = 1 ∧ r = 3 := by
  obtain ⟨hr3, hsp⟩ := nontrivial_bounds p r s hrs hr hlt
  have hb : 1 ≤ b := by
    by_contra hb0
    have hb0' : b = 0 := by omega
    subst hb0'
    simp only [mul_zero, zero_add, pow_one] at h
    exact nontrivial_b_pos p r s a hsp ha h
  have hid := geom_identity r s (2 * b + 1) hlt.le
  simp only [Nat.add_sub_cancel] at hid
  have hSu : (∑ i ∈ Finset.range (2 * b + 1), r ^ i * s ^ (2 * b - i)) * (s - r) = 2 * p ^ a := by
    rw [hid]; omega
  have hcases := s_sub_r_cases_aux p (s - r) _ a hp (by omega) hSu
  rcases hcases with ⟨h1, _⟩ | ⟨h2, hS⟩
  · exfalso
    have e : s = r + 1 := by omega
    subst e
    exact s_ne_r_add_one p r hrs
  · have e : s = r + 2 := by omega
    subst e
    obtain ⟨k, hk, hrk, hpk⟩ := k_param p r hr3 hrs
    rcases hab with rfl | rfl
    · have hS' : ∑ i ∈ Finset.range (2 * b + 1), (2 * k - 1) ^ i * (2 * k + 1) ^ (2 * b - i)
          = (2 * k ^ 2 - 1) ^ (b + 1) := by
        have e2 : r + 2 = 2 * k + 1 := by omega
        rw [← hpk, ← hrk, ← e2]
        exact hS
      obtain ⟨hk2, hb1⟩ := aux_solution k b hk hb hS'
      subst hk2
      subst hb1
      norm_num at hpk hrk
      exact ⟨hpk, rfl, rfl, hrk⟩
    · exfalso
      exact remark_2_8 p r (r + 2) _ hb hrs hS

theorem consecutive_exponents (p x y z : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : x = y + 1 ∨ y = x + 1)
    (h : p ^ x + (2 * p + 1) ^ y = z ^ 2) :
    (x, y, z) = (2, 1, p + 1) ∨ (p = 7 ∧ (x, y, z) = (4, 3, 76)) := by
  rcases parity_split x y hxy with ⟨a, b, rfl, rfl, hab⟩ | ⟨a, b, rfl, rfl, hab⟩
  · exfalso
    exact caseA_no_solution p a b z hp hodd (by omega) hab h
  · have ha : 1 ≤ a := by omega
    obtain ⟨r, s, hrs, hcop, hlt, hz, hs⟩ := caseB_split p a b z hp hodd ha h
    rcases Nat.lt_or_ge 1 r with hr | hr
    · obtain ⟨hp7, ha2, hb1, hr3⟩ := caseB_nontrivial p a b r s hp hodd ha hab hrs hcop hr hlt hs
      right
      subst hp7 ha2 hb1 hr3
      norm_num at hz
      subst hz
      norm_num
    · have hr1 : r = 1 := by
        rcases Nat.eq_zero_or_pos r with h0 | h0
        · subst h0; simp at hrs
        · omega
      subst hr1
      rw [one_mul] at hrs
      subst hrs
      rw [one_pow] at hs hz
      obtain ⟨ha1, hb0⟩ := caseB_trivial p a b hp hodd hab hs
      subst ha1 hb0
      left
      subst hz
      norm_num

end Panda2608
