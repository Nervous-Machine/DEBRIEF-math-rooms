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

/-! Lemmas N01–N37 of the planner's blueprint, in order. -/

-- N01
theorem coprime_p_q (p : ℕ) : Nat.Coprime p (2 * p + 1) :=
  (Nat.coprime_mul_right_add_right p 1 2).2 (Nat.coprime_one_right p)

-- N02
theorem lte_corollary (p : ℕ) (hp : p.Prime) (hodd : Odd p) (b : ℕ) :
    padicValNat p ((2 * p + 1) ^ (2 * b + 1) - 1) = 1 + padicValNat p (2 * b + 1) := by
  haveI := Fact.mk hp
  have h2 : 2 ≤ p := hp.two_le
  have hnd : ¬ p ∣ 2 * p + 1 := by
    intro hd
    have h1 : p ∣ 1 := (Nat.dvd_add_right (dvd_mul_left p 2)).mp hd
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have hkey := padicValNat.pow_sub_pow hodd (show 1 < 2 * p + 1 by omega)
    (show p ∣ 2 * p + 1 - 1 by
      rw [show 2 * p + 1 - 1 = 2 * p by omega]; exact dvd_mul_left p 2) hnd
    (show 2 * b + 1 ≠ 0 by omega)
  rw [Nat.one_pow, show 2 * p + 1 - 1 = 2 * p by omega] at hkey
  have hp2 : padicValNat p 2 = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro hd
    have h3 := Nat.le_of_dvd (by norm_num) hd
    have h4 := Nat.odd_iff.mp hodd
    omega
  have hmul : padicValNat p (2 * p) = padicValNat p 2 + padicValNat p p :=
    padicValNat.mul (by norm_num) hp.ne_zero
  have h3 : padicValNat p (2 * p) = 1 := by
    rw [hmul, hp2, padicValNat.self hp.one_lt]
  omega

-- N03
theorem parity_split (x y : ℕ) (hxy : x = y + 1 ∨ y = x + 1) :
    (∃ a b : ℕ, x = 2 * a + 1 ∧ y = 2 * b ∧ (b = a ∨ b = a + 1)) ∨
    (∃ a b : ℕ, x = 2 * a ∧ y = 2 * b + 1 ∧ (a = b + 1 ∨ a = b)) := by
  rcases Nat.even_or_odd' x with ⟨a, hx | hx⟩
  · right
    refine ⟨a, y / 2, hx, ?_, ?_⟩ <;> omega
  · left
    refine ⟨a, y / 2, hx, ?_, ?_⟩ <;> omega

-- N04
theorem coprime_sub_add_of_odd (u v w : ℕ) (hvu : v < u) (hw : Odd w)
    (h : (u - v) * (u + v) = w) (hcop : Nat.Coprime v w) :
    Nat.Coprime (u - v) (u + v) := by
  apply Nat.coprime_of_dvd
  intro k hk h1 h2
  have hkw : k ∣ w := by
    rw [← h]; exact Dvd.dvd.mul_right h1 (u + v)
  have hkodd : Odd k := Odd.of_dvd_nat hw hkw
  have hk2 : k ∣ 2 * v := by
    have e : u + v = (u - v) + 2 * v := by omega
    rw [e] at h2
    exact (Nat.dvd_add_right h1).mp h2
  have hkv : k ∣ v := by
    rcases (Nat.Prime.dvd_mul hk).mp hk2 with h3 | h3
    · exfalso
      have h4 := Nat.le_of_dvd (by norm_num) h3
      have h5 := hk.two_le
      have h6 := Nat.odd_iff.mp hkodd
      omega
    · exact h3
  exact hk.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hcop hkv hkw)

-- N05
theorem prime_pow_coprime_split (p m n k : ℕ) (hp : p.Prime) (h : m * n = p ^ k)
    (hc : Nat.Coprime m n) : m = 1 ∨ n = 1 := by
  obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).mp (Dvd.intro n h)
  obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow hp).mp (Dvd.intro_left (p ^ i) h)
  rcases Nat.eq_zero_or_pos i with hi0 | hi0
  · left; rw [hi0, pow_zero]
  rcases Nat.eq_zero_or_pos j with hj0 | hj0
  · right; rw [hj0, pow_zero]
  exfalso
  have h1 : p ∣ p ^ i := dvd_pow_self p hi0.ne'
  have h2 : p ∣ p ^ j := dvd_pow_self p hj0.ne'
  exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hc h1 h2)

-- N06
theorem caseA_reduce (p a b z : ℕ) (hp : p.Prime) (hodd : Odd p)
    (h : p ^ (2 * a + 1) + (2 * p + 1) ^ (2 * b) = z ^ 2) :
    p ^ (2 * a + 1) = 2 * (2 * p + 1) ^ b + 1 := by
  have hq2 : (2 * p + 1) ^ (2 * b) = ((2 * p + 1) ^ b) ^ 2 := by rw [pow_mul']
  rw [hq2] at h
  obtain ⟨q, hq⟩ : ∃ q, q = (2 * p + 1) ^ b := ⟨_, rfl⟩
  rw [← hq] at h ⊢
  have hppos : 0 < p ^ (2 * a + 1) := pow_pos hp.pos _
  have hqpos : 0 < q := by rw [hq]; exact pow_pos (by omega) b
  have hlt : q < z := by
    have h1 : q ^ 2 < z ^ 2 := by omega
    exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le z) h1
  have hfac : (z - q) * (z + q) = p ^ (2 * a + 1) := by
    obtain ⟨d, hd⟩ : ∃ d, z = q + d := ⟨z - q, by omega⟩
    rw [hd, Nat.add_sub_cancel_left]
    rw [hd] at h
    nlinarith [h]
  have hcop : Nat.Coprime q (p ^ (2 * a + 1)) := by
    rw [hq]; exact Nat.Coprime.pow b (2 * a + 1) (coprime_p_q p).symm
  have hwodd : Odd (p ^ (2 * a + 1)) := hodd.pow
  have hc := coprime_sub_add_of_odd z q _ hlt hwodd hfac hcop
  rcases prime_pow_coprime_split p _ _ _ hp hfac hc with h1 | h1
  · have hz : z = q + 1 := by omega
    rw [← hfac, h1, hz]; ring
  · exfalso; omega

-- N07
theorem caseA_mod_p (p n m : ℕ) (hp : p.Prime) (hn : 1 ≤ n)
    (h : p ^ n = 2 * (2 * p + 1) ^ m + 1) : p = 3 := by
  have hq1 : 1 ≡ 2 * p + 1 [MOD p] := (Nat.modEq_iff_dvd' (by omega)).mpr ⟨2, by omega⟩
  have hqm : 1 ≡ (2 * p + 1) ^ m [MOD p] := by
    have h1 := hq1.pow m
    rwa [Nat.one_pow] at h1
  have h3 : 2 * 1 + 1 ≡ 2 * (2 * p + 1) ^ m + 1 [MOD p] := (hqm.mul_left 2).add_right 1
  rw [← h] at h3
  have h4 : 2 * 1 + 1 ≡ 0 [MOD p] :=
    h3.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_pow_self p (by omega)))
  have h5 : p ∣ 3 := Nat.modEq_zero_iff_dvd.mp h4
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h5

-- N08
theorem three_pow_odd_mod_seven (a : ℕ) : 3 ^ (2 * a + 1) % 7 ≠ 1 := by
  have key : ∀ a : ℕ, 3 ^ (2 * a + 1) % 7 = 3 ∨ 3 ^ (2 * a + 1) % 7 = 6 ∨
      3 ^ (2 * a + 1) % 7 = 5 := by
    intro a
    induction a with
    | zero => left; norm_num
    | succ n ih =>
      have e : 3 ^ (2 * (n + 1) + 1) = 3 ^ (2 * n + 1) * 9 := by
        rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, pow_add]; norm_num
      rw [e, Nat.mul_mod]
      rcases ih with h | h | h <;> rw [h] <;> norm_num
  intro h1
  rcases key a with h | h | h <;> omega

-- N09
theorem lemma_2_3 (p a : ℕ) (hp : p.Prime) (hodd : Odd p) :
    p ^ (2 * a + 1) ≠ 2 * (2 * p + 1) ^ (a + 1) + 1 := by
  intro h
  have hp3 := caseA_mod_p p (2 * a + 1) (a + 1) hp (by omega) h
  subst hp3
  apply three_pow_odd_mod_seven a
  rw [h]
  have h7 : 7 ∣ 2 * (2 * 3 + 1) ^ (a + 1) := by
    rw [show 2 * 3 + 1 = 7 by norm_num]
    exact Dvd.dvd.mul_left (dvd_pow_self 7 (by omega)) 2
  omega

-- N10
theorem lemma_2_4 (p a : ℕ) (hp : p.Prime) (hodd : Odd p) (ha : 1 ≤ a) :
    p ^ (2 * a + 1) ≠ 2 * (2 * p + 1) ^ a + 1 := by
  intro h
  have hp3 := caseA_mod_p p (2 * a + 1) a hp (by omega) h
  subst hp3
  apply three_pow_odd_mod_seven a
  rw [h]
  have h7 : 7 ∣ 2 * (2 * 3 + 1) ^ a := by
    rw [show 2 * 3 + 1 = 7 by norm_num]
    exact Dvd.dvd.mul_left (dvd_pow_self 7 (by omega)) 2
  omega

-- N11
theorem caseA_no_solution (p a b z : ℕ) (hp : p.Prime) (hodd : Odd p) (hb : 1 ≤ b)
    (hab : b = a ∨ b = a + 1)
    (h : p ^ (2 * a + 1) + (2 * p + 1) ^ (2 * b) = z ^ 2) : False := by
  have h1 := caseA_reduce p a b z hp hodd h
  rcases hab with hab | hab
  · rw [hab] at h1
    exact lemma_2_4 p a hp hodd (by omega) h1
  · rw [hab] at h1
    exact lemma_2_3 p a hp hodd h1

-- N12
theorem caseB_split (p a b z : ℕ) (hp : p.Prime) (hodd : Odd p) (ha : 1 ≤ a)
    (h : p ^ (2 * a) + (2 * p + 1) ^ (2 * b + 1) = z ^ 2) :
    ∃ r s : ℕ, r * s = 2 * p + 1 ∧ Nat.Coprime r s ∧ r < s ∧
      z = p ^ a + r ^ (2 * b + 1) ∧ s ^ (2 * b + 1) = r ^ (2 * b + 1) + 2 * p ^ a := by
  have hpa : (p ^ a) ^ 2 = p ^ (2 * a) := by rw [← pow_mul']
  rw [← hpa] at h
  have hqpos : 0 < (2 * p + 1) ^ (2 * b + 1) := pow_pos (by omega) _
  have hpa_pos : 0 < p ^ a := pow_pos hp.pos a
  have hlt : p ^ a < z := by
    have h1 : (p ^ a) ^ 2 < z ^ 2 := by omega
    exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le z) h1
  have hfac : (z - p ^ a) * (z + p ^ a) = (2 * p + 1) ^ (2 * b + 1) := by
    obtain ⟨d, hd⟩ : ∃ d, z = p ^ a + d := ⟨z - p ^ a, by omega⟩
    rw [hd, Nat.add_sub_cancel_left]
    rw [hd] at h
    nlinarith [h]
  have hcop1 : Nat.Coprime (p ^ a) ((2 * p + 1) ^ (2 * b + 1)) :=
    Nat.Coprime.pow a (2 * b + 1) (coprime_p_q p)
  have hwodd : Odd ((2 * p + 1) ^ (2 * b + 1)) := by
    apply Odd.pow; exact ⟨p, rfl⟩
  have hc := coprime_sub_add_of_odd z (p ^ a) _ hlt hwodd hfac hcop1
  have hc' : IsUnit (gcd (z - p ^ a) (z + p ^ a)) := Nat.isUnit_iff.mpr hc
  have hc'' : IsUnit (gcd (z + p ^ a) (z - p ^ a)) := Nat.isUnit_iff.mpr hc.symm
  obtain ⟨r, hr⟩ := exists_eq_pow_of_mul_eq_pow hc' hfac
  have hfac' : (z + p ^ a) * (z - p ^ a) = (2 * p + 1) ^ (2 * b + 1) := by
    rw [mul_comm]; exact hfac
  obtain ⟨s, hs⟩ := exists_eq_pow_of_mul_eq_pow hc'' hfac'
  have hn : 2 * b + 1 ≠ 0 := by omega
  have hrs : (r * s) ^ (2 * b + 1) = (2 * p + 1) ^ (2 * b + 1) := by
    rw [mul_pow, ← hr, ← hs, hfac]
  have hrs' : r * s = 2 * p + 1 := Nat.pow_left_injective hn hrs
  have hcop_rs : Nat.Coprime r s := by
    have h1 : Nat.Coprime (r ^ (2 * b + 1)) (s ^ (2 * b + 1)) := by
      rw [← hr, ← hs]; exact hc
    exact (Nat.coprime_pow_left_iff (by omega) _ _).mp
      ((Nat.coprime_pow_right_iff (by omega) _ _).mp h1)
  have hrlts : r < s := by
    have h1 : r ^ (2 * b + 1) < s ^ (2 * b + 1) := by rw [← hr, ← hs]; omega
    exact lt_of_pow_lt_pow_left₀ _ (Nat.zero_le s) h1
  refine ⟨r, s, hrs', hcop_rs, hrlts, ?_, ?_⟩
  · omega
  · omega

-- N13
theorem pow_gt_two_mul_add_one (p b : ℕ) (hp : 3 ≤ p) (hb : 2 ≤ b) : 2 * b + 1 < p ^ b := by
  induction b, hb using Nat.le_induction with
  | base => nlinarith
  | succ n hn ih =>
    rw [pow_succ]
    have h1 := Nat.mul_le_mul_left (p ^ n) hp
    omega

-- N14
theorem prop_2_5 (p b : ℕ) (hp : p.Prime) (hodd : Odd p)
    (h : (2 * p + 1) ^ (2 * b + 1) = 2 * p ^ (b + 1) + 1) : b = 0 := by
  haveI := Fact.mk hp
  have hp3 : 3 ≤ p := by
    have h1 := hp.two_le
    have h2 := Nat.odd_iff.mp hodd
    omega
  have h1 := lte_corollary p hp hodd b
  rw [h, show 2 * p ^ (b + 1) + 1 - 1 = 2 * p ^ (b + 1) by omega] at h1
  have hmul : padicValNat p (2 * p ^ (b + 1)) = padicValNat p 2 + padicValNat p (p ^ (b + 1)) :=
    padicValNat.mul (by norm_num) (pow_ne_zero _ hp.ne_zero)
  have hp2 : padicValNat p 2 = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro hd
    have h3 := Nat.le_of_dvd (by norm_num) hd
    omega
  rw [hmul, hp2, padicValNat.prime_pow] at h1
  have hv : padicValNat p (2 * b + 1) = b := by omega
  have hdvd : p ^ b ∣ 2 * b + 1 := by
    have h2 := @pow_padicValNat_dvd p (2 * b + 1)
    rwa [hv] at h2
  have hle : p ^ b ≤ 2 * b + 1 := Nat.le_of_dvd (by omega) hdvd
  by_contra hb0
  have hb1 : 1 ≤ b := Nat.pos_of_ne_zero hb0
  rcases Nat.lt_or_ge b 2 with hb2 | hb2
  · have hb : b = 1 := by omega
    subst hb
    rw [pow_one] at hdvd
    have hd3 : p ∣ 3 := hdvd
    have hp3' : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hd3
    subst hp3'
    norm_num at h
  · have h4 := pow_gt_two_mul_add_one p b hp3 hb2
    omega

-- N15
theorem lemma_2_6 (p b : ℕ) (hp : p.Prime) :
    (2 * p + 1) ^ (2 * b + 1) ≠ 2 * p ^ b + 1 := by
  intro h
  have h1 : p ^ b ≤ (2 * p + 1) ^ b := Nat.pow_le_pow_left (by omega) b
  have h2 : (2 * p + 1) ^ b ≤ (2 * p + 1) ^ (2 * b) := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : (2 * p + 1) ^ (2 * b + 1) = (2 * p + 1) ^ (2 * b) * (2 * p + 1) := pow_succ _ _
  have h4 : 1 ≤ p ^ b := Nat.one_le_pow _ _ hp.pos
  have h5 := hp.two_le
  rw [h3] at h
  have h6 : p ^ b * (2 * p + 1) ≤ (2 * p + 1) ^ (2 * b) * (2 * p + 1) :=
    Nat.mul_le_mul_right _ (h1.trans h2)
  have h7 : p ^ b * 5 ≤ p ^ b * (2 * p + 1) := Nat.mul_le_mul_left _ (by omega)
  omega

-- N16
theorem caseB_trivial (p a b : ℕ) (hp : p.Prime) (hodd : Odd p) (hab : a = b + 1 ∨ a = b)
    (h : (2 * p + 1) ^ (2 * b + 1) = 1 + 2 * p ^ a) : a = 1 ∧ b = 0 := by
  rcases hab with hab | hab
  · rw [hab] at h
    have hb := prop_2_5 p b hp hodd (by rw [h]; ring)
    omega
  · rw [hab] at h
    exfalso
    apply lemma_2_6 p b hp
    rw [h]; ring

-- N17
theorem nontrivial_bounds (p r s : ℕ) (hrs : r * s = 2 * p + 1) (hr : 1 < r) (hlt : r < s) :
    3 ≤ r ∧ s < p := by
  have hodd : Odd (r * s) := by rw [hrs]; exact ⟨p, rfl⟩
  have hr_odd : Odd r := (Nat.odd_mul.mp hodd).1
  have hr3 : 3 ≤ r := by
    have h1 := Nat.odd_iff.mp hr_odd
    omega
  refine ⟨hr3, ?_⟩
  have h3 : 3 * s ≤ r * s := Nat.mul_le_mul_right s hr3
  omega

-- N18
theorem geom_identity (r s n : ℕ) (hrs : r ≤ s) :
    (∑ i ∈ Finset.range n, r ^ i * s ^ (n - 1 - i)) * (s - r) = s ^ n - r ^ n :=
  geom_sum₂_mul_of_le hrs n

-- N19
theorem geom_sum_modEq (r s n : ℕ) (hrs : r ≤ s) :
    (∑ i ∈ Finset.range n, r ^ i * s ^ (n - 1 - i)) ≡ n * r ^ (n - 1) [MOD (s - r)] := by
  have hsr : s ≡ r [MOD (s - r)] := Nat.modEq_sub hrs
  have hterm : ∀ i ∈ Finset.range n,
      r ^ i * s ^ (n - 1 - i) % (s - r) = r ^ (n - 1) % (s - r) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have h1 : r ^ i * s ^ (n - 1 - i) ≡ r ^ i * r ^ (n - 1 - i) [MOD (s - r)] :=
      (hsr.pow (n - 1 - i)).mul_left (r ^ i)
    rw [← pow_add, show i + (n - 1 - i) = n - 1 by omega] at h1
    exact h1
  unfold Nat.ModEq
  rw [Finset.sum_nat_mod, Finset.sum_congr rfl hterm, ← Finset.sum_nat_mod, Finset.sum_const,
    Finset.card_range, smul_eq_mul]

-- N20
theorem lemma_2_7 (p r s a b : ℕ) (hp : p.Prime) (hodd : Odd p) (hcop : Nat.Coprime r s)
    (hr : 3 ≤ r) (hlt : r < s) (hsp : s < p)
    (h : (∑ i ∈ Finset.range (2 * b + 1), r ^ i * s ^ (2 * b - i)) * (s - r) = 2 * p ^ a) :
    Nat.Coprime (s - r) (∑ i ∈ Finset.range (2 * b + 1), r ^ i * s ^ (2 * b - i)) := by
  have hmod := geom_sum_modEq r s (2 * b + 1) hlt.le
  simp only [Nat.add_sub_cancel] at hmod
  apply Nat.coprime_of_dvd
  intro k hk hkd hkS
  have hk2 : k ∣ 2 * p ^ a := by
    rw [← h]; exact Dvd.dvd.mul_left hkd _
  have hkS' : k ∣ (2 * b + 1) * r ^ (2 * b) := (hmod.dvd_iff hkd).mp hkS
  rcases (Nat.Prime.dvd_mul hk).mp hk2 with hk2' | hkp
  · have hk2'' : k = 2 := (Nat.prime_dvd_prime_iff_eq hk Nat.prime_two).mp hk2'
    rw [hk2''] at hkd hkS'
    have hr_odd : Odd r := by
      rcases Nat.even_or_odd r with hre | hro
      · exfalso
        have hse : Even s := by
          have e : s = (s - r) + r := by omega
          rw [e]; exact (even_iff_two_dvd.mpr hkd).add hre
        have h1 := Nat.eq_one_of_dvd_coprimes hcop (even_iff_two_dvd.mp hre) (even_iff_two_dvd.mp hse)
        omega
      · exact hro
    have hodd' : Odd ((2 * b + 1) * r ^ (2 * b)) := Odd.mul ⟨b, rfl⟩ hr_odd.pow
    exact (Nat.not_even_iff_odd.mpr hodd') (even_iff_two_dvd.mpr hkS')
  · have hkp' : k = p := (Nat.prime_dvd_prime_iff_eq hk hp).mp (hk.dvd_of_dvd_pow hkp)
    have h1 : k ≤ s - r := Nat.le_of_dvd (by omega) hkd
    omega

-- N21
theorem nontrivial_b_pos (p r s a : ℕ) (hsp : s < p) (ha : 1 ≤ a)
    (h : s = r + 2 * p ^ a) : False := by
  have h1 := Nat.le_self_pow (show a ≠ 0 by omega) p
  omega

-- N22
theorem s_sub_r_cases (p u v a : ℕ) (hp : p.Prime) (hodd : Odd p) (hcop : Nat.Coprime u v)
    (hv : 3 ≤ v) (hu : u < p) (h : v * u = 2 * p ^ a) :
    (u = 1 ∧ v = 2 * p ^ a) ∨ (u = 2 ∧ v = p ^ a) := by
  have hpa : 0 < p ^ a := pow_pos hp.pos a
  have hu0 : 0 < u := by
    rcases Nat.eq_zero_or_pos u with h0 | h0
    · rw [h0, mul_zero] at h; omega
    · exact h0
  have hcpu : Nat.Coprime p u := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    have h1 := Nat.le_of_dvd hu0 hd
    omega
  have hcpau : Nat.Coprime (p ^ a) u := Nat.Coprime.pow_left a hcpu
  have hu2 : u ∣ 2 := by
    have h1 : u ∣ 2 * p ^ a := Dvd.intro_left v h
    exact Nat.Coprime.dvd_of_dvd_mul_right hcpau.symm h1
  rcases (Nat.dvd_prime Nat.prime_two).mp hu2 with h1 | h1
  · left
    refine ⟨h1, ?_⟩
    rw [h1, mul_one] at h
    exact h
  · right
    refine ⟨h1, ?_⟩
    rw [h1] at h
    omega

-- N23
theorem s_ne_r_add_one (p r : ℕ) (h : r * (r + 1) = 2 * p + 1) : False := by
  have h1 := Nat.even_mul_succ_self r
  rw [h, Nat.even_iff] at h1
  omega

-- N24
theorem k_param (p r : ℕ) (hr : 3 ≤ r) (h : r * (r + 2) = 2 * p + 1) :
    ∃ k : ℕ, 2 ≤ k ∧ r = 2 * k - 1 ∧ p = 2 * k ^ 2 - 1 := by
  have hodd : Odd r := by
    have h1 : Odd (r * (r + 2)) := by rw [h]; exact ⟨p, rfl⟩
    exact (Nat.odd_mul.mp h1).1
  obtain ⟨k, hk⟩ := hodd
  refine ⟨k + 1, by omega, by omega, ?_⟩
  subst hk
  have e1 : 2 * (k + 1) ^ 2 = 2 * k ^ 2 + 4 * k + 2 := by ring
  have e2 : (2 * k + 1) * (2 * k + 1 + 2) = 4 * k ^ 2 + 8 * k + 3 := by ring
  omega

-- N25
theorem remark_2_8 (p r s b : ℕ) (hb : 1 ≤ b) (hrs : r * s = 2 * p + 1)
    (hS : ∑ i ∈ Finset.range (2 * b + 1), r ^ i * s ^ (2 * b - i) = p ^ b) : False := by
  have hterm : r ^ b * s ^ (2 * b - b) ≤ ∑ i ∈ Finset.range (2 * b + 1), r ^ i * s ^ (2 * b - i) :=
    Finset.single_le_sum (f := fun i => r ^ i * s ^ (2 * b - i)) (fun i _ => Nat.zero_le _)
      (Finset.mem_range.mpr (by omega))
  rw [show 2 * b - b = b by omega, ← mul_pow, hrs, hS] at hterm
  have h1 : p ^ b < (2 * p + 1) ^ b := Nat.pow_lt_pow_left (by omega) (by omega)
  omega

-- N26
theorem amgm_pair (X Y b i : ℕ) (hi : i ≤ 2 * b) :
    2 * (Y ^ b * X ^ b) ≤ Y ^ i * X ^ (2 * b - i) + Y ^ (2 * b - i) * X ^ i := by
  rcases le_total i b with h | h
  · obtain ⟨t, rfl⟩ : ∃ t, b = i + t := ⟨b - i, by omega⟩
    rw [show 2 * (i + t) - i = i + 2 * t by omega]
    have key := two_mul_le_add_sq (X ^ t) (Y ^ t)
    have h2 := Nat.mul_le_mul_left (Y ^ i * X ^ i) key
    calc 2 * (Y ^ (i + t) * X ^ (i + t)) = Y ^ i * X ^ i * (2 * X ^ t * Y ^ t) := by ring
      _ ≤ Y ^ i * X ^ i * ((X ^ t) ^ 2 + (Y ^ t) ^ 2) := h2
      _ = Y ^ i * X ^ (i + 2 * t) + Y ^ (i + 2 * t) * X ^ i := by ring
  · obtain ⟨t, rfl⟩ : ∃ t, i = b + t := ⟨i - b, by omega⟩
    rw [show 2 * b - (b + t) = b - t by omega]
    obtain ⟨u, rfl⟩ : ∃ u, b = t + u := ⟨b - t, by omega⟩
    rw [show t + u - t = u by omega]
    have key := two_mul_le_add_sq (X ^ t) (Y ^ t)
    have h2 := Nat.mul_le_mul_left (Y ^ u * X ^ u) key
    calc 2 * (Y ^ (t + u) * X ^ (t + u)) = Y ^ u * X ^ u * (2 * X ^ t * Y ^ t) := by ring
      _ ≤ Y ^ u * X ^ u * ((X ^ t) ^ 2 + (Y ^ t) ^ 2) := h2
      _ = Y ^ (t + u + t) * X ^ u + Y ^ u * X ^ (t + u + t) := by ring

-- N27
theorem geom_sum_lower (X Y b : ℕ) :
    (2 * b + 1) * (Y ^ b * X ^ b) ≤ ∑ i ∈ Finset.range (2 * b + 1), Y ^ i * X ^ (2 * b - i) := by
  have hrefl : ∑ i ∈ Finset.range (2 * b + 1), Y ^ (2 * b - i) * X ^ i
      = ∑ i ∈ Finset.range (2 * b + 1), Y ^ i * X ^ (2 * b - i) := by
    have h1 := Finset.sum_range_reflect (fun i => Y ^ i * X ^ (2 * b - i)) (2 * b + 1)
    rw [← h1]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have e1 : 2 * b + 1 - 1 - i = 2 * b - i := by omega
    have e2 : 2 * b - (2 * b - i) = i := by omega
    simp only [e1, e2]
  have hsum : ∑ i ∈ Finset.range (2 * b + 1), 2 * (Y ^ b * X ^ b)
      ≤ ∑ i ∈ Finset.range (2 * b + 1), (Y ^ i * X ^ (2 * b - i) + Y ^ (2 * b - i) * X ^ i) := by
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mem_range] at hi
    exact amgm_pair X Y b i (by omega)
  rw [Finset.sum_add_distrib, hrefl, Finset.sum_const, Finset.card_range, smul_eq_mul] at hsum
  have e : (2 * b + 1) * (2 * (Y ^ b * X ^ b)) = 2 * ((2 * b + 1) * (Y ^ b * X ^ b)) := by ring
  omega

-- N28
theorem bound6 (k b : ℕ) (hk : 2 ≤ k) (hb : 1 ≤ b)
    (hS : ∑ i ∈ Finset.range (2 * b + 1), (2 * k - 1) ^ i * (2 * k + 1) ^ (2 * b - i)
      = (2 * k ^ 2 - 1) ^ (b + 1)) :
    (2 * b + 1) * 2 ^ b < 2 * k ^ 2 - 1 := by
  have h1 := geom_sum_lower (2 * k + 1) (2 * k - 1) b
  rw [hS, ← mul_pow] at h1
  have hk2 : 4 ≤ k ^ 2 := by nlinarith
  have hk1 : 1 ≤ 2 * k := by omega
  have hk4 : 1 ≤ 4 * k ^ 2 := by omega
  have hprod : (2 * k - 1) * (2 * k + 1) = 4 * k ^ 2 - 1 := by
    zify [hk1, hk4]
    ring
  rw [hprod] at h1
  obtain ⟨m, hm⟩ : ∃ m, m = 2 * k ^ 2 - 1 := ⟨_, rfl⟩
  rw [← hm] at h1 ⊢
  have hm2 : 2 * m < 4 * k ^ 2 - 1 := by omega
  have h2 : (2 * m) ^ b < (4 * k ^ 2 - 1) ^ b := Nat.pow_lt_pow_left hm2 (by omega)
  have h3 : (2 * b + 1) * (2 * m) ^ b < (2 * b + 1) * (4 * k ^ 2 - 1) ^ b :=
    Nat.mul_lt_mul_of_pos_left h2 (by omega)
  have h4 : (2 * b + 1) * (2 * m) ^ b < m ^ (b + 1) := lt_of_lt_of_le h3 h1
  rw [mul_pow, pow_succ] at h4
  have h5 : ((2 * b + 1) * 2 ^ b) * m ^ b < m * m ^ b := by
    calc ((2 * b + 1) * 2 ^ b) * m ^ b = (2 * b + 1) * (2 ^ b * m ^ b) := by ring
      _ < m ^ b * m := h4
      _ = m * m ^ b := by ring
  exact Nat.lt_of_mul_lt_mul_right h5

-- N29
theorem aux_eq_int (k b : ℕ) (hk : 2 ≤ k)
    (hS : ∑ i ∈ Finset.range (2 * b + 1), (2 * k - 1) ^ i * (2 * k + 1) ^ (2 * b - i)
      = (2 * k ^ 2 - 1) ^ (b + 1)) :
    (2 * (k : ℤ) + 1) ^ (2 * b + 1) - (2 * (k : ℤ) - 1) ^ (2 * b + 1)
      = 2 * (2 * (k : ℤ) ^ 2 - 1) ^ (b + 1) := by
  have hle : 2 * k - 1 ≤ 2 * k + 1 := by omega
  have hid := geom_identity (2 * k - 1) (2 * k + 1) (2 * b + 1) hle
  simp only [Nat.add_sub_cancel] at hid
  rw [hS, show 2 * k + 1 - (2 * k - 1) = 2 by omega] at hid
  have hpow : (2 * k - 1) ^ (2 * b + 1) ≤ (2 * k + 1) ^ (2 * b + 1) := Nat.pow_le_pow_left hle _
  have hk1 : 1 ≤ 2 * k := by omega
  have hk2 : 1 ≤ 2 * k ^ 2 := by nlinarith
  zify [hpow, hk1, hk2] at hid
  linarith

-- N30
theorem trunc_binom (t : ℤ) (n : ℕ) :
    ∃ A : ℤ, (t + 1) ^ n = 1 + n * t + (n.choose 2 : ℤ) * t ^ 2 + (n.choose 3 : ℤ) * t ^ 3 + t ^ 4 * A := by
  induction n with
  | zero =>
    refine ⟨0, ?_⟩
    rw [show Nat.choose 0 2 = 0 by decide, show Nat.choose 0 3 = 0 by decide]
    simp
  | succ n ih =>
    obtain ⟨A, hA⟩ := ih
    have c2 : (n + 1).choose 2 = n.choose 2 + n := by
      show (n + 1).choose (1 + 1) = n.choose (1 + 1) + n
      rw [Nat.choose_succ_succ', Nat.choose_one_right, Nat.add_comm n]
    have c3 : (n + 1).choose 3 = n.choose 3 + n.choose 2 := by
      show (n + 1).choose (2 + 1) = n.choose (2 + 1) + n.choose 2
      rw [Nat.choose_succ_succ', Nat.add_comm (n.choose 2)]
    refine ⟨A + (n.choose 3 : ℤ) + t * A, ?_⟩
    rw [pow_succ, hA, c2, c3]
    push_cast
    ring

-- N31
theorem lhs_expansion (k : ℤ) (b : ℕ) :
    ∃ A : ℤ, (2 * k + 1) ^ (2 * b + 1) - (2 * k - 1) ^ (2 * b + 1)
      = 2 + 8 * (b : ℤ) * (2 * b + 1) * k ^ 2 + 16 * k ^ 4 * A := by
  obtain ⟨A₁, h₁⟩ := trunc_binom (2 * k) (2 * b + 1)
  obtain ⟨A₂, h₂⟩ := trunc_binom (-(2 * k)) (2 * b + 1)
  have hc2 : (2 * b + 1).choose 2 = b * (2 * b + 1) := by
    rw [Nat.choose_two_right, Nat.add_sub_cancel]
    have e : (2 * b + 1) * (2 * b) = b * (2 * b + 1) * 2 := by ring
    rw [e, Nat.mul_div_cancel _ (by norm_num)]
  have hodd : Odd (2 * b + 1) := ⟨b, rfl⟩
  have hneg : (2 * k - 1) ^ (2 * b + 1) = -((-(2 * k) + 1) ^ (2 * b + 1)) := by
    have e : (2 * k - 1) = -(-(2 * k) + 1) := by ring
    rw [e, Odd.neg_pow hodd]
  refine ⟨A₁ + A₂, ?_⟩
  rw [hneg, h₁, h₂, hc2]
  push_cast
  ring

-- N32
theorem rhs_expansion (k : ℤ) (b : ℕ) (hb : Odd b) :
    ∃ D : ℤ, (2 * k ^ 2 - 1) ^ (b + 1) = 1 - 2 * ((b : ℤ) + 1) * k ^ 2 + 4 * k ^ 4 * D := by
  obtain ⟨A, hA⟩ := trunc_binom (-(2 * k ^ 2)) (b + 1)
  have heven : Even (b + 1) := hb.add_one
  have hneg : (2 * k ^ 2 - 1) ^ (b + 1) = (-(2 * k ^ 2) + 1) ^ (b + 1) := by
    have e : (2 * k ^ 2 - 1) = -(-(2 * k ^ 2) + 1) := by ring
    rw [e, Even.neg_pow heven]
  refine ⟨((b + 1).choose 2 : ℤ) - 2 * ((b + 1).choose 3 : ℤ) * k ^ 2 + 4 * k ^ 4 * A, ?_⟩
  rw [hneg, hA]
  push_cast
  ring

-- N33
theorem aux_b_odd (k : ℤ) (b : ℕ) (hk : 2 ≤ k)
    (h : (2 * k + 1) ^ (2 * b + 1) - (2 * k - 1) ^ (2 * b + 1) = 2 * (2 * k ^ 2 - 1) ^ (b + 1)) :
    Odd b := by
  rcases Nat.even_or_odd b with hb | hb
  · exfalso
    obtain ⟨A, hA⟩ := lhs_expansion k b
    have hodd : Odd (b + 1) := hb.add_one
    have hmod : (2 * k ^ 2 - 1) ^ (b + 1) ≡ (-1) ^ (b + 1) [ZMOD 2 * k ^ 2] := by
      apply Int.ModEq.pow
      exact Int.modEq_iff_dvd.mpr ⟨-1, by ring⟩
    rw [hodd.neg_one_pow] at hmod
    obtain ⟨E, hE⟩ := Int.modEq_iff_dvd.mp hmod
    have h4 : (2 * k ^ 2 : ℤ) ∣ 4 :=
      ⟨-(2 * E) - 4 * (b : ℤ) * (2 * (b : ℤ) + 1) - 8 * k ^ 2 * A, by linear_combination -hA + h - 2 * hE⟩
    have h5 := Int.le_of_dvd (by norm_num) h4
    nlinarith
  · exact hb

-- N34
theorem aux_div (k : ℤ) (b : ℕ) (hk : 2 ≤ k)
    (h : (2 * k + 1) ^ (2 * b + 1) - (2 * k - 1) ^ (2 * b + 1) = 2 * (2 * k ^ 2 - 1) ^ (b + 1)) :
    2 * k ^ 2 ∣ 4 * (b : ℤ) ^ 2 + 3 * b + 1 := by
  have hb := aux_b_odd k b hk h
  obtain ⟨A, hA⟩ := lhs_expansion k b
  obtain ⟨D, hD⟩ := rhs_expansion k b hb
  refine ⟨D - 2 * A, ?_⟩
  have hk0 : k ^ 2 ≠ 0 := pow_ne_zero 2 (by omega)
  have h4 : (4 : ℤ) ≠ 0 := by norm_num
  have key : 4 * k ^ 2 * (4 * (b : ℤ) ^ 2 + 3 * b + 1) = 4 * k ^ 2 * (2 * k ^ 2 * (D - 2 * A)) := by
    linear_combination -hA + h + 2 * hD
  exact mul_left_cancel₀ (mul_ne_zero h4 hk0) key

-- N35
theorem two_pow_ge (b : ℕ) (hb : 3 ≤ b) : 2 * b + 2 ≤ 2 ^ b := by
  induction b, hb using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ]
    omega

-- N36
theorem aux_solution (k b : ℕ) (hk : 2 ≤ k) (hb : 1 ≤ b)
    (hS : ∑ i ∈ Finset.range (2 * b + 1), (2 * k - 1) ^ i * (2 * k + 1) ^ (2 * b - i)
      = (2 * k ^ 2 - 1) ^ (b + 1)) :
    k = 2 ∧ b = 1 := by
  have hint := aux_eq_int k b hk hS
  have hk' : (2 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have hodd := aux_b_odd (k : ℤ) b hk' hint
  have hdiv := aux_div (k : ℤ) b hk' hint
  have hle : (2 : ℤ) * (k : ℤ) ^ 2 ≤ 4 * (b : ℤ) ^ 2 + 3 * b + 1 :=
    Int.le_of_dvd (by positivity) hdiv
  have hle' : 2 * k ^ 2 ≤ 4 * b ^ 2 + 3 * b + 1 := by exact_mod_cast hle
  have hb6 := bound6 k b hk hb hS
  have hk2 : 4 ≤ k ^ 2 := by nlinarith
  have hb6' : (2 * b + 1) * 2 ^ b + 1 < 2 * k ^ 2 := by omega
  have hb2 : b ≤ 2 := by
    by_contra hcon
    push_neg at hcon
    have h35 := two_pow_ge b (by omega)
    have h36 : (2 * b + 1) * (2 * b + 2) ≤ (2 * b + 1) * 2 ^ b := Nat.mul_le_mul_left _ h35
    nlinarith
  have hb1 : b = 1 := by
    have h1 := Nat.odd_iff.mp hodd
    omega
  subst hb1
  refine ⟨?_, rfl⟩
  have hk3 : k ≤ 2 := by nlinarith
  omega

-- N37
theorem caseB_nontrivial (p a b r s : ℕ) (hp : p.Prime) (hodd : Odd p) (ha : 1 ≤ a)
    (hab : a = b + 1 ∨ a = b) (hrs : r * s = 2 * p + 1) (hcop : Nat.Coprime r s)
    (hr : 1 < r) (hlt : r < s) (h : s ^ (2 * b + 1) = r ^ (2 * b + 1) + 2 * p ^ a) :
    p = 7 ∧ a = 2 ∧ b = 1 ∧ r = 3 := by
  obtain ⟨hr3, hsp⟩ := nontrivial_bounds p r s hrs hr hlt
  rcases Nat.eq_zero_or_pos b with hb0 | hbpos
  · exfalso
    subst hb0
    rw [show 2 * 0 + 1 = 1 by norm_num, pow_one, pow_one] at h
    exact nontrivial_b_pos p r s a hsp ha h
  have hb1 : 1 ≤ b := hbpos
  have hid := geom_identity r s (2 * b + 1) hlt.le
  simp only [Nat.add_sub_cancel] at hid
  rw [h, Nat.add_sub_cancel_left] at hid
  have hcopS := lemma_2_7 p r s a b hp hodd hcop hr3 hlt hsp hid
  have hS3 : 3 ≤ ∑ i ∈ Finset.range (2 * b + 1), r ^ i * s ^ (2 * b - i) := by
    have h0 : r ^ 0 * s ^ (2 * b - 0) ≤ ∑ i ∈ Finset.range (2 * b + 1), r ^ i * s ^ (2 * b - i) :=
      Finset.single_le_sum (f := fun i => r ^ i * s ^ (2 * b - i)) (fun i _ => Nat.zero_le _)
        (Finset.mem_range.mpr (by omega))
    rw [pow_zero, one_mul, Nat.sub_zero] at h0
    have h1 : s ≤ s ^ (2 * b) := by
      calc s = s ^ 1 := (pow_one s).symm
        _ ≤ s ^ (2 * b) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hcases := s_sub_r_cases p (s - r) _ a hp hodd hcopS hS3 (by omega) hid
  rcases hcases with ⟨h1, _⟩ | ⟨h2, hSp⟩
  · exfalso
    have hs : s = r + 1 := by omega
    have hrs' : r * (r + 1) = 2 * p + 1 := by rw [← hs]; exact hrs
    exact s_ne_r_add_one p r hrs'
  · have hs : s = r + 2 := by omega
    have hrs' : r * (r + 2) = 2 * p + 1 := by rw [← hs]; exact hrs
    obtain ⟨k, hk2, hrk, hpk⟩ := k_param p r hr3 hrs'
    have hsk : s = 2 * k + 1 := by omega
    rcases hab with hab | hab
    · rw [hab] at hSp
      rw [hrk, hsk, hpk] at hSp
      obtain ⟨hk, hb⟩ := aux_solution k b hk2 hb1 hSp
      subst hk
      subst hb
      norm_num at hpk hrk
      omega
    · exfalso
      rw [hab] at hSp
      exact remark_2_8 p r s b hb1 hrs hSp


/-- Theorem 1.1 of arXiv:2608.18608v2: the only positive solutions of `p^x + (2p+1)^y = z^2` with `p` an odd
prime and `|x - y| = 1` are `(x, y, z) = (2, 1, p+1)`, and, when `p = 7`, also `(4, 3, 76)`. -/
theorem consecutive_exponents (p x y z : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : x = y + 1 ∨ y = x + 1)
    (h : p ^ x + (2 * p + 1) ^ y = z ^ 2) :
    (x, y, z) = (2, 1, p + 1) ∨ (p = 7 ∧ (x, y, z) = (4, 3, 76)) := by
  rcases parity_split x y hxy with ⟨a, b, hxa, hyb, hab⟩ | ⟨a, b, hxa, hyb, hab⟩
  · exfalso
    subst hxa
    subst hyb
    exact caseA_no_solution p a b z hp hodd (by omega) hab h
  · subst hxa
    subst hyb
    have ha : 1 ≤ a := by omega
    obtain ⟨r, s, hrs, hcop, hlt, hz, hpow⟩ := caseB_split p a b z hp hodd ha h
    rcases Nat.lt_or_ge 1 r with hr1 | hr1
    · obtain ⟨hp7, ha2, hb1, hr3⟩ := caseB_nontrivial p a b r s hp hodd ha hab hrs hcop hr1 hlt hpow
      right
      subst hp7
      subst ha2
      subst hb1
      subst hr3
      rw [hz]
      norm_num
    · have hr : r = 1 := by
        rcases Nat.eq_zero_or_pos r with h0 | h0
        · rw [h0, zero_mul] at hrs; omega
        · omega
      subst hr
      rw [one_pow] at hpow hz
      have hs : s = 2 * p + 1 := by omega
      rw [hs] at hpow
      obtain ⟨ha1, hb0⟩ := caseB_trivial p a b hp hodd hab hpow
      subst ha1
      subst hb0
      left
      rw [hz]
      norm_num

end Panda2608
