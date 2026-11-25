module

public import Mathlib

@[expose] public section

namespace Panda2608

-- N01
theorem coprime_p_q (p : ℕ) : Nat.Coprime p (2 * p + 1) := by
  have h1 : Nat.Coprime p 1 := Nat.coprime_one_right p
  exact (Nat.coprime_mul_right_add_right p 1 2).2 h1

-- helper: a prime cannot divide both members of a coprime pair
theorem prime_not_dvd_both {k m n : ℕ} (hk : k.Prime) (hc : Nat.Coprime m n)
    (h1 : k ∣ m) (h2 : k ∣ n) : False := by
  have hg : Nat.gcd m n = 1 := hc
  have h3 : k ∣ Nat.gcd m n := Nat.dvd_gcd h1 h2
  rw [hg] at h3
  exact hk.one_lt.ne' (Nat.dvd_one.mp h3)

-- N02 (helpers lte_aux, val_two_mul)
theorem lte_aux (p : ℕ) (hp : p.Prime) (hodd : Odd p) (b : ℕ) :
    padicValNat p ((2 * p + 1) ^ (2 * b + 1) - 1) = padicValNat p (2 * p) + padicValNat p (2 * b + 1) := by
  haveI := Fact.mk hp
  have h1 : 1 < 2 * p + 1 := by have := hp.two_le; omega
  have h2 : p ∣ 2 * p + 1 - 1 := by
    rw [show 2 * p + 1 - 1 = 2 * p by omega]
    exact Dvd.intro_left 2 rfl
  have h3 : ¬ p ∣ 2 * p + 1 := (Nat.Prime.coprime_iff_not_dvd hp).1 (coprime_p_q p)
  have key := padicValNat.pow_sub_pow (n := 2 * b + 1) hodd h1 h2 h3 (by omega)
  rw [one_pow] at key
  rw [key, show 2 * p + 1 - 1 = 2 * p by omega]

theorem val_two_mul (p : ℕ) (hp : p.Prime) (hodd : Odd p) : padicValNat p (2 * p) = 1 := by
  haveI := Fact.mk hp
  have hp2 : 2 < p := by
    have := hp.two_le
    have := Nat.odd_iff.mp hodd
    omega
  have hnd : ¬ p ∣ 2 := fun hd => by
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  have hm : padicValNat p (2 * p) = padicValNat p 2 + padicValNat p p :=
    padicValNat.mul (p := p) (a := 2) (b := p) (by norm_num) hp.ne_zero
  rw [hm, padicValNat.eq_zero_of_not_dvd hnd]
  have hs : padicValNat p p = 1 := by
    first
      | exact padicValNat.self hp.one_lt
      | exact padicValNat_self
      | simp
  omega

theorem lte_corollary (p : ℕ) (hp : p.Prime) (hodd : Odd p) (b : ℕ) :
    padicValNat p ((2 * p + 1) ^ (2 * b + 1) - 1) = 1 + padicValNat p (2 * b + 1) := by
  rw [lte_aux p hp hodd b, val_two_mul p hp hodd]

-- N03
theorem parity_split (x y : ℕ) (hxy : x = y + 1 ∨ y = x + 1) :
    (∃ a b : ℕ, x = 2 * a + 1 ∧ y = 2 * b ∧ (b = a ∨ b = a + 1)) ∨
    (∃ a b : ℕ, x = 2 * a ∧ y = 2 * b + 1 ∧ (a = b + 1 ∨ a = b)) := by
  obtain ⟨a, ha⟩ := Nat.even_or_odd' x
  rcases ha with ha | ha
  · right
    refine ⟨a, (y - 1) / 2, ha, ?_, ?_⟩ <;> omega
  · left
    refine ⟨a, y / 2, ha, ?_, ?_⟩ <;> omega

-- N04
theorem coprime_sub_add_of_odd (u v w : ℕ) (hvu : v < u) (hw : Odd w)
    (h : (u - v) * (u + v) = w) (hcop : Nat.Coprime v w) :
    Nat.Coprime (u - v) (u + v) := by
  apply Nat.coprime_of_dvd
  intro k hk h1 h2
  have h2v : k ∣ 2 * v := by
    have h3 : k ∣ u + v - (u - v) := by
      first
        | exact Nat.dvd_sub h2 h1
        | exact Nat.dvd_sub' h2 h1
    rwa [show u + v - (u - v) = 2 * v by omega] at h3
  have hkw : k ∣ w := by
    rw [← h]
    exact Dvd.dvd.mul_right h1 (u + v)
  have hkodd : Odd k := Odd.of_dvd_nat hw hkw
  have hk2 : ¬ 2 ∣ k := by
    have := Nat.odd_iff.mp hkodd
    omega
  have hcop2 : Nat.Coprime k 2 := ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hk2).symm
  have hkv : k ∣ v := by
    first
      | exact hcop2.dvd_of_dvd_mul_left h2v
      | exact hcop2.dvd_of_dvd_mul_right (by rwa [mul_comm] at h2v)
  exact prime_not_dvd_both hk hcop hkv hkw

-- N05
theorem prime_pow_coprime_split (p m n k : ℕ) (hp : p.Prime) (h : m * n = p ^ k)
    (hc : Nat.Coprime m n) : m = 1 ∨ n = 1 := by
  obtain ⟨i, hi, hmi⟩ := (Nat.dvd_prime_pow hp).1 (Dvd.intro n h)
  obtain ⟨j, hj, hnj⟩ := (Nat.dvd_prime_pow hp).1 (Dvd.intro_left m h)
  rcases Nat.eq_zero_or_pos i with hi0 | hi0
  · left
    rw [hmi, hi0, pow_zero]
  rcases Nat.eq_zero_or_pos j with hj0 | hj0
  · right
    rw [hnj, hj0, pow_zero]
  exfalso
  have h1 : p ∣ m := by
    rw [hmi]
    exact dvd_pow_self p (by omega)
  have h2 : p ∣ n := by
    rw [hnj]
    exact dvd_pow_self p (by omega)
  exact prime_not_dvd_both hp hc h1 h2

-- N06
theorem caseA_reduce (p a b z : ℕ) (hp : p.Prime) (hodd : Odd p)
    (h : p ^ (2 * a + 1) + (2 * p + 1) ^ (2 * b) = z ^ 2) :
    p ^ (2 * a + 1) = 2 * (2 * p + 1) ^ b + 1 := by
  have hQ : (2 * p + 1) ^ (2 * b) = ((2 * p + 1) ^ b) ^ 2 := by
    first
      | ring
      | rw [pow_mul']
      | (rw [← pow_mul, mul_comm])
  rw [hQ] at h
  have hpos : 0 < p ^ (2 * a + 1) := pow_pos hp.pos _
  have hQpos : 0 < (2 * p + 1) ^ b := pow_pos (by omega) _
  have hlt : (2 * p + 1) ^ b < z := by
    by_contra hcon
    push_neg at hcon
    have := Nat.pow_le_pow_left hcon 2
    omega
  have hprod : (z - (2 * p + 1) ^ b) * (z + (2 * p + 1) ^ b) = p ^ (2 * a + 1) := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hlt.le
    rw [hd, Nat.add_sub_cancel_left]
    have e : ((2 * p + 1) ^ b + d) ^ 2
        = ((2 * p + 1) ^ b) ^ 2 + d * ((2 * p + 1) ^ b + d + (2 * p + 1) ^ b) := by ring
    rw [hd, e] at h
    omega
  have hcop1 : Nat.Coprime ((2 * p + 1) ^ b) (p ^ (2 * a + 1)) :=
    Nat.Coprime.pow b (2 * a + 1) (coprime_p_q p).symm
  have hcop2 := coprime_sub_add_of_odd z ((2 * p + 1) ^ b) (p ^ (2 * a + 1)) hlt
    (Odd.pow hodd) hprod hcop1
  rcases prime_pow_coprime_split p _ _ (2 * a + 1) hp hprod hcop2 with h1 | h1
  · rw [← hprod, h1, one_mul]
    omega
  · omega

-- N07
theorem caseA_mod_p (p n m : ℕ) (hp : p.Prime) (hn : 1 ≤ n)
    (h : p ^ n = 2 * (2 * p + 1) ^ m + 1) : p = 3 := by
  have h1 : p ∣ 2 * (2 * p + 1) ^ m + 1 := by
    rw [← h]
    exact dvd_pow_self p (by omega)
  have h2 : p ∣ (2 * p + 1) ^ m - 1 := by
    have h3 := Nat.sub_dvd_pow_sub_pow (2 * p + 1) 1 m
    rw [one_pow, show 2 * p + 1 - 1 = 2 * p by omega] at h3
    exact (Dvd.intro_left 2 rfl).trans h3
  have hq : 1 ≤ (2 * p + 1) ^ m := Nat.one_le_pow _ _ (by omega)
  have h3 : p ∣ 3 := by
    have h4 : p ∣ 2 * ((2 * p + 1) ^ m - 1) := Dvd.dvd.mul_left h2 2
    have h5 : p ∣ 2 * (2 * p + 1) ^ m + 1 - 2 * ((2 * p + 1) ^ m - 1) := by
      first
        | exact Nat.dvd_sub h1 h4
        | exact Nat.dvd_sub' h1 h4
    rwa [show 2 * (2 * p + 1) ^ m + 1 - 2 * ((2 * p + 1) ^ m - 1) = 3 by omega] at h5
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3

-- N08
theorem three_pow_odd_mod_seven (a : ℕ) : 3 ^ (2 * a + 1) % 7 ≠ 1 := by
  have key : ∀ n : ℕ, 3 ^ (2 * n + 1) % 7 = 3 ∨ 3 ^ (2 * n + 1) % 7 = 6 ∨
      3 ^ (2 * n + 1) % 7 = 5 := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      have e : 3 ^ (2 * (n + 1) + 1) = 3 ^ (2 * n + 1) * 9 := by
        rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 2 by omega, pow_add]
        norm_num
      rw [e, Nat.mul_mod]
      rcases ih with h | h | h <;> rw [h] <;> norm_num
  have := key a
  omega

-- N09
theorem lemma_2_3 (p a : ℕ) (hp : p.Prime) (hodd : Odd p) :
    p ^ (2 * a + 1) ≠ 2 * (2 * p + 1) ^ (a + 1) + 1 := by
  intro h
  have hp3 : p = 3 := caseA_mod_p p (2 * a + 1) (a + 1) hp (by omega) h
  subst hp3
  have h' : 3 ^ (2 * a + 1) = 2 * 7 ^ (a + 1) + 1 := h
  obtain ⟨c, hc⟩ : 7 ∣ 7 ^ (a + 1) := dvd_pow_self 7 (by omega)
  rw [hc] at h'
  have := three_pow_odd_mod_seven a
  omega

-- N10
theorem lemma_2_4 (p a : ℕ) (hp : p.Prime) (hodd : Odd p) (ha : 1 ≤ a) :
    p ^ (2 * a + 1) ≠ 2 * (2 * p + 1) ^ a + 1 := by
  intro h
  have hp3 : p = 3 := caseA_mod_p p (2 * a + 1) a hp (by omega) h
  subst hp3
  have h' : 3 ^ (2 * a + 1) = 2 * 7 ^ a + 1 := h
  obtain ⟨c, hc⟩ : 7 ∣ 7 ^ a := dvd_pow_self 7 (by omega)
  rw [hc] at h'
  have := three_pow_odd_mod_seven a
  omega

-- N11
theorem caseA_no_solution (p a b z : ℕ) (hp : p.Prime) (hodd : Odd p) (hb : 1 ≤ b)
    (hab : b = a ∨ b = a + 1)
    (h : p ^ (2 * a + 1) + (2 * p + 1) ^ (2 * b) = z ^ 2) : False := by
  have h6 := caseA_reduce p a b z hp hodd h
  rcases hab with hab | hab
  · subst hab
    exact lemma_2_4 p b hp hodd hb h6
  · subst hab
    exact lemma_2_3 p a hp hodd h6

-- N12
theorem caseB_split (p a b z : ℕ) (hp : p.Prime) (hodd : Odd p) (ha : 1 ≤ a)
    (h : p ^ (2 * a) + (2 * p + 1) ^ (2 * b + 1) = z ^ 2) :
    ∃ r s : ℕ, r * s = 2 * p + 1 ∧ Nat.Coprime r s ∧ r < s ∧
      z = p ^ a + r ^ (2 * b + 1) ∧ s ^ (2 * b + 1) = r ^ (2 * b + 1) + 2 * p ^ a := by
  have hP : p ^ (2 * a) = (p ^ a) ^ 2 := by
    first
      | ring
      | rw [pow_mul']
      | (rw [← pow_mul, mul_comm])
  rw [hP] at h
  have hPpos : 0 < p ^ a := pow_pos hp.pos _
  have hqpos : 0 < (2 * p + 1) ^ (2 * b + 1) := pow_pos (by omega) _
  have hlt : p ^ a < z := by
    by_contra hcon
    push_neg at hcon
    have := Nat.pow_le_pow_left hcon 2
    omega
  have hprod : (z - p ^ a) * (z + p ^ a) = (2 * p + 1) ^ (2 * b + 1) := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hlt.le
    rw [hd, Nat.add_sub_cancel_left]
    have e : (p ^ a + d) ^ 2 = (p ^ a) ^ 2 + d * (p ^ a + d + p ^ a) := by ring
    rw [hd, e] at h
    omega
  have hcop1 : Nat.Coprime (p ^ a) ((2 * p + 1) ^ (2 * b + 1)) :=
    Nat.Coprime.pow a (2 * b + 1) (coprime_p_q p)
  have hodd' : Odd ((2 * p + 1) ^ (2 * b + 1)) := Odd.pow (odd_two_mul_add_one p)
  have hcop2 := coprime_sub_add_of_odd z (p ^ a) _ hlt hodd' hprod hcop1
  have hu : IsUnit (gcd (z - p ^ a) (z + p ^ a)) := by
    have h1 : Nat.gcd (z - p ^ a) (z + p ^ a) = 1 := hcop2
    have h2 : gcd (z - p ^ a) (z + p ^ a) = 1 := by
      first
        | exact h1
        | (rw [gcd_eq_nat_gcd]; exact h1)
        | (rw [Nat.gcd_eq_nat_gcd]; exact h1)
    rw [h2]
    exact isUnit_one
  obtain ⟨r, hr⟩ := exists_eq_pow_of_mul_eq_pow hu hprod
  have hu' : IsUnit (gcd (z + p ^ a) (z - p ^ a)) := by
    have h1 : Nat.gcd (z + p ^ a) (z - p ^ a) = 1 := hcop2.symm
    have h2 : gcd (z + p ^ a) (z - p ^ a) = 1 := by
      first
        | exact h1
        | (rw [gcd_eq_nat_gcd]; exact h1)
        | (rw [Nat.gcd_eq_nat_gcd]; exact h1)
    rw [h2]
    exact isUnit_one
  have hprod' : (z + p ^ a) * (z - p ^ a) = (2 * p + 1) ^ (2 * b + 1) := by
    rw [mul_comm]
    exact hprod
  obtain ⟨s, hs⟩ := exists_eq_pow_of_mul_eq_pow hu' hprod'
  have hn : 2 * b + 1 ≠ 0 := by omega
  have hrs : r * s = 2 * p + 1 := by
    apply Nat.pow_left_injective hn
    show (r * s) ^ (2 * b + 1) = (2 * p + 1) ^ (2 * b + 1)
    rw [mul_pow, ← hr, ← hs, hprod]
  refine ⟨r, s, hrs, ?_, ?_, ?_, ?_⟩
  · have hc : Nat.Coprime (r ^ (2 * b + 1)) (s ^ (2 * b + 1)) := by
      rw [← hr, ← hs]
      exact hcop2
    have hc2 : Nat.Coprime (r ^ (2 * b + 1)) s := (Nat.coprime_pow_right_iff (by omega) _ _).1 hc
    exact (Nat.coprime_pow_left_iff (by omega) _ _).1 hc2
  · have h1 : r ^ (2 * b + 1) < s ^ (2 * b + 1) := by
      rw [← hr, ← hs]
      omega
    by_contra hcon
    push_neg at hcon
    have := Nat.pow_le_pow_left hcon (2 * b + 1)
    omega
  · omega
  · omega

-- N13
theorem pow_gt_two_mul_add_one (p b : ℕ) (hp : 3 ≤ p) (hb : 2 ≤ b) : 2 * b + 1 < p ^ b := by
  induction b, hb using Nat.le_induction with
  | base =>
    have := Nat.pow_le_pow_left hp 2
    norm_num at this ⊢
    omega
  | succ n hn ih =>
    rw [pow_succ]
    have := Nat.mul_le_mul_left (p ^ n) hp
    omega

-- N14
theorem prop_2_5 (p b : ℕ) (hp : p.Prime) (hodd : Odd p)
    (h : (2 * p + 1) ^ (2 * b + 1) = 2 * p ^ (b + 1) + 1) : b = 0 := by
  haveI := Fact.mk hp
  have hp2 : 2 < p := by
    have := hp.two_le
    have := Nat.odd_iff.mp hodd
    omega
  have h1 : (2 * p + 1) ^ (2 * b + 1) - 1 = 2 * p ^ (b + 1) := by omega
  have h2 := lte_corollary p hp hodd b
  rw [h1] at h2
  have hnd : ¬ p ∣ 2 := fun hd => by
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  have hm : padicValNat p (2 * p ^ (b + 1)) = padicValNat p 2 + padicValNat p (p ^ (b + 1)) :=
    padicValNat.mul (p := p) (a := 2) (b := p ^ (b + 1)) (by norm_num) (pow_ne_zero _ hp.ne_zero)
  have hpp : padicValNat p (p ^ (b + 1)) = b + 1 := padicValNat.prime_pow (b + 1)
  rw [hm, hpp, padicValNat.eq_zero_of_not_dvd hnd] at h2
  have h3 : padicValNat p (2 * b + 1) = b := by omega
  by_contra hb
  have hb1 : 1 ≤ b := Nat.pos_of_ne_zero hb
  have h4 : p ^ padicValNat p (2 * b + 1) ∣ 2 * b + 1 := pow_padicValNat_dvd
  rw [h3] at h4
  have h5 : p ^ b ≤ 2 * b + 1 := Nat.le_of_dvd (by omega) h4
  rcases Nat.lt_or_ge b 2 with hb2 | hb2
  · have hb1' : b = 1 := by omega
    subst hb1'
    have h6 : p ∣ 3 := by
      rw [pow_one] at h4
      exact h4
    have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h6
    subst hp3
    norm_num at h
  · have := pow_gt_two_mul_add_one p b (by omega) hb2
    omega

-- N15
theorem lemma_2_6 (p b : ℕ) (hp : p.Prime) :
    (2 * p + 1) ^ (2 * b + 1) ≠ 2 * p ^ b + 1 := by
  intro h
  have h2 := hp.two_le
  have h1 : p ^ b ≤ (2 * p + 1) ^ b := Nat.pow_le_pow_left (by omega) b
  have h3 : 1 ≤ p ^ b := Nat.one_le_pow _ _ hp.pos
  have h4 : (2 * p + 1) ^ (2 * b + 1)
      = (2 * p + 1) ^ b * (2 * p + 1) ^ b * (2 * p + 1) := by ring
  rw [h4] at h
  have h5 : p ^ b * 1 * 5 ≤ (2 * p + 1) ^ b * (2 * p + 1) ^ b * (2 * p + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul h1 h3) (by omega)
  omega

-- N16
theorem caseB_trivial (p a b : ℕ) (hp : p.Prime) (hodd : Odd p) (hab : a = b + 1 ∨ a = b)
    (h : (2 * p + 1) ^ (2 * b + 1) = 1 + 2 * p ^ a) : a = 1 ∧ b = 0 := by
  rcases hab with hab | hab
  · subst hab
    have := prop_2_5 p b hp hodd (by omega)
    omega
  · rw [hab] at h
    exact absurd (by omega) (lemma_2_6 p b hp)

end Panda2608
