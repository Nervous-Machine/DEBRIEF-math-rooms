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
  have h2 : 2 ≤ p := hp.two_le
  have h1 : p ^ b ≤ (2 * p + 1) ^ b := Nat.pow_le_pow_left (by omega) b
  have h3 : 1 ≤ p ^ b := Nat.one_le_pow b p hp.pos
  have h4 : (2 * p + 1) ^ (2 * b + 1)
      = (2 * p + 1) ^ b * (2 * p + 1) ^ b * (2 * p + 1) := by
    first
      | (rw [show 2 * b + 1 = b + b + 1 by omega, pow_succ, pow_add])
      | ring
  rw [h4] at h
  have h6 : p ^ b * 1 ≤ (2 * p + 1) ^ b * (2 * p + 1) ^ b := Nat.mul_le_mul h1 (h3.trans h1)
  have h7 : 5 ≤ 2 * p + 1 := by omega
  have h5 : p ^ b * 1 * 5 ≤ (2 * p + 1) ^ b * (2 * p + 1) ^ b * (2 * p + 1) :=
    Nat.mul_le_mul h6 h7
  first
    | omega
    | nlinarith

-- N16
theorem caseB_trivial (p a b : ℕ) (hp : p.Prime) (hodd : Odd p) (hab : a = b + 1 ∨ a = b)
    (h : (2 * p + 1) ^ (2 * b + 1) = 1 + 2 * p ^ a) : a = 1 ∧ b = 0 := by
  rcases hab with hab | hab
  · subst hab
    have := prop_2_5 p b hp hodd (by omega)
    omega
  · rw [hab] at h
    exact absurd (by omega) (lemma_2_6 p b hp)

-- N17
theorem nontrivial_bounds (p r s : ℕ) (hrs : r * s = 2 * p + 1) (hr : 1 < r) (hlt : r < s) :
    3 ≤ r ∧ s < p := by
  have hr3 : 3 ≤ r := by
    rcases Nat.lt_or_ge r 3 with h | h
    · have h2 : r = 2 := by omega
      subst h2
      omega
    · exact h
  refine ⟨hr3, ?_⟩
  have := Nat.mul_le_mul_right s hr3
  omega

-- N18
theorem geom_identity (r s n : ℕ) (hrs : r ≤ s) :
    (∑ i ∈ Finset.range n, r ^ i * s ^ (n - 1 - i)) * (s - r) = s ^ n - r ^ n :=
  geom_sum₂_mul_of_le hrs n

-- N19
theorem geom_sum_modEq (r s n : ℕ) (hrs : r ≤ s) :
    (∑ i ∈ Finset.range n, r ^ i * s ^ (n - 1 - i)) ≡ n * r ^ (n - 1) [MOD (s - r)] := by
  have hterm : ∀ i ∈ Finset.range n,
      r ^ i * s ^ (n - 1 - i) % (s - r) = r ^ (n - 1) % (s - r) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have h1 : s ^ (n - 1 - i) ≡ r ^ (n - 1 - i) [MOD (s - r)] := (Nat.modEq_sub hrs).pow _
    have h2 : r ^ i * s ^ (n - 1 - i) ≡ r ^ i * r ^ (n - 1 - i) [MOD (s - r)] :=
      Nat.ModEq.mul_left _ h1
    rw [← pow_add, show i + (n - 1 - i) = n - 1 by omega] at h2
    exact h2
  show (∑ i ∈ Finset.range n, r ^ i * s ^ (n - 1 - i)) % (s - r) = (n * r ^ (n - 1)) % (s - r)
  rw [Finset.sum_nat_mod, Finset.sum_congr rfl hterm]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
  first
    | exact Nat.ModEq.mul_left n (Nat.mod_modEq _ _)
    | simp [Nat.mul_mod, Nat.mod_mod]

-- N20
theorem lemma_2_7 (p r s a b : ℕ) (hp : p.Prime) (hodd : Odd p) (hcop : Nat.Coprime r s)
    (hr : 3 ≤ r) (hlt : r < s) (hsp : s < p)
    (h : (∑ i ∈ Finset.range (2 * b + 1), r ^ i * s ^ (2 * b - i)) * (s - r) = 2 * p ^ a) :
    Nat.Coprime (s - r) (∑ i ∈ Finset.range (2 * b + 1), r ^ i * s ^ (2 * b - i)) := by
  have hmod : (∑ i ∈ Finset.range (2 * b + 1), r ^ i * s ^ (2 * b - i))
      ≡ (2 * b + 1) * r ^ (2 * b) [MOD (s - r)] := by
    have h0 := geom_sum_modEq r s (2 * b + 1) hlt.le
    simp only [Nat.add_sub_cancel] at h0
    exact h0
  apply Nat.coprime_of_dvd
  intro k hk hkm hkS
  have hk1 : k ∣ (2 * b + 1) * r ^ (2 * b) := (Nat.ModEq.dvd_iff hmod hkm).1 hkS
  have hk2 : k ∣ 2 * p ^ a := by
    rw [← h]
    exact Dvd.dvd.mul_left hkm _
  rcases (Nat.Prime.dvd_mul hk).1 hk1 with h1 | h1
  · rcases (Nat.Prime.dvd_mul hk).1 hk2 with h2 | h2
    · have hk2' : k = 2 := (Nat.prime_dvd_prime_iff_eq hk Nat.prime_two).1 h2
      subst hk2'
      omega
    · have hkp : k = p := (Nat.prime_dvd_prime_iff_eq hk hp).1 (hk.dvd_of_dvd_pow h2)
      subst hkp
      have := Nat.le_of_dvd (by omega) hkm
      omega
  · have hkr : k ∣ r := hk.dvd_of_dvd_pow h1
    have hks : k ∣ s := by
      have h3 := Nat.dvd_add hkm hkr
      rwa [Nat.sub_add_cancel hlt.le] at h3
    exact prime_not_dvd_both hk hcop hkr hks

-- N21
theorem nontrivial_b_pos (p r s a : ℕ) (hsp : s < p) (ha : 1 ≤ a)
    (h : s = r + 2 * p ^ a) : False := by
  have := Nat.le_self_pow (by omega : a ≠ 0) p
  omega

-- N22
theorem s_sub_r_cases (p u v a : ℕ) (hp : p.Prime) (hodd : Odd p) (hcop : Nat.Coprime u v)
    (hv : 3 ≤ v) (hu : u < p) (h : v * u = 2 * p ^ a) :
    (u = 1 ∧ v = 2 * p ^ a) ∨ (u = 2 ∧ v = p ^ a) := by
  have hu0 : 0 < u := by
    rcases Nat.eq_zero_or_pos u with h0 | h0
    · subst h0
      have : 0 < p ^ a := pow_pos hp.pos a
      omega
    · exact h0
  have hpu : ¬ p ∣ u := fun hd => by
    have := Nat.le_of_dvd hu0 hd
    omega
  have hcu : Nat.Coprime u (p ^ a) :=
    Nat.Coprime.pow_right a ((Nat.Prime.coprime_iff_not_dvd hp).2 hpu).symm
  have hu2 : u ∣ 2 := by
    have h1 : u ∣ 2 * p ^ a := Dvd.intro_left v h
    exact hcu.dvd_of_dvd_mul_right h1
  have hu2' : u ≤ 2 := Nat.le_of_dvd (by norm_num) hu2
  rcases (show u = 1 ∨ u = 2 by omega) with h1 | h1
  · left
    subst h1
    omega
  · right
    subst h1
    omega

-- N23
theorem s_ne_r_add_one (p r : ℕ) (h : r * (r + 1) = 2 * p + 1) : False := by
  obtain ⟨c, hc⟩ := Nat.even_mul_succ_self r
  omega

-- N24
theorem k_param (p r : ℕ) (hr : 3 ≤ r) (h : r * (r + 2) = 2 * p + 1) :
    ∃ k : ℕ, 2 ≤ k ∧ r = 2 * k - 1 ∧ p = 2 * k ^ 2 - 1 := by
  have hodd : Odd (r * (r + 2)) := by
    rw [h]
    exact odd_two_mul_add_one p
  have hr_odd : Odd r := (Nat.odd_mul.1 hodd).1
  obtain ⟨m, hm⟩ := hr_odd
  subst hm
  refine ⟨m + 1, by omega, by omega, ?_⟩
  have e1 : (2 * m + 1) * (2 * m + 1 + 2) = 4 * (m * m) + 8 * m + 3 := by ring
  have e2 : (m + 1) ^ 2 = m * m + 2 * m + 1 := by ring
  omega

-- N25
theorem remark_2_8 (p r s b : ℕ) (hb : 1 ≤ b) (hrs : r * s = 2 * p + 1)
    (hS : ∑ i ∈ Finset.range (2 * b + 1), r ^ i * s ^ (2 * b - i) = p ^ b) : False := by
  have hmem : b ∈ Finset.range (2 * b + 1) := Finset.mem_range.2 (by omega)
  have h1 : r ^ b * s ^ (2 * b - b) ≤ ∑ i ∈ Finset.range (2 * b + 1), r ^ i * s ^ (2 * b - i) :=
    Finset.single_le_sum (f := fun i => r ^ i * s ^ (2 * b - i)) (fun i _ => Nat.zero_le _) hmem
  rw [hS, show 2 * b - b = b by omega, ← mul_pow, hrs] at h1
  have h2 : p ^ b < (2 * p + 1) ^ b := Nat.pow_lt_pow_left (by omega) (by omega)
  omega

-- N26 (helpers two_mul_le_sq_add_sq, amgm_pair_aux)
theorem two_mul_le_sq_add_sq (u v : ℕ) : 2 * (u * v) ≤ u * u + v * v := by
  rcases le_total u v with h | h
  · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le h
    have e1 : u * (u + e) = u * u + u * e := by ring
    have e2 : (u + e) * (u + e) = u * u + 2 * (u * e) + e * e := by ring
    omega
  · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le h
    have e1 : (v + e) * v = v * v + v * e := by ring
    have e2 : (v + e) * (v + e) = v * v + 2 * (v * e) + e * e := by ring
    omega

theorem amgm_pair_aux (X Y b i : ℕ) (hi : i ≤ b) :
    2 * (Y ^ b * X ^ b) ≤ Y ^ i * X ^ (2 * b - i) + Y ^ (2 * b - i) * X ^ i := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [show 2 * (i + d) - i = i + 2 * d by omega]
  have key := two_mul_le_sq_add_sq (X ^ d) (Y ^ d)
  have e2 : Y ^ (i + d) * X ^ (i + d) = (Y ^ i * X ^ i) * (Y ^ d * X ^ d) := by ring
  have e3 : Y ^ i * X ^ (i + 2 * d) + Y ^ (i + 2 * d) * X ^ i
      = (Y ^ i * X ^ i) * (X ^ d * X ^ d + Y ^ d * Y ^ d) := by ring
  rw [e2, e3]
  calc 2 * (Y ^ i * X ^ i * (Y ^ d * X ^ d))
      = (Y ^ i * X ^ i) * (2 * (X ^ d * Y ^ d)) := by ring
    _ ≤ (Y ^ i * X ^ i) * (X ^ d * X ^ d + Y ^ d * Y ^ d) := Nat.mul_le_mul_left _ key

theorem amgm_pair (X Y b i : ℕ) (hi : i ≤ 2 * b) :
    2 * (Y ^ b * X ^ b) ≤ Y ^ i * X ^ (2 * b - i) + Y ^ (2 * b - i) * X ^ i := by
  rcases le_total i b with h | h
  · exact amgm_pair_aux X Y b i h
  · have h1 := amgm_pair_aux X Y b (2 * b - i) (by omega)
    rw [show 2 * b - (2 * b - i) = i by omega] at h1
    rw [add_comm]
    exact h1

-- N27
theorem geom_sum_lower (X Y b : ℕ) :
    (2 * b + 1) * (Y ^ b * X ^ b) ≤ ∑ i ∈ Finset.range (2 * b + 1), Y ^ i * X ^ (2 * b - i) := by
  have hrefl : ∑ i ∈ Finset.range (2 * b + 1), Y ^ (2 * b - i) * X ^ i
      = ∑ i ∈ Finset.range (2 * b + 1), Y ^ i * X ^ (2 * b - i) := by
    rw [← Finset.sum_range_reflect (fun i => Y ^ i * X ^ (2 * b - i)) (2 * b + 1)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    show Y ^ (2 * b - i) * X ^ i = Y ^ (2 * b + 1 - 1 - i) * X ^ (2 * b - (2 * b + 1 - 1 - i))
    rw [show 2 * b + 1 - 1 - i = 2 * b - i by omega, show 2 * b - (2 * b - i) = i by omega]
  have hpair : ∀ i ∈ Finset.range (2 * b + 1),
      2 * (Y ^ b * X ^ b) ≤ Y ^ i * X ^ (2 * b - i) + Y ^ (2 * b - i) * X ^ i := by
    intro i hi
    rw [Finset.mem_range] at hi
    exact amgm_pair X Y b i (by omega)
  have hsum := Finset.sum_le_sum hpair
  rw [Finset.sum_add_distrib, hrefl] at hsum
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hsum
  have e : (2 * b + 1) * (2 * (Y ^ b * X ^ b)) = 2 * ((2 * b + 1) * (Y ^ b * X ^ b)) := by ring
  rw [e] at hsum
  omega

-- N28 (helper bound6_aux)
theorem bound6_aux (M b : ℕ) (hb : 1 ≤ b) (h1 : (2 * b + 1) * (2 * M + 1) ^ b ≤ M ^ b * M) :
    (2 * b + 1) * 2 ^ b < M := by
  have h3 : (2 * M) ^ b < (2 * M + 1) ^ b := Nat.pow_lt_pow_left (by omega) (by omega)
  rw [mul_pow] at h3
  have h4 : (2 * b + 1) * (2 ^ b * M ^ b) < (2 * b + 1) * (2 * M + 1) ^ b :=
    mul_lt_mul_of_pos_left h3 (by omega)
  by_contra hcon
  push_neg at hcon
  have h5 : M ^ b * M ≤ M ^ b * ((2 * b + 1) * 2 ^ b) := Nat.mul_le_mul_left _ hcon
  have e : M ^ b * ((2 * b + 1) * 2 ^ b) = (2 * b + 1) * (2 ^ b * M ^ b) := by ring
  rw [e] at h5
  omega

theorem bound6 (k b : ℕ) (hk : 2 ≤ k) (hb : 1 ≤ b)
    (hS : ∑ i ∈ Finset.range (2 * b + 1), (2 * k - 1) ^ i * (2 * k + 1) ^ (2 * b - i)
      = (2 * k ^ 2 - 1) ^ (b + 1)) :
    (2 * b + 1) * 2 ^ b < 2 * k ^ 2 - 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hM : 2 * (j + 1) ^ 2 - 1 = 2 * (j * j) + 4 * j + 1 := by
    have e : (j + 1) ^ 2 = j * j + 2 * j + 1 := by ring
    omega
  have hr : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
  rw [hM] at hS ⊢
  rw [hr] at hS
  have h27 := geom_sum_lower (2 * (j + 1) + 1) (2 * j + 1) b
  rw [hS] at h27
  have hA : (2 * j + 1) ^ b * (2 * (j + 1) + 1) ^ b
      = (2 * (2 * (j * j) + 4 * j + 1) + 1) ^ b := by
    rw [← mul_pow]
    congr 1
    ring
  rw [hA, pow_succ (2 * (j * j) + 4 * j + 1) b] at h27
  exact bound6_aux (2 * (j * j) + 4 * j + 1) b hb h27

-- N29
theorem aux_eq_int (k b : ℕ) (hk : 2 ≤ k)
    (hS : ∑ i ∈ Finset.range (2 * b + 1), (2 * k - 1) ^ i * (2 * k + 1) ^ (2 * b - i)
      = (2 * k ^ 2 - 1) ^ (b + 1)) :
    (2 * (k : ℤ) + 1) ^ (2 * b + 1) - (2 * (k : ℤ) - 1) ^ (2 * b + 1)
      = 2 * (2 * (k : ℤ) ^ 2 - 1) ^ (b + 1) := by
  have hg := geom_identity (2 * k - 1) (2 * k + 1) (2 * b + 1) (by omega)
  simp only [Nat.add_sub_cancel] at hg
  rw [hS, show 2 * k + 1 - (2 * k - 1) = 2 by omega] at hg
  have hle : (2 * k - 1) ^ (2 * b + 1) ≤ (2 * k + 1) ^ (2 * b + 1) :=
    Nat.pow_le_pow_left (by omega) _
  have hk1 : 1 ≤ k ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h1 : 1 ≤ 2 * k := by omega
  have h2 : 1 ≤ 2 * k ^ 2 := by omega
  have hz : (((2 * k ^ 2 - 1) ^ (b + 1) * 2 : ℕ) : ℤ)
      = (((2 * k + 1) ^ (2 * b + 1) - (2 * k - 1) ^ (2 * b + 1) : ℕ) : ℤ) := by
    rw [hg]
  push_cast [Nat.cast_sub hle, Nat.cast_sub h1, Nat.cast_sub h2] at hz
  first
    | linarith
    | linear_combination -1 * hz
    | linear_combination hz

-- N30 (helpers choose_succ_two, choose_succ_three)
theorem choose_succ_two (n : ℕ) : (n + 1).choose 2 = n.choose 2 + n := by
  have h := Nat.choose_succ_succ' n 1
  rw [Nat.choose_one_right] at h
  have h2 : (n + 1).choose 2 = n + n.choose 2 := h
  omega

theorem choose_succ_three (n : ℕ) : (n + 1).choose 3 = n.choose 3 + n.choose 2 := by
  have h : (n + 1).choose 3 = n.choose 2 + n.choose 3 := Nat.choose_succ_succ' n 2
  omega

theorem trunc_binom (t : ℤ) (n : ℕ) :
    ∃ A : ℤ, (t + 1) ^ n = 1 + n * t + (n.choose 2 : ℤ) * t ^ 2 + (n.choose 3 : ℤ) * t ^ 3
      + t ^ 4 * A := by
  induction n with
  | zero =>
    refine ⟨0, ?_⟩
    have c2 : Nat.choose 0 2 = 0 := by decide
    have c3 : Nat.choose 0 3 = 0 := by decide
    simp [c2, c3]
  | succ n ih =>
    obtain ⟨A, hA⟩ := ih
    refine ⟨A + (n.choose 3 : ℤ) + t * A, ?_⟩
    rw [choose_succ_two, choose_succ_three, pow_succ (t + 1) n, hA]
    push_cast
    ring

-- N31 (helper choose_two_odd)
theorem choose_two_odd (b : ℕ) : (2 * b + 1).choose 2 = b * (2 * b + 1) := by
  rw [Nat.choose_two_right]
  have e1 : (2 * b + 1) * (2 * b + 1 - 1) = 4 * (b * b) + 2 * b := by
    rw [show 2 * b + 1 - 1 = 2 * b by omega]
    ring
  have e2 : b * (2 * b + 1) = 2 * (b * b) + b := by ring
  omega

theorem lhs_expansion (k : ℤ) (b : ℕ) :
    ∃ A : ℤ, (2 * k + 1) ^ (2 * b + 1) - (2 * k - 1) ^ (2 * b + 1)
      = 2 + 8 * (b : ℤ) * (2 * b + 1) * k ^ 2 + 16 * k ^ 4 * A := by
  obtain ⟨A₁, h₁⟩ := trunc_binom (2 * k) (2 * b + 1)
  obtain ⟨A₂, h₂⟩ := trunc_binom (-(2 * k)) (2 * b + 1)
  have hodd : Odd (2 * b + 1) := odd_two_mul_add_one b
  have hneg : (2 * k - 1) ^ (2 * b + 1) = - (-(2 * k) + 1) ^ (2 * b + 1) := by
    have e : -(2 * k) + 1 = -(2 * k - 1) := by ring
    rw [e, hodd.neg_pow, neg_neg]
  have hc : ((2 * b + 1).choose 2 : ℤ) = (b : ℤ) * (2 * b + 1) := by
    rw [choose_two_odd]
    push_cast
    ring
  refine ⟨A₁ + A₂, ?_⟩
  rw [hneg, h₁, h₂, hc]
  push_cast
  ring

-- N32
theorem rhs_expansion (k : ℤ) (b : ℕ) (hb : Odd b) :
    ∃ D : ℤ, (2 * k ^ 2 - 1) ^ (b + 1) = 1 - 2 * ((b : ℤ) + 1) * k ^ 2 + 4 * k ^ 4 * D := by
  obtain ⟨A, hA⟩ := trunc_binom (-(2 * k ^ 2)) (b + 1)
  have heven : Even (b + 1) := hb.add_one
  have hneg : (2 * k ^ 2 - 1) ^ (b + 1) = (-(2 * k ^ 2) + 1) ^ (b + 1) := by
    have e : -(2 * k ^ 2) + 1 = -(2 * k ^ 2 - 1) := by ring
    rw [e, heven.neg_pow]
  refine ⟨((b + 1).choose 2 : ℤ) - 2 * ((b + 1).choose 3 : ℤ) * k ^ 2 + 4 * k ^ 4 * A, ?_⟩
  rw [hneg, hA]
  push_cast
  ring

-- N33
theorem aux_b_odd (k : ℤ) (b : ℕ) (hk : 2 ≤ k)
    (h : (2 * k + 1) ^ (2 * b + 1) - (2 * k - 1) ^ (2 * b + 1) = 2 * (2 * k ^ 2 - 1) ^ (b + 1)) :
    Odd b := by
  by_contra hb
  have heven : Even b := Nat.not_odd_iff_even.mp hb
  have hodd1 : Odd (b + 1) := heven.add_one
  obtain ⟨A, hA⟩ := lhs_expansion k b
  have hdvd := Odd.add_dvd_pow_add_pow (2 * k ^ 2 - 1) 1 hodd1
  rw [one_pow, sub_add_cancel] at hdvd
  obtain ⟨E, hE⟩ := hdvd
  have h4 : (2 * k ^ 2) ∣ 4 :=
    ⟨2 * E - 4 * b * (2 * b + 1) - 8 * k ^ 2 * A, by linear_combination 2 * hE - hA + h⟩
  have h5 : 2 * k ^ 2 ≤ 4 := Int.le_of_dvd (by norm_num) h4
  nlinarith [mul_le_mul hk hk (by norm_num : (0:ℤ) ≤ 2) (by omega : (0:ℤ) ≤ k)]

-- N34
theorem aux_div (k : ℤ) (b : ℕ) (hk : 2 ≤ k)
    (h : (2 * k + 1) ^ (2 * b + 1) - (2 * k - 1) ^ (2 * b + 1) = 2 * (2 * k ^ 2 - 1) ^ (b + 1)) :
    2 * k ^ 2 ∣ 4 * (b : ℤ) ^ 2 + 3 * b + 1 := by
  have hb := aux_b_odd k b hk h
  obtain ⟨A, hA⟩ := lhs_expansion k b
  obtain ⟨D, hD⟩ := rhs_expansion k b hb
  refine ⟨D - 2 * A, ?_⟩
  have hk0 : (4 * k ^ 2 : ℤ) ≠ 0 := by
    have h2 : (0:ℤ) < k ^ 2 := pow_pos (by omega) 2
    omega
  apply mul_left_cancel₀ hk0
  linear_combination h + 2 * hD - hA

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
  have h28 := bound6 k b hk hb hS
  have h29 := aux_eq_int k b hk hS
  have hkZ : (2 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have h33 := aux_b_odd (k : ℤ) b hkZ h29
  have h34 := aux_div (k : ℤ) b hkZ h29
  have h34' : 2 * k ^ 2 ∣ 4 * b ^ 2 + 3 * b + 1 := by
    first
      | exact_mod_cast h34
      | exact Int.natCast_dvd_natCast.mp (by push_cast; exact h34)
  have hle : 2 * k ^ 2 ≤ 4 * b ^ 2 + 3 * b + 1 := Nat.le_of_dvd (by omega) h34'
  have hb3 : b < 3 := by
    by_contra hcon
    push_neg at hcon
    have h35 := two_pow_ge b hcon
    have h6 : (2 * b + 1) * (2 * b + 2) ≤ (2 * b + 1) * 2 ^ b := Nat.mul_le_mul_left _ h35
    have e : (2 * b + 1) * (2 * b + 2) = 4 * b ^ 2 + 6 * b + 2 := by ring
    omega
  have hb1 : b = 1 := by
    obtain ⟨c, hc⟩ := h33
    omega
  subst hb1
  refine ⟨?_, rfl⟩
  have h8 : 2 * k ^ 2 ∣ 8 := by
    have e : (4 * 1 ^ 2 + 3 * 1 + 1 : ℕ) = 8 := by norm_num
    rw [e] at h34'
    exact h34'
  have hle8 : 2 * k ^ 2 ≤ 8 := Nat.le_of_dvd (by norm_num) h8
  have hk2 : k ^ 2 = k * k := sq k
  have hk3 : k ≤ 2 := by
    by_contra hcon
    push_neg at hcon
    have : 3 * 3 ≤ k * k := Nat.mul_le_mul hcon hcon
    omega
  omega


end Panda2608
