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

end Panda2608
