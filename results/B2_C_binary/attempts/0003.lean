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

-- N02
theorem lte_corollary (p : ℕ) (hp : p.Prime) (hodd : Odd p) (b : ℕ) :
    padicValNat p ((2 * p + 1) ^ (2 * b + 1) - 1) = 1 + padicValNat p (2 * b + 1) := by
  haveI := Fact.mk hp
  have hp2 : 2 < p := by
    have := hp.two_le
    have := Nat.odd_iff.mp hodd
    omega
  have h1 : 1 < 2 * p + 1 := by omega
  have h2 : p ∣ 2 * p + 1 - 1 := by
    rw [show 2 * p + 1 - 1 = 2 * p by omega]
    exact Dvd.intro_left 2 rfl
  have h3 : ¬ p ∣ 2 * p + 1 := (Nat.Prime.coprime_iff_not_dvd hp).1 (coprime_p_q p)
  have key := padicValNat.pow_sub_pow (n := 2 * b + 1) hodd h1 h2 h3 (by omega)
  rw [one_pow] at key
  rw [key, show 2 * p + 1 - 1 = 2 * p by omega]
  rw [padicValNat.mul (show (2:ℕ) ≠ 0 by norm_num) hp.ne_zero, padicValNat.self hp.one_lt]
  have hnd : ¬ p ∣ 2 := fun hd => by
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  rw [padicValNat.eq_zero_of_not_dvd hnd]
  omega

end Panda2608
