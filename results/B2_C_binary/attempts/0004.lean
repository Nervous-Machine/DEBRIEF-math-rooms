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

end Panda2608
