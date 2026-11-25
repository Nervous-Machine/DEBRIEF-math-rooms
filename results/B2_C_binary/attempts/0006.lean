module

public import Mathlib

@[expose] public section

namespace Panda2608

theorem coprime_p_q (p : ℕ) : Nat.Coprime p (2 * p + 1) := by
  have h1 : Nat.Coprime p 1 := Nat.coprime_one_right p
  exact (Nat.coprime_mul_right_add_right p 1 2).2 h1

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

end Panda2608
