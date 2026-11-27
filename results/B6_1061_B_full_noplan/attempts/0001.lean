/-
Erdős Problem 1061: the statement of Eric Li's claim (arXiv:2606.25849v1, Theorem 1.1: for every fixed R > 0,
S(x) / (x (log x)^R) → ∞), written by the registrar on 2026-11-26 over the counting function `S` copied verbatim from
google-deepmind/formal-conjectures, FormalConjectures/ErdosProblems/1061.lean at commit 9097e2f9 (Apache-2.0;
Copyright 2026 The Formal Conjectures Authors), with the FormalConjecturesUtil import replaced by Mathlib.
Ordered pairs are counted, as in the paper. The searcher may not alter the definition or the statement.
References: erdosproblems.com/1061; Guy, Unsolved Problems in Number Theory, B15.
-/
module

public import Mathlib

@[expose] public section

open Filter Asymptotics
open scoped ArithmeticFunction.sigma

namespace Erdos1061

/-- Let `S x` count the number of **ordered** pairs of positive integers `(a, b)` with `a + b ≤ x`
such that `σ(a) + σ(b) = σ(a + b)`, where `σ` is the sum of divisors function. -/
noncomputable abbrev S (x : ℝ) : ℝ :=
  ((Finset.Icc 1 ⌊x⌋₊ ×ˢ Finset.Icc 1 ⌊x⌋₊).filter fun (a, b) ↦
      a + b ≤ x ∧ σ 1 a + σ 1 b = σ 1 (a + b)).card

/-! ## Searcher's route (no blueprint in this arm)

Route: (1) `σ` is multiplicative, so a solution `(u, v)` of `σ u + σ v = σ (u + v)` lifts to `(u m, v m)` for every
`m` coprime to `u v (u + v)`; (2) `(1, 2)` is a solution, hence `(m, 2 m)` is a solution for every `m` coprime to `6`,
which already gives `S x ≥ x / 18 - 1`; (3) the root is equivalent to the eventual lower bound
`C x (log x)^R ≤ S x` for every `C`; (4) that lower bound (superlinear growth) is the open room. -/

/-- `σ` is multiplicative on coprime arguments. -/
lemma sigma_mul_of_coprime {m n : ℕ} (h : Nat.Coprime m n) : σ 1 (m * n) = σ 1 m * σ 1 n :=
  ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime h

lemma sigma_two : σ 1 2 = 3 := by
  have := ArithmeticFunction.sigma_one_apply_prime_pow (i := 1) Nat.prime_two
  simpa [Finset.sum_range_succ] using this

lemma sigma_three : σ 1 3 = 4 := by
  have := ArithmeticFunction.sigma_one_apply_prime_pow (i := 1) Nat.prime_three
  simpa [Finset.sum_range_succ] using this

/-- `(1, 2)` is a solution: `σ 1 + σ 2 = 1 + 3 = 4 = σ 3`. -/
lemma solution_one_two : σ 1 1 + σ 1 2 = σ 1 (1 + 2) := by
  rw [ArithmeticFunction.sigma_one, sigma_two]
  norm_num [sigma_three]

/-- Lifting: a solution `(u, v)` lifts to `(u m, v m)` for every `m` coprime to `u v (u + v)`. -/
lemma solution_lift {u v m : ℕ} (huv : σ 1 u + σ 1 v = σ 1 (u + v))
    (hm : Nat.Coprime (u * v * (u + v)) m) :
    σ 1 (u * m) + σ 1 (v * m) = σ 1 ((u + v) * m) := by
  have hu : Nat.Coprime u m := by
    exact Nat.Coprime.coprime_dvd_left (Dvd.intro _ rfl) (Nat.Coprime.coprime_dvd_left (Dvd.intro _ rfl) hm)
  have hv : Nat.Coprime v m := by
    exact Nat.Coprime.coprime_dvd_left (Dvd.intro_left _ rfl) (Nat.Coprime.coprime_dvd_left (Dvd.intro _ rfl) hm)
  have hs : Nat.Coprime (u + v) m := Nat.Coprime.coprime_dvd_left (Dvd.intro_left _ rfl) hm
  rw [sigma_mul_of_coprime hu, sigma_mul_of_coprime hv, sigma_mul_of_coprime hs, ← add_mul, huv]

/-- The family `(m, 2 m)`, `m` coprime to `6`. -/
lemma solution_m_two_m {m : ℕ} (hm : Nat.Coprime 6 m) : σ 1 m + σ 1 (2 * m) = σ 1 (3 * m) := by
  have := solution_lift (u := 1) (v := 2) (m := m) solution_one_two (by simpa using hm)
  simpa using this

/-- `6 k + 1` is coprime to `6`. -/
lemma coprime_six_succ (k : ℕ) : Nat.Coprime 6 (6 * k + 1) := by
  rw [Nat.coprime_comm, Nat.Coprime, Nat.gcd_comm, Nat.gcd_mul_left_add_right]
  simp

/-- The explicit family `k ↦ (6 k + 1, 2 (6 k + 1))`, `k < ⌊x / 18⌋₊`, lands in the set counted by `S x`. -/
lemma family_mem (x : ℝ) {k : ℕ} (hk : k < ⌊x / 18⌋₊) :
    (6 * k + 1, 2 * (6 * k + 1)) ∈
      (Finset.Icc 1 ⌊x⌋₊ ×ˢ Finset.Icc 1 ⌊x⌋₊).filter fun (a, b) ↦
        a + b ≤ x ∧ σ 1 a + σ 1 b = σ 1 (a + b) := by
  have hk' : ((k : ℝ) + 1) ≤ x / 18 := by
    have := Nat.lt_floor_add_one (x / 18)
    have h1 : (k : ℝ) + 1 ≤ (⌊x / 18⌋₊ : ℝ) := by exact_mod_cast hk
    have h2 : (⌊x / 18⌋₊ : ℝ) ≤ x / 18 := Nat.floor_le (by positivity)
    linarith
  have h18 : 18 * ((k : ℝ) + 1) ≤ x := by linarith
  have hx0 : 0 ≤ x := by linarith
  have ha : ((6 * k + 1 : ℕ) : ℝ) ≤ x := by push_cast; linarith
  have hb : ((2 * (6 * k + 1) : ℕ) : ℝ) ≤ x := by push_cast; linarith
  have hab : ((6 * k + 1 : ℕ) : ℝ) + ((2 * (6 * k + 1) : ℕ) : ℝ) ≤ x := by push_cast; linarith
  refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_, ?_⟩
  · exact Finset.mem_Icc.mpr ⟨by omega, Nat.le_floor ha⟩
  · exact Finset.mem_Icc.mpr ⟨by omega, Nat.le_floor hb⟩
  · exact_mod_cast hab
  · have := solution_m_two_m (coprime_six_succ k)
    rw [this]; congr 1; ring

/-- Linear lower bound in terms of the floor: `⌊x / 18⌋₊ ≤ S x`. -/
lemma floor_le_S (x : ℝ) : (⌊x / 18⌋₊ : ℝ) ≤ S x := by
  unfold S
  have hinj : Set.InjOn (fun k : ℕ => (6 * k + 1, 2 * (6 * k + 1))) (Finset.range ⌊x / 18⌋₊ : Set ℕ) := by
    intro a _ b _ h
    simp only [Prod.mk.injEq] at h
    omega
  have hsub : (Finset.range ⌊x / 18⌋₊).image (fun k : ℕ => (6 * k + 1, 2 * (6 * k + 1))) ⊆
      (Finset.Icc 1 ⌊x⌋₊ ×ˢ Finset.Icc 1 ⌊x⌋₊).filter fun (a, b) ↦
        a + b ≤ x ∧ σ 1 a + σ 1 b = σ 1 (a + b) := by
    intro p hp
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
    exact family_mem x (Finset.mem_range.mp hk)
  have := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_range] at this
  exact_mod_cast this

/-- Linear lower bound: `x / 18 - 1 ≤ S x`. -/
lemma linear_lower (x : ℝ) : x / 18 - 1 ≤ S x := by
  have := floor_le_S x
  have h := Nat.sub_one_lt_floor (x / 18)
  linarith

/-- Reduction: the root follows from the eventual lower bound `C x (log x)^R ≤ S x` for every `C`. -/
lemma root_of_eventually_lower
    (h : ∀ R : ℝ, 0 < R → ∀ C : ℝ, ∀ᶠ x in atTop, C * (x * Real.log x ^ R) ≤ S x) :
    ∀ R : ℝ, 0 < R → Tendsto (fun x : ℝ ↦ S x / (x * Real.log x ^ R)) atTop atTop := by
  intro R hR
  rw [Filter.tendsto_atTop]
  intro C
  filter_upwards [h R hR C, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  have hpos : 0 < x * Real.log x ^ R := by
    have := Real.log_pos hx1
    positivity
  rw [le_div_iff₀ hpos]
  exact hx

/-- The open room: superlinear growth of `S`, beating every power of `log`. Not closed in this arm. -/
lemma eventually_lower (R : ℝ) (hR : 0 < R) (C : ℝ) :
    ∀ᶠ x in atTop, C * (x * Real.log x ^ R) ≤ S x := by
  sorry

/-- Li's Theorem 1.1: for every fixed `R > 0`, `S x / (x (log x)^R)` tends to infinity. In particular `S` is not
asymptotic to `c * x` for any finite `c > 0`. -/
theorem li_1061 : ∀ R : ℝ, 0 < R →
    Tendsto (fun x : ℝ ↦ S x / (x * Real.log x ^ R)) atTop atTop :=
  root_of_eventually_lower eventually_lower

end Erdos1061
