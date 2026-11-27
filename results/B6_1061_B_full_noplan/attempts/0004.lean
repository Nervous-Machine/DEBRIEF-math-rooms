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
    have hfp : 0 < ⌊x / 18⌋₊ := by omega
    have hge : (1 : ℝ) ≤ x / 18 := Nat.floor_pos.mp hfp
    have h1 : (k : ℝ) + 1 ≤ (⌊x / 18⌋₊ : ℝ) := by exact_mod_cast hk
    have h2 : (⌊x / 18⌋₊ : ℝ) ≤ x / 18 := Nat.floor_le (by linarith)
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

/-- Every solution `(u, v)` with `u, v ≥ 1` gives a linear lower bound through its lifts
`(u (n k + 1), v (n k + 1))`, `n = u v (u + v)`. -/
lemma floor_le_S_of_solution {u v : ℕ} (hu : 0 < u) (hv : 0 < v)
    (huv : σ 1 u + σ 1 v = σ 1 (u + v)) (x : ℝ) :
    (⌊x / (2 * (u * v * (u + v)) * (u + v))⌋₊ : ℝ) ≤ S x := by
  unfold S
  set n : ℕ := u * v * (u + v) with hn
  set D : ℝ := 2 * (u * v * (u + v)) * (u + v) with hD
  have hn1 : 1 ≤ n := by
    rw [hn]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hs : 0 < u + v := by omega
  have hD' : D = 2 * (n : ℝ) * ((u + v : ℕ) : ℝ) := by rw [hD, hn]; push_cast; ring
  have hDpos : 0 < D := by rw [hD']; positivity
  have hinj : Set.InjOn (fun k : ℕ => (u * (n * k + 1), v * (n * k + 1)))
      (Finset.range ⌊x / D⌋₊ : Set ℕ) := by
    intro a _ b _ h
    simp only [Prod.mk.injEq] at h
    have h1 := Nat.eq_of_mul_eq_mul_left hu h.1
    have h2 : n * a = n * b := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega) h2
  have hsub : (Finset.range ⌊x / D⌋₊).image (fun k : ℕ => (u * (n * k + 1), v * (n * k + 1))) ⊆
      (Finset.Icc 1 ⌊x⌋₊ ×ˢ Finset.Icc 1 ⌊x⌋₊).filter fun (a, b) ↦
        a + b ≤ x ∧ σ 1 a + σ 1 b = σ 1 (a + b) := by
    intro p hp
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
    have hk := Finset.mem_range.mp hk
    have hfp : 0 < ⌊x / D⌋₊ := by omega
    have hge : (1 : ℝ) ≤ x / D := Nat.floor_pos.mp hfp
    have h1 : (k : ℝ) + 1 ≤ (⌊x / D⌋₊ : ℝ) := by exact_mod_cast hk
    have h2 : (⌊x / D⌋₊ : ℝ) ≤ x / D := Nat.floor_le (by linarith)
    have hk' : ((k : ℝ) + 1) * D ≤ x := by
      rw [← le_div_iff₀ hDpos]; linarith
    have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hs' : (0 : ℝ) < ((u + v : ℕ) : ℝ) := by exact_mod_cast hs
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
    -- the key estimate: `(u + v) (n k + 1) ≤ 2 n (u + v) (k + 1) ≤ x`
    have hab : ((u + v : ℕ) : ℝ) * ((n : ℝ) * k + 1) ≤ x := by
      have e1 : ((u + v : ℕ) : ℝ) * ((n : ℝ) * k + 1) ≤
          ((u + v : ℕ) : ℝ) * (2 * (n : ℝ) * ((k : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (by nlinarith) hs'.le
      have e2 : ((u + v : ℕ) : ℝ) * (2 * (n : ℝ) * ((k : ℝ) + 1)) = ((k : ℝ) + 1) * D := by
        rw [hD']; ring
      linarith
    have hx0 : 0 ≤ x := by
      have := (le_div_iff₀ hDpos).mp hge; linarith
    have hau : ((u * (n * k + 1) : ℕ) : ℝ) ≤ x := by
      refine le_trans ?_ hab
      push_cast
      have : (u : ℝ) ≤ (u : ℝ) + v := by linarith [(Nat.cast_nonneg v : (0:ℝ) ≤ v)]
      exact mul_le_mul_of_nonneg_right this (by positivity)
    have hav : ((v * (n * k + 1) : ℕ) : ℝ) ≤ x := by
      refine le_trans ?_ hab
      push_cast
      have : (v : ℝ) ≤ (u : ℝ) + v := by linarith [(Nat.cast_nonneg u : (0:ℝ) ≤ u)]
      exact mul_le_mul_of_nonneg_right this (by positivity)
    have hsum : ((u * (n * k + 1) : ℕ) : ℝ) + ((v * (n * k + 1) : ℕ) : ℝ) ≤ x := by
      refine le_trans (le_of_eq ?_) hab
      push_cast; ring
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_, ?_⟩
    · exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (by positivity), Nat.le_floor hau⟩
    · exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (by positivity), Nat.le_floor hav⟩
    · exact_mod_cast hsum
    · have hcop : Nat.Coprime (u * v * (u + v)) (n * k + 1) := by
        rw [hn, Nat.coprime_mul_left_add_right]; exact Nat.coprime_one_right _
      have := solution_lift huv hcop
      rw [this]; congr 1; ring
  have := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_range] at this
  exact_mod_cast this

/-- Primitive solutions `(u, v)` (coprime, `u + v ≤ x / m`) whose lift by `m` is a legitimate lift. -/
noncomputable def prim (x : ℝ) (m : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 ⌊x⌋₊ ×ˢ Finset.Icc 1 ⌊x⌋₊).filter fun (u, v) ↦
    (((u + v) * m : ℕ) : ℝ) ≤ x ∧ Nat.Coprime u v ∧ Nat.Coprime (u * v * (u + v)) m ∧
      σ 1 u + σ 1 v = σ 1 (u + v)

/-- Reduction to primitive solutions: the lifts `(u m, v m)` of primitive solutions are pairwise distinct
solutions, so `S x` dominates the sum over `m` of the number of primitive solutions admitting the lift by `m`. -/
lemma sum_prim_le_S (x : ℝ) :
    ((∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (prim x m).card : ℕ) : ℝ) ≤ S x := by
  unfold S
  rw [← Finset.card_sigma]
  have key := Finset.card_le_card_of_injOn
    (s := (Finset.Icc 1 ⌊x⌋₊).sigma fun m => prim x m)
    (t := (Finset.Icc 1 ⌊x⌋₊ ×ˢ Finset.Icc 1 ⌊x⌋₊).filter fun (a, b) ↦
        a + b ≤ x ∧ σ 1 a + σ 1 b = σ 1 (a + b))
    (fun p : Σ _ : ℕ, ℕ × ℕ => (p.2.1 * p.1, p.2.2 * p.1)) ?_ ?_
  · exact_mod_cast key
  · intro p hp
    rw [Finset.mem_coe, Finset.mem_sigma] at hp
    obtain ⟨hm, hp⟩ := hp
    obtain ⟨m, u, v⟩ := p
    simp only [prim, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp hm
    obtain ⟨⟨⟨hu1, _⟩, ⟨hv1, _⟩⟩, hle, _, hcop, huv⟩ := hp
    have hm1 : 1 ≤ m := hm.1
    have hu : ((u * m : ℕ) : ℝ) ≤ x := by
      refine le_trans ?_ hle; exact_mod_cast Nat.mul_le_mul_right m (by omega)
    have hv : ((v * m : ℕ) : ℝ) ≤ x := by
      refine le_trans ?_ hle; exact_mod_cast Nat.mul_le_mul_right m (by omega)
    rw [Finset.mem_coe]
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_, ?_⟩
    · exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (by positivity), Nat.le_floor hu⟩
    · exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (by positivity), Nat.le_floor hv⟩
    · have hle' : ((u : ℝ) + v) * m ≤ x := by exact_mod_cast hle
      have e : ((u : ℝ) * m + v * m) = ((u : ℝ) + v) * m := by ring
      rw [← e] at hle'
      exact_mod_cast hle'
    · have := solution_lift huv hcop
      rw [this]; congr 1; ring
  · intro p hp q hq hpq
    rw [Finset.mem_coe, Finset.mem_sigma] at hp hq
    obtain ⟨m, u, v⟩ := p
    obtain ⟨m', u', v'⟩ := q
    simp only [prim, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp hq
    simp only [Prod.mk.injEq] at hpq
    obtain ⟨h1, h2⟩ := hpq
    have hm1 : 1 ≤ m := hp.1.1
    have hm1' : 1 ≤ m' := hq.1.1
    have hcop : Nat.Coprime u v := hp.2.2.2.1
    have hcop' : Nat.Coprime u' v' := hq.2.2.2.1
    have hg : Nat.gcd (u * m) (v * m) = Nat.gcd (u' * m') (v' * m') := by rw [h1, h2]
    rw [Nat.gcd_mul_right, Nat.gcd_mul_right, hcop, hcop', one_mul, one_mul] at hg
    subst hg
    have hu : u = u' := Nat.eq_of_mul_eq_mul_right (by omega) h1
    have hv : v = v' := Nat.eq_of_mul_eq_mul_right (by omega) h2
    subst hu; subst hv
    rfl

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
