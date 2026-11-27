/-
Erdős Problem 1133, statement copied verbatim from google-deepmind/formal-conjectures,
FormalConjectures/ErdosProblems/1133.lean at commit 9097e2f9 (Apache-2.0; Copyright 2026 The Formal Conjectures Authors),
with the FormalConjecturesUtil import replaced by Mathlib. The searcher may not alter the statement.
References: erdosproblems.com/1133; Erdős (1967); Yang, J.-Q., arXiv:2609.14769 (2026).
-/
module

public import Mathlib

@[expose] public section

open Filter Set

namespace Erdos1133

/-! ## The searcher's own route (arm B6_1133_B_full_noplan, no blueprint)

* `Statement C` is the conclusion of the problem for one fixed bound `C`.
* `statement_of_lt_one`: for `C < 1` the problem is trivial (take `y ≡ 1`).
* `statement_mono`: the conclusion is monotone in `C`.
* `interpImage x m C`: the vectors of values at the nodes `x` of real polynomials of degree
  `≤ m` bounded by `C` on `[-1,1]`.  `NotCovered C` says that for large `n` some `y ∈ [-1,1]^n`
  is at Hamming distance `> εn` from every such vector with `m < (1+ε)n`; this implies
  `Statement C` (`statement_of_notCovered`).
* `MeasureSmall C`: the set of `y` in the cube that are so covered has Lebesgue measure strictly
  smaller than the cube.  A measure pigeonhole gives `NotCovered C` (`notCovered_of_measureSmall`).
* `measureSmall_of_one_le`: the analytic core, for `C ≥ 1`.  Left open.
-/

/-- The conclusion of Erdős problem 1133 for a fixed bound `C`. -/
def Statement (C : ℝ) : Prop :=
  ∃ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    ∀ x : Fin n → Icc (-1 : ℝ) 1,
      ∃ y : Fin n → Icc (-1 : ℝ) 1,
        ∀ P : Polynomial ℝ,
          (P.natDegree : ℝ) < (1 + ε) * (n : ℝ) →
          ((Finset.univ.filter (fun i ↦ P.eval (x i : ℝ) = (y i : ℝ))).card : ℝ) ≥
            (1 - ε) * (n : ℝ) →
          ∃ z ∈ Icc (-1 : ℝ) 1, |P.eval z| > C

/-- The conclusion is monotone in the bound. -/
theorem statement_mono {C₁ C₂ : ℝ} (h : C₁ ≤ C₂) (H : Statement C₂) : Statement C₁ := by
  obtain ⟨ε, hε, hN⟩ := H
  refine ⟨ε, hε, ?_⟩
  filter_upwards [hN] with n hn x
  obtain ⟨y, hy⟩ := hn x
  refine ⟨y, fun P hP hcard => ?_⟩
  obtain ⟨z, hz, hz'⟩ := hy P hP hcard
  exact ⟨z, hz, lt_of_le_of_lt h hz'⟩

/-- For `C < 1` the problem is trivial: take `y ≡ 1`; any polynomial agreeing with `y` at
one node already has a value `1 > C` there. -/
theorem statement_of_lt_one {C : ℝ} (hC : C < 1) : Statement C := by
  refine ⟨1 / 2, by norm_num, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn x
  refine ⟨fun _ => ⟨1, by norm_num⟩, fun P _ hcard => ?_⟩
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (1 - 1 / 2) * (n : ℝ) := by nlinarith
  have hcardpos := lt_of_lt_of_le hpos hcard
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (by exact_mod_cast hcardpos)
  have h2 : P.eval (x i : ℝ) = 1 := (Finset.mem_filter.mp hi).2
  exact ⟨x i, (x i).2, by rw [h2, abs_one]; exact hC⟩

/-- The vectors of values at the nodes `x` of the real polynomials of degree at most `m`
that are bounded by `C` on `[-1,1]`. -/
def interpImage {n : ℕ} (x : Fin n → Icc (-1 : ℝ) 1) (m : ℕ) (C : ℝ) : Set (Fin n → ℝ) :=
  {v | ∃ P : Polynomial ℝ, P.natDegree ≤ m ∧ (∀ z ∈ Icc (-1 : ℝ) 1, |P.eval z| ≤ C) ∧
    ∀ i, P.eval (x i : ℝ) = v i}

/-- The number of coordinates in which two vectors agree. -/
noncomputable def agree {n : ℕ} (v y : Fin n → ℝ) : ℕ := (Finset.univ.filter (fun i ↦ v i = y i)).card

/-- Hamming-covering form: for large `n` and any nodes there is `y ∈ [-1,1]^n` agreeing in
fewer than `(1-ε)n` coordinates with every value vector of a polynomial of degree `< (1+ε)n`
bounded by `C`. -/
def NotCovered (C : ℝ) : Prop :=
  ∃ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    ∀ x : Fin n → Icc (-1 : ℝ) 1,
      ∃ y : Fin n → Icc (-1 : ℝ) 1,
        ∀ m : ℕ, (m : ℝ) < (1 + ε) * (n : ℝ) →
          ∀ v ∈ interpImage x m C, (agree v (fun i ↦ (y i : ℝ)) : ℝ) < (1 - ε) * (n : ℝ)

theorem statement_of_notCovered {C : ℝ} (H : NotCovered C) : Statement C := by
  obtain ⟨ε, hε, hN⟩ := H
  refine ⟨ε, hε, ?_⟩
  filter_upwards [hN] with n hn x
  obtain ⟨y, hy⟩ := hn x
  refine ⟨y, fun P hP hcard => ?_⟩
  by_contra hcon
  push Not at hcon
  have hv : (fun i ↦ P.eval (x i : ℝ)) ∈ interpImage x P.natDegree C :=
    ⟨P, le_rfl, hcon, fun i => rfl⟩
  have hlt := hy P.natDegree hP _ hv
  simp only [agree] at hlt
  exact absurd hcard (not_le.mpr hlt)

/-- The cube `[-1,1]^n`. -/
def cube (n : ℕ) : Set (Fin n → ℝ) := Set.pi Set.univ (fun _ : Fin n => Icc (-1 : ℝ) 1)

/-- The set of `y` that agree in at least `(1-ε)n` coordinates with the value vector of some
polynomial of degree `< (1+ε)n` bounded by `C` on `[-1,1]`. -/
def coverSet {n : ℕ} (x : Fin n → Icc (-1 : ℝ) 1) (ε C : ℝ) : Set (Fin n → ℝ) :=
  {y | ∃ m : ℕ, (m : ℝ) < (1 + ε) * (n : ℝ) ∧
    ∃ v ∈ interpImage x m C, (1 - ε) * (n : ℝ) ≤ (agree v y : ℝ)}

/-- Measure form: the covered part of the cube has strictly smaller Lebesgue measure than the
cube. -/
def MeasureSmall (C : ℝ) : Prop :=
  ∃ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    ∀ x : Fin n → Icc (-1 : ℝ) 1,
      MeasureTheory.volume (coverSet x ε C ∩ cube n) < MeasureTheory.volume (cube n)

/-- Measure pigeonhole: a set of smaller measure than the cube misses a point of the cube. -/
theorem notCovered_of_measureSmall {C : ℝ} (H : MeasureSmall C) : NotCovered C := by
  obtain ⟨ε, hε, hN⟩ := H
  refine ⟨ε, hε, ?_⟩
  filter_upwards [hN] with n hn x
  have hlt := hn x
  have hns : ¬ (cube n ⊆ coverSet x ε C) := by
    intro hsub
    have hsub' : cube n ⊆ coverSet x ε C ∩ cube n := fun y hy => ⟨hsub hy, hy⟩
    exact absurd (MeasureTheory.measure_mono hsub') (not_le.mpr hlt)
  rw [Set.not_subset] at hns
  obtain ⟨y, hy, hny⟩ := hns
  refine ⟨fun i => ⟨y i, hy i (Set.mem_univ i)⟩, fun m hm v hv => ?_⟩
  by_contra hcon
  push Not at hcon
  exact hny ⟨m, hm, v, hv, hcon⟩

/-- The analytic core for `C ≥ 1`: the covered part of the cube is a strict-measure subset.
(Heuristically its measure is exponentially small in `n`; left open.) -/
theorem measureSmall_of_one_le {C : ℝ} (hC : 1 ≤ C) : MeasureSmall C := by
  sorry

/-- Let C > 0. There exists ε > 0 such that if n is sufficiently large the following holds. For any
x₁, …, xₙ ∈ [-1,1] there exist y₁, …, yₙ ∈ [-1,1] such that, if P is a polynomial of degree m < (1+ε)n with
P(xᵢ) = yᵢ for at least (1−ε)n many i, then max_{x ∈ [-1,1]} |P(x)| > C. -/
theorem erdos_1133 :
    ∀ C > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      ∀ x : Fin n → Icc (-1 : ℝ) 1,
        ∃ y : Fin n → Icc (-1 : ℝ) 1,
          ∀ P : Polynomial ℝ,
            (P.natDegree : ℝ) < (1 + ε) * (n : ℝ) →
            ((Finset.univ.filter (fun i ↦ P.eval (x i : ℝ) = (y i : ℝ))).card : ℝ) ≥
              (1 - ε) * (n : ℝ) →
            ∃ z ∈ Icc (-1 : ℝ) 1, |P.eval z| > C := by
  intro C _hC
  rcases lt_or_ge C 1 with h | h
  · exact statement_of_lt_one h
  · exact statement_of_notCovered (notCovered_of_measureSmall (measureSmall_of_one_le h))

end Erdos1133
