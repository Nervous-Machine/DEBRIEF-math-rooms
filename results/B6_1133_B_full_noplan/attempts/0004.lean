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
* `MeasureSmall C` is reduced by a union bound over the agreement set `S` (`coverSetOn`,
  `bigSets`, `volume_coverSet_le`, `volume_cube`) to two rooms:
  `exists_volume_coverSetOn_le` (analytic, per-`S` volume bound; open) and
  `exists_card_bigSets_mul_lt` (combinatorial, binomial count; open unless closed below).
  `measureSmall_of_one_le` assembles them.
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

/-- The set of `y` agreeing on the coordinates in `S` with the value vector of some polynomial
of degree `< (1+ε)n` bounded by `C` on `[-1,1]`. -/
def coverSetOn {n : ℕ} (x : Fin n → Icc (-1 : ℝ) 1) (ε C : ℝ) (S : Finset (Fin n)) :
    Set (Fin n → ℝ) :=
  {y | ∃ m : ℕ, (m : ℝ) < (1 + ε) * (n : ℝ) ∧
    ∃ v ∈ interpImage x m C, ∀ i ∈ S, v i = y i}

/-- The subsets of `Fin n` of size at least `(1-ε)n`. -/
noncomputable def bigSets (n : ℕ) (ε : ℝ) : Finset (Finset (Fin n)) :=
  Finset.univ.filter (fun S : Finset (Fin n) => (1 - ε) * (n : ℝ) ≤ (S.card : ℝ))

/-- A covered `y` is covered on its own agreement set, which is a big set. -/
theorem coverSet_inter_cube_subset {n : ℕ} (x : Fin n → Icc (-1 : ℝ) 1) (ε C : ℝ) :
    coverSet x ε C ∩ cube n ⊆ ⋃ S ∈ bigSets n ε, (coverSetOn x ε C S ∩ cube n) := by
  rintro y ⟨⟨m, hm, v, hv, hagree⟩, hy⟩
  refine Set.mem_iUnion₂.mpr ⟨Finset.univ.filter (fun i ↦ v i = y i), ?_,
    ⟨m, hm, v, hv, fun i hi => (Finset.mem_filter.mp hi).2⟩, hy⟩
  simp only [bigSets, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hagree

/-- Union bound over the agreement sets. -/
theorem volume_coverSet_le {n : ℕ} (x : Fin n → Icc (-1 : ℝ) 1) (ε C : ℝ) :
    MeasureTheory.volume (coverSet x ε C ∩ cube n) ≤
      ∑ S ∈ bigSets n ε, MeasureTheory.volume (coverSetOn x ε C S ∩ cube n) :=
  (MeasureTheory.measure_mono (coverSet_inter_cube_subset x ε C)).trans
    (MeasureTheory.measure_biUnion_finset_le _ _)

/-- The cube `[-1,1]^n` has volume `2^n`. -/
theorem volume_cube (n : ℕ) : MeasureTheory.volume (cube n) = ENNReal.ofReal (2 ^ n) := by
  rw [cube, MeasureTheory.volume_pi_pi]
  simp only [Real.volume_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow (by norm_num)]
  norm_num

/-- The analytic room (open): for `C ≥ 1`, uniformly for all small `ε`, the data on any set of
at least `(1-ε)n` nodes that are interpolated there by some polynomial of degree `< (1+ε)n`
bounded by `C` on `[-1,1]` fill an exponentially small fraction `ρ^n` of the cube `[-1,1]^n`.
The searcher believes this is the true content of the problem; it is not proved here. -/
theorem exists_volume_coverSetOn_le {C : ℝ} (hC : 1 ≤ C) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∃ ε₁ > (0 : ℝ), ∀ ε : ℝ, 0 < ε → ε ≤ ε₁ →
      ∀ᶠ n : ℕ in atTop, ∀ x : Fin n → Icc (-1 : ℝ) 1, ∀ S : Finset (Fin n),
        (1 - ε) * (n : ℝ) ≤ (S.card : ℝ) →
        MeasureTheory.volume (coverSetOn x ε C S ∩ cube n) ≤ ENNReal.ofReal (ρ ^ n * 2 ^ n) := by
  sorry

/-- Weighting the subsets of `Fin n` by `ε^{n-|S|}` (total weight `(1+ε)^n`), the sets of size
`≥ (1-ε)n` each carry weight `≥ ε^{εn}`, so they number at most `((1+ε) ε^{-ε})^n`. -/
theorem card_bigSets_le (n : ℕ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ((bigSets n ε).card : ℝ) ≤ ((1 + ε) * ε ^ (-ε)) ^ n := by
  have hsum : ∑ S : Finset (Fin n), ε ^ (n - S.card) = (1 + ε) ^ n := by
    have := Fin.sum_pow_mul_eq_add_pow (n := n) (1 : ℝ) ε
    simpa using this
  have hterm : ∀ S ∈ bigSets n ε, ε ^ (ε * n) ≤ ε ^ (n - S.card) := by
    intro S hS
    have hS' : (1 - ε) * (n : ℝ) ≤ S.card := (Finset.mem_filter.mp hS).2
    have hSn : S.card ≤ n := (Finset.card_le_univ S).trans_eq (Fintype.card_fin n)
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_ge hε0 hε1
    rw [Nat.cast_sub hSn]
    linarith
  have hmain : ((bigSets n ε).card : ℝ) * ε ^ (ε * n) ≤ (1 + ε) ^ n := by
    calc ((bigSets n ε).card : ℝ) * ε ^ (ε * n) = ∑ _S ∈ bigSets n ε, ε ^ (ε * n) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ S ∈ bigSets n ε, ε ^ (n - S.card) := Finset.sum_le_sum hterm
      _ ≤ ∑ S : Finset (Fin n), ε ^ (n - S.card) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun S _ _ => pow_nonneg hε0.le _)
      _ = (1 + ε) ^ n := hsum
  have hpos : 0 < ε ^ (ε * n) := Real.rpow_pos_of_pos hε0 _
  rw [mul_pow, ← Real.rpow_mul_natCast hε0.le, neg_mul, Real.rpow_neg hε0.le, ← div_eq_mul_inv,
    le_div_iff₀ hpos]
  exact hmain

/-- `(1+ε) ε^{-ε} → 1` as `ε → 0⁺`. -/
theorem tendsto_base :
    Tendsto (fun ε : ℝ => (1 + ε) * ε ^ (-ε)) (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 1) := by
  have hc : Continuous (fun ε : ℝ => (1 + ε) * Real.exp (Real.negMulLog ε)) := by fun_prop
  have h1 : Tendsto (fun ε : ℝ => (1 + ε) * Real.exp (Real.negMulLog ε)) (nhds 0) (nhds 1) := by
    have := hc.tendsto 0
    simpa using this
  refine (h1.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [Real.rpow_def_of_pos hε, Real.negMulLog, show Real.log ε * -ε = -ε * Real.log ε from by ring]

/-- The combinatorial room: the number of subsets of `Fin n` of size `≥ (1-ε)n` grows like
`2^{H(ε) n}`, so for `ε` small enough it is beaten by any fixed exponential `ρ^{-n}`. -/
theorem exists_card_bigSets_mul_lt (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (ε₁ : ℝ) (hε₁ : 0 < ε₁) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ ε₁ ∧ ∀ᶠ n : ℕ in atTop, ((bigSets n ε).card : ℝ) * ρ ^ n < 1 := by
  have hlim : Tendsto (fun ε : ℝ => ρ * ((1 + ε) * ε ^ (-ε))) (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (ρ * 1)) := tendsto_base.const_mul ρ
  rw [mul_one] at hlim
  have h1 : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Ioi 0), ρ * ((1 + ε) * ε ^ (-ε)) < 1 :=
    hlim.eventually_lt_const hρ1
  have h2 : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Ioi 0), ε < ε₁ :=
    (eventually_lt_nhds hε₁).filter_mono nhdsWithin_le_nhds
  have h3 : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Ioi 0), ε < 1 :=
    (eventually_lt_nhds one_pos).filter_mono nhdsWithin_le_nhds
  have h4 : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Ioi 0), ε ∈ Ioi (0 : ℝ) := eventually_mem_nhdsWithin
  obtain ⟨ε, hε1, hε2, hε3, hε4⟩ := (h1.and (h2.and (h3.and h4))).exists
  have hε0 : 0 < ε := hε4
  refine ⟨ε, hε0, hε2.le, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hb0 : 0 ≤ ρ * ((1 + ε) * ε ^ (-ε)) := by positivity
  calc ((bigSets n ε).card : ℝ) * ρ ^ n ≤ ((1 + ε) * ε ^ (-ε)) ^ n * ρ ^ n :=
        mul_le_mul_of_nonneg_right (card_bigSets_le n hε0 hε3.le) (pow_nonneg hρ0 n)
    _ = (ρ * ((1 + ε) * ε ^ (-ε))) ^ n := by ring
    _ ≤ ρ * ((1 + ε) * ε ^ (-ε)) := pow_le_of_le_one hb0 hε1.le (by omega)
    _ < 1 := hε1

/-- The analytic core for `C ≥ 1`, assembled from the two rooms above by the union bound. -/
theorem measureSmall_of_one_le {C : ℝ} (hC : 1 ≤ C) : MeasureSmall C := by
  obtain ⟨ρ, hρ0, hρ1, ε₁, hε₁, hA⟩ := exists_volume_coverSetOn_le hC
  obtain ⟨ε, hε0, hεε₁, hB⟩ := exists_card_bigSets_mul_lt ρ hρ0 hρ1 ε₁ hε₁
  refine ⟨ε, hε0, ?_⟩
  filter_upwards [hA ε hε0 hεε₁, hB] with n hn hcount x
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  calc MeasureTheory.volume (coverSet x ε C ∩ cube n)
      ≤ ∑ S ∈ bigSets n ε, MeasureTheory.volume (coverSetOn x ε C S ∩ cube n) :=
        volume_coverSet_le x ε C
    _ ≤ ∑ _S ∈ bigSets n ε, ENNReal.ofReal (ρ ^ n * 2 ^ n) :=
        Finset.sum_le_sum fun S hS => hn x S (Finset.mem_filter.mp hS).2
    _ = (bigSets n ε).card • ENNReal.ofReal (ρ ^ n * 2 ^ n) := Finset.sum_const _
    _ = ENNReal.ofReal (((bigSets n ε).card : ℝ) * (ρ ^ n * 2 ^ n)) := by
        rw [nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ < ENNReal.ofReal (2 ^ n) := by
        rw [ENNReal.ofReal_lt_ofReal_iff h2]
        calc ((bigSets n ε).card : ℝ) * (ρ ^ n * 2 ^ n)
            = (((bigSets n ε).card : ℝ) * ρ ^ n) * 2 ^ n := by ring
          _ < 1 * 2 ^ n := mul_lt_mul_of_pos_right hcount h2
          _ = 2 ^ n := one_mul _
    _ = MeasureTheory.volume (cube n) := (volume_cube n).symm

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
