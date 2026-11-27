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

-- N01 (literature_import)
theorem olevskii_ulanovskii_prop_4_2 :
    ∃ a > (0:ℝ), ∃ b > (0:ℝ), ∀ τ : ℕ, 1 ≤ τ → ∀ Γ : Finset ℝ,
       (∀ s ∈ Γ, s ∈ Set.Ico (-(τ:ℝ)) (τ:ℝ)) → 2 * τ ≤ Γ.card →
      ∀ σ : ℝ, Real.pi < σ → ∀ K : ℝ,
        (∀ v : ℝ  → ℂ, (∀ s ∈ Γ, ‖v s‖ ≤ 1) →
          ∃ f : ℂ → ℂ, Differentiable ℂ f ∧
            (∀ δ > (0:ℝ), ∃ M : ℝ, ∀ z : ℂ,  ‖f z‖ ≤ M * Real.exp ((σ + δ) * ‖z‖)) ∧
            (∀ x : ℝ, ‖f (x : ℂ)‖ ≤ K) ∧ ∀ s ∈ Γ, f (s : ℂ) = v s) →
         a * Real.log (σ / (σ - Real.pi + b * (τ:ℝ) ^ (-((1:ℝ) / 3)))) ≤ K := by
  sorry

-- N02 (literature_import)
theorem bernstein_vertical_growth (σ K : ℝ) (hσ : 0 < σ) (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (htype :  ∀ δ > (0:ℝ), ∃ M : ℝ, ∀ z : ℂ, ‖f z‖ ≤ M * Real.exp ((σ + δ) * ‖z‖))
    (hbd : ∀ x : ℝ, ‖f (x : ℂ)‖ ≤ K) (z : ℂ) :
     ‖f z‖ ≤ K * Real.exp (σ * |z.im|) := by
  sorry

-- N03 (literature_import)
theorem bernstein_real_sample_set_isClosed (σ H : ℝ) (hσ : 0 < σ) (k : ℕ) (t : Fin k → ℝ) :
    IsClosed {v  : Fin k → ℝ | ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
      (∀ δ > (0:ℝ), ∃ M : ℝ, ∀ z : ℂ, ‖g z‖ ≤ M * Real.exp ((σ + δ)  * ‖z‖)) ∧
      (∀ x : ℝ, (g (x : ℂ)).im = 0) ∧ (∀ x : ℝ, ‖g (x : ℂ)‖ ≤ H) ∧
      ∀ i, (g (t i : ℂ)).re = v i} :=  by
  sorry

-- N04 (algebraic_identity)
theorem exp_type_linear_comb (σ : ℝ) (f g : ℂ → ℂ) (a b : ℂ)
    (hf : ∀ δ > (0:ℝ), ∃ M : ℝ, ∀ z : ℂ, ‖f z‖  ≤ M * Real.exp ((σ + δ) * ‖z‖))
    (hg : ∀ δ > (0:ℝ), ∃ M : ℝ, ∀ z : ℂ, ‖g z‖ ≤ M * Real.exp ((σ + δ) * ‖z‖)) :
     ∀ δ > (0:ℝ), ∃ M : ℝ, ∀ z : ℂ, ‖a * f z + b * g z‖ ≤ M * Real.exp ((σ + δ) * ‖z‖) := by
  intro δ hδ
  obtain ⟨Mf, hMf⟩ := hf δ hδ
  obtain ⟨Mg, hMg⟩ := hg δ hδ
  refine ⟨‖a‖ * Mf + ‖b‖ * Mg, fun z => ?_⟩
  calc ‖a * f z + b * g z‖ ≤ ‖a * f z‖ + ‖b * g z‖ := norm_add_le _ _
    _ = ‖a‖ * ‖f z‖ + ‖b‖ * ‖g z‖ := by rw [norm_mul, norm_mul]
    _ ≤ ‖a‖ * (Mf * Real.exp ((σ + δ) * ‖z‖)) + ‖b‖ * (Mg * Real.exp ((σ + δ) * ‖z‖)) := by
        gcongr
        · exact hMf z
        · exact hMg z
    _ = (‖a‖ * Mf + ‖b‖ * Mg) * Real.exp ((σ + δ) * ‖z‖) := by ring

-- N05 (algebraic_identity)
theorem bernstein_affine_rescale (σ lam c K : ℝ) (hσ : 0 ≤ σ) (hlam : 0 < lam) (f : ℂ → ℂ)
    (hf : Differentiable  ℂ f)
    (htype : ∀ δ > (0:ℝ), ∃ M : ℝ, ∀ z : ℂ, ‖f z‖ ≤ M * Real.exp ((σ + δ) * ‖z‖))
    (hbd : ∀ x : ℝ, ‖f (x :  ℂ)‖ ≤ K) :
    Differentiable ℂ (fun z : ℂ => f (z / (lam : ℂ) + (c : ℂ))) ∧
    (∀ δ > (0:ℝ), ∃ M : ℝ, ∀ z : ℂ,
       ‖f (z / (lam : ℂ) + (c : ℂ))‖ ≤ M * Real.exp ((σ / lam + δ) * ‖z‖)) ∧
    (∀ x : ℝ, ‖f ((x : ℂ) / (lam : ℂ) +  (c : ℂ))‖ ≤ K) := by
  refine ⟨?_, ?_, ?_⟩
  · exact hf.comp ((differentiable_id.div_const _).add_const _)
  · intro δ hδ
    obtain ⟨M, hM⟩ := htype (δ * lam) (by positivity)
    refine ⟨M * Real.exp ((σ + δ * lam) * |c|), fun z => ?_⟩
    have hM0 : 0 ≤ M := by
      have h0 := hM 0
      have h1 : 0 < Real.exp ((σ + δ * lam) * ‖(0:ℂ)‖) := Real.exp_pos _
      by_contra hneg
      push_neg at hneg
      have := mul_neg_of_neg_of_pos hneg h1
      linarith [norm_nonneg (f 0)]
    have hnz : ‖z / (lam:ℂ) + (c:ℂ)‖ ≤ ‖z‖ / lam + |c| := by
      calc ‖z / (lam:ℂ) + (c:ℂ)‖ ≤ ‖z / (lam:ℂ)‖ + ‖(c:ℂ)‖ := norm_add_le _ _
        _ = ‖z‖ / lam + |c| := by
            rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_pos hlam]
    have hcoef : 0 ≤ σ + δ * lam := by positivity
    calc ‖f (z / lam + c)‖ ≤ M * Real.exp ((σ + δ * lam) * ‖z / (lam:ℂ) + (c:ℂ)‖) := hM _
      _ ≤ M * Real.exp ((σ + δ * lam) * (‖z‖ / lam + |c|)) := by
          apply mul_le_mul_of_nonneg_left _ hM0
          apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonneg_left hnz hcoef
      _ = M * Real.exp ((σ + δ * lam) * |c|) * Real.exp ((σ / lam + δ) * ‖z‖) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          field_simp
          ring
  · intro x
    have : (x:ℂ) / (lam:ℂ) + (c:ℂ) = ((x / lam + c : ℝ) : ℂ) := by push_cast; ring
    rw [this]; exact hbd _

-- N06 (algebraic_identity)
theorem complex_data_from_real (σ H : ℝ) (k : ℕ) (s : Fin k → ℝ)
    (hreal : ∀ v : Fin k → ℝ, (∀ i, |v i|  ≤ 1) →
      ∃ f : ℂ → ℂ, Differentiable ℂ f ∧
        (∀ δ > (0:ℝ), ∃ M : ℝ, ∀ z : ℂ, ‖f z‖ ≤ M * Real.exp ((σ +  δ) * ‖z‖)) ∧
        (∀ x : ℝ, ‖f (x : ℂ)‖ ≤ H) ∧ ∀ i, f (s i : ℂ) = (v i : ℂ)) :
    ∀ w : Fin k → ℂ, (∀ i, ‖w i‖  ≤ 1) →
      ∃ f : ℂ → ℂ, Differentiable ℂ f ∧
        (∀ δ > (0:ℝ), ∃ M : ℝ, ∀ z : ℂ, ‖f z‖ ≤ M * Real.exp ((σ +  δ) * ‖z‖)) ∧
        (∀ x : ℝ, ‖f (x : ℂ)‖ ≤ 2 * H) ∧ ∀ i, f (s i : ℂ) = w i := by
  intro w hw
  obtain ⟨f1, hf1d, hf1t, hf1b, hf1v⟩ :=
    hreal (fun i => (w i).re) (fun i => (Complex.abs_re_le_norm _).trans (hw i))
  obtain ⟨f2, hf2d, hf2t, hf2b, hf2v⟩ :=
    hreal (fun i => (w i).im) (fun i => (Complex.abs_im_le_norm _).trans (hw i))
  refine ⟨fun z => 1 * f1 z + Complex.I * f2 z, ?_, ?_, ?_, ?_⟩
  · exact (hf1d.const_mul _).add (hf2d.const_mul _)
  · exact exp_type_linear_comb σ f1 f2 1 Complex.I hf1t hf2t
  · intro x
    calc ‖1 * f1 x + Complex.I * f2 x‖ ≤ ‖1 * f1 x‖ + ‖Complex.I * f2 x‖ := norm_add_le _ _
      _ = ‖f1 x‖ + ‖f2 x‖ := by simp
      _ ≤ H + H := add_le_add (hf1b x) (hf2b x)
      _ = 2 * H := by ring
  · intro i
    have h1 := hf1v i
    have h2 := hf2v i
    show 1 * f1 (s i : ℂ) + Complex.I * f2 (s i : ℂ) = w i
    rw [h1, h2, one_mul, mul_comm Complex.I]
    exact Complex.re_add_im (w i)

-- N07 (algebraic_identity)
theorem lemma32_rescale_params (τ : ℕ) (hτ : 1 ≤ τ) (c t : ℝ)
    (ht : t ∈ Set.Icc c (c + 2 * (τ:ℝ) + 1))  :
    (2 * (τ:ℝ)) / (2 * τ + 2) * (t - c - (2 * (τ:ℝ) + 1) / 2) ∈ Set.Ico (-(τ:ℝ)) (τ:ℝ) ∧
    Real.pi < Real.pi /  ((2 * (τ:ℝ)) / (2 * τ + 2)) ∧
    Real.pi / ((2 * (τ:ℝ)) / (2 * τ + 2)) ≤ 2 * Real.pi := by
  have hτr : (1:ℝ) ≤ τ := by exact_mod_cast hτ
  obtain ⟨ht1, ht2⟩ := ht
  have hpos : (0:ℝ) < 2 * τ + 2 := by linarith
  have hpos2 : (0:ℝ) < 2 * τ := by linarith
  have hpi := Real.pi_pos
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ τ) (by linarith : (0:ℝ) ≤ t - c)]
  · rw [div_mul_eq_mul_div, div_lt_iff₀ hpos]
    nlinarith [mul_le_mul_of_nonneg_left (by linarith : t - c ≤ 2 * (τ:ℝ) + 1) (by linarith : (0:ℝ) ≤ τ)]
  · rw [div_div_eq_mul_div, lt_div_iff₀ hpos2]
    nlinarith
  · rw [div_div_eq_mul_div, div_le_iff₀ hpos2]
    nlinarith [mul_le_mul_of_nonneg_left hτr hpi.le]

-- N08 (algebraic_identity)
theorem lemma32_log_bound (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (τ : ℕ) (hτ : 1 ≤ τ) :
    a / 3 * Real.log (2  * (τ:ℝ)) - a * Real.log ((2 * Real.pi + b * (2:ℝ) ^ ((1:ℝ) / 3)) / Real.pi) ≤
      a * Real.log ((Real.pi / ((2 *  (τ:ℝ)) / (2 * τ + 2))) /
        (Real.pi / ((2 * (τ:ℝ)) / (2 * τ + 2)) - Real.pi + b * (τ:ℝ) ^ (-((1:ℝ) / 3)))) :=  by
  have hτr : (1:ℝ) ≤ τ := by exact_mod_cast hτ
  have hτ0 : (0:ℝ) < τ := by linarith
  have hpi := Real.pi_pos
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (τ:ℝ) ^ ((1:ℝ)/3) := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = (2:ℝ) ^ ((1:ℝ)/3) := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; exact Real.rpow_pos_of_pos hτ0 _
  have hw0 : 0 < w := by rw [hw]; exact Real.rpow_pos_of_pos two_pos _
  have hu3 : u ^ 3 = τ := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hτ0.le]; norm_num
  have hw3 : w ^ 3 = 2 := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul two_pos.le]; norm_num
  have hu1 : 1 ≤ u := by
    by_contra h
    push_neg at h
    have : u ^ 3 < 1 := pow_lt_one₀ hu0.le h (by norm_num)
    linarith
  have hw2 : w ≤ 2 := by
    by_contra h
    push_neg at h
    have : (2:ℝ) ^ 3 < w ^ 3 := pow_lt_pow_left₀ h (by norm_num) (by norm_num)
    linarith
  have hneg : (τ:ℝ) ^ (-((1:ℝ)/3)) = u⁻¹ := by rw [Real.rpow_neg hτ0.le, hu]
  have hσ : Real.pi / ((2 * (τ:ℝ)) / (2 * τ + 2)) = Real.pi + Real.pi / τ := by
    field_simp; ring
  rw [hneg, hσ, ← hw]
  have hlog : Real.log (2 * (τ:ℝ)) = 3 * Real.log (w * u) := by
    have h := Real.log_pow 3 (w * u)
    rw [mul_pow, hw3, hu3] at h
    rw [h]; norm_num
  rw [hlog]
  have hQ : 0 < (2 * Real.pi + b * w) / Real.pi := by positivity
  have e1 : a / 3 * (3 * Real.log (w * u)) - a * Real.log ((2 * Real.pi + b * w) / Real.pi) =
      a * (Real.log (w * u) - Real.log ((2 * Real.pi + b * w) / Real.pi)) := by ring
  rw [e1]
  apply mul_le_mul_of_nonneg_left _ ha.le
  rw [← Real.log_div (mul_pos hw0 hu0).ne' hQ.ne']
  have e2 : Real.pi + Real.pi / τ - Real.pi = Real.pi / τ := by ring
  rw [e2]
  apply Real.log_le_log (by positivity)
  rw [div_div_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
  rw [← hu3]
  have h1 : w * u * Real.pi * (Real.pi / u ^ 3 + b * u⁻¹) = w * Real.pi * (Real.pi / u ^ 2 + b) := by
    field_simp
    ring
  rw [h1]
  have h2 : Real.pi / u ^ 2 ≤ Real.pi := div_le_self hpi.le (one_le_pow₀ hu1)
  have h3 : 0 ≤ Real.pi / u ^ 3 := by positivity
  have h4 := mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ w * Real.pi)
  have h5 := mul_le_mul_of_nonneg_right hw2 (sq_nonneg Real.pi)
  have h6 := mul_nonneg h3 (by positivity : (0:ℝ) ≤ 2 * Real.pi + b * w)
  nlinarith [h4, h5, h6]

-- N09 (quantitative_improvement)
theorem lemma32_choose_k (a b0 : ℝ) (ha : 0 < a) (hb0 : 0 ≤ b0) :
    ∃ A0 > (0:ℝ), ∀ H > (0:ℝ), ∃ τ : ℕ, 1  ≤ τ ∧
      2 * H < a / 3 * Real.log (2 * (τ:ℝ)) - b0 ∧
      2 * (τ:ℝ) ≤ Real.exp (A0 * (1 + H)) := by
  refine ⟨2 + 3 * b0 / a + 6 / a, by positivity, fun H hH => ?_⟩
  set X := 3 * (2 * H + b0) / a with hX
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  refine ⟨⌈Real.exp X⌉₊, ?_, ?_, ?_⟩
  · exact Nat.one_le_ceil_iff.mpr (Real.exp_pos _)
  · have h1 : Real.exp X ≤ (⌈Real.exp X⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : Real.exp X < 2 * (⌈Real.exp X⌉₊ : ℝ) := by linarith [Real.exp_pos X]
    have h3 : X < Real.log (2 * (⌈Real.exp X⌉₊ : ℝ)) := by
      have h3' := Real.log_lt_log (Real.exp_pos X) h2
      rwa [Real.log_exp] at h3'
    have h4 : a / 3 * X = 2 * H + b0 := by rw [hX]; field_simp; ring
    have h5 := mul_lt_mul_of_pos_left h3 (by positivity : (0:ℝ) < a / 3)
    linarith
  · have h1 : (⌈Real.exp X⌉₊ : ℝ) < Real.exp X + 1 := Nat.ceil_lt_add_one (Real.exp_pos _).le
    have h2 : (1:ℝ) ≤ Real.exp X := Real.one_le_exp hX0
    have h4 : (4:ℝ) ≤ Real.exp 2 := by
      have h := Real.add_one_le_exp 1
      have h' : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      rw [h']; nlinarith [Real.exp_pos 1]
    have h5 : 2 + X ≤ (2 + 3 * b0 / a + 6 / a) * (1 + H) := by
      have e : (2 + 3 * b0 / a + 6 / a) * (1 + H) - (2 + X) = 2 * H + 3 * b0 * H / a + 6 / a := by
        rw [hX]; field_simp; ring
      have : 0 ≤ 2 * H + 3 * b0 * H / a + 6 / a := by positivity
      linarith
    calc 2 * (⌈Real.exp X⌉₊ : ℝ) ≤ 4 * Real.exp X := by linarith
      _ ≤ Real.exp 2 * Real.exp X := mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
      _ = Real.exp (2 + X) := (Real.exp_add _ _).symm
      _ ≤ Real.exp ((2 + 3 * b0 / a + 6 / a) * (1 + H)) := Real.exp_le_exp.mpr h5

-- N10 (assembly)
theorem lemma32_distinct_core :
    ∃ a > (0:ℝ), ∃ b0 ≥ (0:ℝ), ∀ τ : ℕ, 1 ≤ τ → ∀ (c : ℝ) (t : Fin (2 * τ)  → ℝ),
      Function.Injective t → (∀ i, t i ∈ Set.Icc c (c + 2 * (τ:ℝ) + 1)) → ∀ H : ℝ,
      (∀ v : Fin (2 * τ)  → ℝ, (∀ i, |v i| ≤ 1) →
        ∃ f : ℂ → ℂ, Differentiable ℂ f ∧
          (∀ δ > (0:ℝ), ∃ M : ℝ, ∀ z : ℂ, ‖f z‖  ≤ M * Real.exp ((Real.pi + δ) * ‖z‖)) ∧
          (∀ x : ℝ, ‖f (x : ℂ)‖ ≤ H) ∧ ∀ i, f (t i : ℂ) = (v i : ℂ)) →
       a / 3 * Real.log (2 * (τ:ℝ)) - b0 ≤ 2 * H := by
  sorry

-- N11 (case_split)
theorem coincident_nodes_obstruction (k : ℕ) (t : Fin k → ℝ) (i j : Fin k) (hij : i ≠ j)
    (heq : t i = t  j) :
    ∃ v : Fin k → ℝ, (∀ l, |v l| ≤ 1) ∧ ∀ f : ℂ → ℂ, ¬ ∀ l, f (t l : ℂ) = (v l : ℂ) := by
  refine ⟨Function.update (fun _ => (1:ℝ)) j (-1), fun l => ?_, fun f hf => ?_⟩
  · by_cases h : l = j
    · subst h; simp
    · simp [Function.update_of_ne h]
  · have h1 := hf i
    have h2 := hf j
    simp only [Function.update_of_ne hij, Function.update_self, heq] at h1 h2
    rw [h1] at h2
    norm_num at h2

-- N12 (assembly)
theorem effective_finite_obstruction :
    ∃ A0 > (0:ℝ), ∀ H > (0:ℝ), ∃ k : ℕ, Even k ∧ 2 ≤ k ∧ (k:ℝ) ≤ Real.exp  (A0 * (1 + H)) ∧
      ∀ (c : ℝ) (t : Fin k → ℝ), (∀ i, t i ∈ Set.Icc c (c + (k:ℝ) + 1)) →
        ∃ v : Fin k → ℝ,  (∀ i, |v i| ≤ 1) ∧
          ¬ ∃ f : ℂ → ℂ, Differentiable ℂ f ∧
            (∀ δ > (0:ℝ), ∃ M : ℝ, ∀ z : ℂ, ‖f z‖  ≤ M * Real.exp ((Real.pi + δ) * ‖z‖)) ∧
            (∀ x : ℝ, ‖f (x : ℂ)‖ ≤ H) ∧ ∀ i, f (t i : ℂ) = (v i : ℂ) := by
  obtain ⟨a, ha, b0, hb0, hcore⟩ := lemma32_distinct_core
  obtain ⟨A0, hA0, hchoose⟩ := lemma32_choose_k a b0 ha hb0
  refine ⟨A0, hA0, fun H hH => ?_⟩
  obtain ⟨τ, hτ, hlt, hle⟩ := hchoose H hH
  refine ⟨2 * τ, even_two_mul τ, by omega, by push_cast; exact hle, fun c t ht => ?_⟩
  by_cases hinj : Function.Injective t
  · by_contra hcon
    push_neg at hcon
    have ht' : ∀ i, t i ∈ Set.Icc c (c + 2 * (τ:ℝ) + 1) := by
      intro i
      have h := ht i
      push_cast at h
      exact h
    have := hcore τ hτ c t hinj ht' H hcon
    linarith
  · rw [Function.Injective] at hinj
    push_neg at hinj
    obtain ⟨i, j, heq, hij⟩ := hinj
    obtain ⟨v, hv, hno⟩ := coincident_nodes_obstruction (2 * τ) t i j hij heq
    exact ⟨v, hv, fun ⟨f, _, _, _, hf⟩ => hno f hf⟩

-- N13 (algebraic_identity)
theorem real_symmetrization (σ C : ℝ) (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (htype : ∀ δ > (0:ℝ), ∃ M :  ℝ, ∀ z : ℂ, ‖f z‖ ≤ M * Real.exp ((σ + δ) * ‖z‖))
    (hbd : ∀ x : ℝ, ‖f (x : ℂ)‖ ≤ C) :
    Differentiable ℂ (fun  z : ℂ => (f z + starRingEnd ℂ (f (starRingEnd ℂ z))) / 2) ∧
    (∀ δ > (0:ℝ), ∃ M : ℝ, ∀ z : ℂ,
      ‖(f z + starRingEnd  ℂ (f (starRingEnd ℂ z))) / 2‖ ≤ M * Real.exp ((σ + δ) * ‖z‖)) ∧
    (∀ x : ℝ, ((f (x : ℂ) + starRingEnd ℂ (f (starRingEnd  ℂ (x : ℂ)))) / 2).im = 0) ∧
    (∀ x : ℝ, ‖(f (x : ℂ) + starRingEnd ℂ (f (starRingEnd ℂ (x : ℂ)))) / 2‖ ≤ C) ∧
     (∀ x : ℝ, ((f (x : ℂ) + starRingEnd ℂ (f (starRingEnd ℂ (x : ℂ)))) / 2).re = (f (x : ℂ)).re) := by
  have hconj : Differentiable ℂ (fun z : ℂ => starRingEnd ℂ (f (starRingEnd ℂ z))) := by
    intro z
    have h := (hf (starRingEnd ℂ z)).conj_conj
    rw [starRingEnd_self_apply] at h
    exact h
  have hsym : ∀ z : ℂ, ‖(f z + starRingEnd ℂ (f (starRingEnd ℂ z))) / 2‖ ≤
      (‖f z‖ + ‖f (starRingEnd ℂ z)‖) / 2 := by
    intro z
    calc ‖(f z + starRingEnd ℂ (f (starRingEnd ℂ z))) / 2‖
        = ‖f z + starRingEnd ℂ (f (starRingEnd ℂ z))‖ / 2 := by rw [norm_div, Complex.norm_two]
      _ ≤ (‖f z‖ + ‖starRingEnd ℂ (f (starRingEnd ℂ z))‖) / 2 := by
          gcongr; exact norm_add_le _ _
      _ = (‖f z‖ + ‖f (starRingEnd ℂ z)‖) / 2 := by rw [Complex.norm_conj]
  have hreal : ∀ x : ℝ, (f (x:ℂ) + starRingEnd ℂ (f (starRingEnd ℂ (x:ℂ)))) / 2 =
      (((f (x:ℂ)).re : ℝ) : ℂ) := by
    intro x
    rw [Complex.conj_ofReal, Complex.add_conj]
    push_cast; ring
  refine ⟨(hf.add hconj).div_const _, ?_, ?_, ?_, ?_⟩
  · intro δ hδ
    obtain ⟨M, hM⟩ := htype δ hδ
    refine ⟨M, fun z => ?_⟩
    calc _ ≤ (‖f z‖ + ‖f (starRingEnd ℂ z)‖) / 2 := hsym z
      _ ≤ (M * Real.exp ((σ + δ) * ‖z‖) + M * Real.exp ((σ + δ) * ‖starRingEnd ℂ z‖)) / 2 := by
          gcongr
          · exact hM z
          · exact hM _
      _ = M * Real.exp ((σ + δ) * ‖z‖) := by rw [Complex.norm_conj]; ring
  · intro x; rw [hreal x]; exact Complex.ofReal_im _
  · intro x
    rw [hreal x, Complex.norm_real, Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans (hbd x)
  · intro x; rw [hreal x]; exact Complex.ofReal_re _

-- N14 (algebraic_identity)
theorem bernstein_real_sample_set_convex (σ H : ℝ) (k : ℕ) (t : Fin k → ℝ) :
    Convex ℝ {v : Fin k → ℝ |  ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
      (∀ δ > (0:ℝ), ∃ M : ℝ, ∀ z : ℂ, ‖g z‖ ≤ M * Real.exp ((σ + δ) * ‖z‖)) ∧
       (∀ x : ℝ, (g (x : ℂ)).im = 0) ∧ (∀ x : ℝ, ‖g (x : ℂ)‖ ≤ H) ∧
      ∀ i, (g (t i : ℂ)).re = v i} := by
  intro v1 hv1 v2 hv2 a b ha hb hab
  obtain ⟨g1, hg1d, hg1t, hg1im, hg1b, hg1v⟩ := hv1
  obtain ⟨g2, hg2d, hg2t, hg2im, hg2b, hg2v⟩ := hv2
  refine ⟨fun z => (a:ℂ) * g1 z + (b:ℂ) * g2 z, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hg1d.const_mul _).add (hg2d.const_mul _)
  · exact exp_type_linear_comb σ g1 g2 _ _ hg1t hg2t
  · intro x
    simp [Complex.add_im, Complex.mul_im, hg1im x, hg2im x]
  · intro x
    calc ‖(a:ℂ) * g1 x + (b:ℂ) * g2 x‖ ≤ ‖(a:ℂ) * g1 x‖ + ‖(b:ℂ) * g2 x‖ := norm_add_le _ _
      _ = a * ‖g1 x‖ + b * ‖g2 x‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * H + b * H :=
          add_le_add (mul_le_mul_of_nonneg_left (hg1b x) ha) (mul_le_mul_of_nonneg_left (hg2b x) hb)
      _ = H := by rw [← add_mul, hab, one_mul]
  · intro i
    simp [Complex.add_re, Complex.mul_re, hg1v i, hg2v i]

-- N15 (assembly)
theorem finite_dim_point_separation (k : ℕ) (K : Set (Fin k → ℝ)) (hconv : Convex ℝ K)
    (hclosed : IsClosed  K) (v : Fin k → ℝ) (hv : v ∉ K) :
    ∃ w : Fin k → ℝ, ∀ z ∈ K, ∑ i, w i * z i < ∑ i, w i * v i := by
  obtain ⟨f, u, hfu, huv⟩ := geometric_hahn_banach_closed_point hconv hclosed hv
  refine ⟨fun i => f (fun j => if i = j then 1 else 0), fun z hz => ?_⟩
  have key : ∀ y : Fin k → ℝ, f y = ∑ i, (f fun j => if i = j then 1 else 0) * y i := by
    intro y
    have h := LinearMap.pi_apply_eq_sum_univ (f : (Fin k → ℝ) →ₗ[ℝ] ℝ) y
    simp only [ContinuousLinearMap.coe_coe] at h
    rw [h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, mul_comm]
  show ∑ i, (f fun j => if i = j then 1 else 0) * z i < ∑ i, (f fun j => if i = j then 1 else 0) * v i
  rw [← key z, ← key v]
  exact (hfu z hz).trans huv

-- N16 (extremal_averaging)
theorem sign_from_separation (k : ℕ) (ρ : ℝ) (w : Fin k → ℝ) (u : Fin k → ℂ)
    (hsep : ∑ i, w i * (u i).re  < (1 - ρ) * ∑ i, |w i|) :
    ∃ i, ρ < ‖u i - (((if 0 ≤ w i then 1 else -1 : ℝ)) : ℂ)‖ := by
  by_contra h
  push_neg at h
  have hle : ∀ i, (1 - ρ) * |w i| ≤ w i * (u i).re := by
    intro i
    have h1 : |(u i - ((if 0 ≤ w i then 1 else -1 : ℝ) : ℂ)).re| ≤ ρ :=
      (Complex.abs_re_le_norm _).trans (h i)
    rw [Complex.sub_re, Complex.ofReal_re, abs_le] at h1
    split_ifs at h1 with hw
    · rw [abs_of_nonneg hw]; nlinarith
    · rw [abs_of_neg (not_le.mp hw)]; nlinarith [not_le.mp hw]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hle i)
  rw [← Finset.mul_sum] at hs
  linarith

-- N17 (two_structure_coupling)
theorem signs_prescribed_tolerance (C ρ : ℝ) (hC : 0 < C) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (k : ℕ) (t : Fin  k → ℝ)
    (hobs : ∃ v : Fin k → ℝ, (∀ i, |v i| ≤ 1) ∧
      ¬ ∃ f : ℂ → ℂ, Differentiable ℂ f ∧
        (∀ δ > (0:ℝ),  ∃ M : ℝ, ∀ z : ℂ, ‖f z‖ ≤ M * Real.exp ((Real.pi + δ) * ‖z‖)) ∧
        (∀ x : ℝ, ‖f (x : ℂ)‖ ≤ C / (1 - ρ)) ∧ ∀ i,  f (t i : ℂ) = (v i : ℂ)) :
    ∃ s : Fin k → ℝ, (∀ i, s i = 1 ∨ s i = -1) ∧
      ∀ f : ℂ → ℂ, Differentiable ℂ f  →
        (∀ δ > (0:ℝ), ∃ M : ℝ, ∀ z : ℂ, ‖f z‖ ≤ M * Real.exp ((Real.pi + δ) * ‖z‖)) →
        (∀ x : ℝ, ‖f (x :  ℂ)‖ ≤ C) → ∃ i, ρ < ‖f (t i : ℂ) - (s i : ℂ)‖ := by
  sorry

-- N18 (assembly)
theorem local_sign_obstruction :
    ∃ A0 > (0:ℝ), ∀ C > (0:ℝ), ∀ ρ : ℝ, 0 ≤ ρ → ρ < 1 →
      ∃ k : ℕ, Even  k ∧ 2 ≤ k ∧ (k:ℝ) ≤ Real.exp (A0 * (1 + C / (1 - ρ))) ∧
        ∀ (c : ℝ) (t : Fin k → ℝ), (∀ i, t i ∈ Set.Icc c (c  + (k:ℝ) + 1)) →
          ∃ s : Fin k → ℝ, (∀ i, s i = 1 ∨ s i = -1) ∧
            ∀ f : ℂ → ℂ, Differentiable ℂ f  →
              (∀ δ > (0:ℝ), ∃ M : ℝ, ∀ z : ℂ, ‖f z‖ ≤ M * Real.exp ((Real.pi + δ) * ‖z‖)) →
              (∀ x :  ℝ, ‖f (x : ℂ)‖ ≤ C) → ∃ i, ρ < ‖f (t i : ℂ) - (s i : ℂ)‖ := by
  obtain ⟨A0, hA0, heff⟩ := effective_finite_obstruction
  refine ⟨A0, hA0, fun C hC ρ hρ0 hρ1 => ?_⟩
  have hH : 0 < C / (1 - ρ) := div_pos hC (by linarith)
  obtain ⟨k, hk_even, hk2, hkle, hk⟩ := heff (C / (1 - ρ)) hH
  exact ⟨k, hk_even, hk2, hkle, fun c t ht =>
    signs_prescribed_tolerance C ρ hC hρ0 hρ1 k t (hk c t ht)⟩

-- N19 (algebraic_identity)
theorem norm_cos_le_exp_abs_im (w : ℂ) : ‖Complex.cos w‖ ≤ Real.exp |w.im| := by
  have h2 : 2 * Complex.cos w = Complex.exp (w * Complex.I) + Complex.exp (-w * Complex.I) :=
    Complex.two_cos w
  have hn : ‖2 * Complex.cos w‖ ≤ 2 * Real.exp |w.im| := by
    rw [h2]
    calc ‖Complex.exp (w * Complex.I) + Complex.exp (-w * Complex.I)‖
        ≤ ‖Complex.exp (w * Complex.I)‖ + ‖Complex.exp (-w * Complex.I)‖ := norm_add_le _ _
      _ = Real.exp (-w.im) + Real.exp (w.im) := by
          rw [Complex.norm_exp, Complex.norm_exp]; simp
      _ ≤ Real.exp |w.im| + Real.exp |w.im| := by
          gcongr
          · exact neg_le_abs _
          · exact le_abs_self _
      _ = 2 * Real.exp |w.im| := by ring
  rw [norm_mul, Complex.norm_two] at hn
  linarith

-- N20 (two_structure_coupling)
theorem poly_cos_exp_type (P : Polynomial ℝ) (D : ℝ) (hD : 0 < D) (hdeg : (P.natDegree : ℝ) ≤ D) :
    Differentiable  ℂ (fun z : ℂ => Polynomial.aeval (Complex.cos ((Real.pi : ℂ) * z / (D : ℂ))) P) ∧
    ∀ δ > (0:ℝ), ∃ M : ℝ, ∀ z : ℂ,
       ‖Polynomial.aeval (Complex.cos ((Real.pi : ℂ) * z / (D : ℂ))) P‖ ≤
        M * Real.exp ((Real.pi + δ) * ‖z‖)  := by
  refine ⟨?_, ?_⟩
  · exact P.differentiable_aeval.comp
      (Complex.differentiable_cos.comp ((differentiable_id.const_mul _).div_const _))
  · intro δ hδ
    have hS0 : 0 ≤ ∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖ :=
      Finset.sum_nonneg fun i _ => norm_nonneg _
    refine ⟨∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖, fun z => ?_⟩
    have hE1 : 1 ≤ Real.exp (Real.pi * ‖z‖ / D) := Real.one_le_exp (by positivity)
    have hcE : ‖Complex.cos ((Real.pi : ℂ) * z / (D : ℂ))‖ ≤ Real.exp (Real.pi * ‖z‖ / D) := by
      calc ‖Complex.cos ((Real.pi : ℂ) * z / (D : ℂ))‖
          ≤ Real.exp |((Real.pi : ℂ) * z / (D : ℂ)).im| := norm_cos_le_exp_abs_im _
        _ ≤ Real.exp (Real.pi * ‖z‖ / D) := by
          apply Real.exp_le_exp.mpr
          have e : (Real.pi : ℂ) * z / (D : ℂ) = ((Real.pi / D : ℝ) : ℂ) * z := by
            push_cast; ring
          rw [e, Complex.im_ofReal_mul, abs_mul, abs_of_pos (div_pos Real.pi_pos hD)]
          have e2 : Real.pi * ‖z‖ / D = Real.pi / D * ‖z‖ := by ring
          rw [e2]
          exact mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm z) (by positivity)
    have h1 : ‖Polynomial.aeval (Complex.cos ((Real.pi : ℂ) * z / (D : ℂ))) P‖ ≤
        (∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖) *
          Real.exp (Real.pi * ‖z‖ / D) ^ P.natDegree := by
      rw [Polynomial.aeval_eq_sum_range, Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
      rw [norm_smul, norm_pow]
      rw [Finset.mem_range] at hi
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      calc ‖Complex.cos ((Real.pi : ℂ) * z / (D : ℂ))‖ ^ i
          ≤ Real.exp (Real.pi * ‖z‖ / D) ^ i := pow_le_pow_left₀ (norm_nonneg _) hcE i
        _ ≤ Real.exp (Real.pi * ‖z‖ / D) ^ P.natDegree :=
          pow_le_pow_right₀ hE1 (Nat.lt_succ_iff.mp hi)
    have h2 : Real.exp (Real.pi * ‖z‖ / D) ^ P.natDegree ≤ Real.exp ((Real.pi + δ) * ‖z‖) := by
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have hq : (P.natDegree : ℝ) / D ≤ 1 := (div_le_one hD).mpr hdeg
      calc (P.natDegree : ℝ) * (Real.pi * ‖z‖ / D) = (P.natDegree / D) * (Real.pi * ‖z‖) := by ring
        _ ≤ 1 * (Real.pi * ‖z‖) := mul_le_mul_of_nonneg_right hq (by positivity)
        _ ≤ (Real.pi + δ) * ‖z‖ := by
          have := mul_nonneg hδ.le (norm_nonneg z)
          nlinarith
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hS0)

-- N21 (algebraic_identity)
theorem poly_cos_real_values (P : Polynomial ℝ) (D C : ℝ)
    (hC : ∀ z ∈ Set.Icc (-1:ℝ) 1, |P.eval z| ≤ C)  (t : ℝ) :
    Polynomial.aeval (Complex.cos ((Real.pi : ℂ) * (t : ℂ) / (D : ℂ))) P =
      ((P.eval (Real.cos (Real.pi  * t / D)) : ℝ) : ℂ) ∧
    ‖Polynomial.aeval (Complex.cos ((Real.pi : ℂ) * (t : ℂ) / (D : ℂ))) P‖ ≤ C := by
  have h1 : Complex.cos ((Real.pi : ℂ) * (t : ℂ) / (D : ℂ)) =
      ((Real.cos (Real.pi * t / D) : ℝ) : ℂ) := by
    push_cast; ring_nf
  have h2 : Polynomial.aeval (Complex.cos ((Real.pi : ℂ) * (t : ℂ) / (D : ℂ))) P =
      ((P.eval (Real.cos (Real.pi * t / D)) : ℝ) : ℂ) := by
    have h := Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval (A := ℂ)
      (Real.cos (Real.pi * t / D)) P
    rw [Complex.coe_algebraMap] at h
    rw [h1]; exact h
  refine ⟨h2, ?_⟩
  rw [h2, Complex.norm_real, Real.norm_eq_abs]
  exact hC _ ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

-- N22 (algebraic_identity)
theorem arccos_node (D x : ℝ) (hD : 0 < D) (hx : x ∈ Set.Icc (-1:ℝ) 1) :
    D / Real.pi * Real.arccos x ∈  Set.Icc 0 D ∧
    Real.cos (Real.pi * (D / Real.pi * Real.arccos x) / D) = x := by
  have hpi := Real.pi_pos
  refine ⟨⟨mul_nonneg (div_nonneg hD.le hpi.le) (Real.arccos_nonneg x), ?_⟩, ?_⟩
  · calc D / Real.pi * Real.arccos x ≤ D / Real.pi * Real.pi := by
          gcongr; exact Real.arccos_le_pi x
      _ = D := by field_simp
  · have : Real.pi * (D / Real.pi * Real.arccos x) / D = Real.arccos x := by
      field_simp
    rw [this]; exact Real.cos_arccos hx.1 hx.2

-- N23 (assembly)
theorem polynomial_to_bernstein (P : Polynomial ℝ) (D C : ℝ) (hD : 0 < D)
    (hdeg : (P.natDegree : ℝ) ≤ D)  (hC : ∀ z ∈ Set.Icc (-1:ℝ) 1, |P.eval z| ≤ C) :
    Differentiable ℂ (fun z : ℂ => Polynomial.aeval (Complex.cos ((Real.pi  : ℂ) * z / (D : ℂ))) P) ∧
    (∀ δ > (0:ℝ), ∃ M : ℝ, ∀ z : ℂ,
      ‖Polynomial.aeval (Complex.cos ((Real.pi : ℂ)  * z / (D : ℂ))) P‖ ≤
        M * Real.exp ((Real.pi + δ) * ‖z‖)) ∧
    (∀ x : ℝ, ‖Polynomial.aeval (Complex.cos ((Real.pi  : ℂ) * (x : ℂ) / (D : ℂ))) P‖ ≤ C) ∧
    (∀ x ∈ Set.Icc (-1:ℝ) 1,
      Polynomial.aeval (Complex.cos ((Real.pi :  ℂ) * ((D / Real.pi * Real.arccos x : ℝ) : ℂ) / (D : ℂ))) P =
        ((P.eval x : ℝ) : ℂ)) := by
  obtain ⟨hdiff, htype⟩ := poly_cos_exp_type P D hD hdeg
  refine ⟨hdiff, htype, fun x => (poly_cos_real_values P D C hC x).2, fun x hx => ?_⟩
  rw [(poly_cos_real_values P D C hC _).1, (arccos_node D x hD hx).2]

-- N24 (case_split)
theorem finset_split_into_blocks {α : Type*} [DecidableEq α] (k : ℕ) (hk : 1 ≤ k) (S : Finset α) :
    ∃ q  : ℕ, ∃ G : Fin q → Finset α,
      (∀ l, G l ⊆ S) ∧ (∀ l, (G l).card = k) ∧ (∀ l l', l ≠ l' → Disjoint (G l) (G l'))  ∧
      S.card ≤ k * q + (k - 1) := by
  sorry

-- N25 (extremal_averaging)
theorem bucket_grouping (n k N : ℕ) (hk : 1 ≤ k) (b : Fin n → Fin N) :
    ∃ q : ℕ, ∃ G : Fin q → Finset (Fin  n),
      (∀ l, (G l).card = k) ∧ (∀ l l', l ≠ l' → Disjoint (G l) (G l')) ∧
      (∀ l, ∃ j : Fin N, ∀ i ∈ G l, b  i = j) ∧ n ≤ k * q + (k - 1) * N := by
  sorry

-- N26 (algebraic_identity)
theorem bucket_interval (D t : ℝ) (k : ℕ) (hD : 0 < D) (hk : 1 ≤ k) (ht : t ∈ Set.Icc 0 D) :
    min ⌊t / ((k:ℝ)  + 1)⌋₊ (⌈D / ((k:ℝ) + 1)⌉₊ - 1) < ⌈D / ((k:ℝ) + 1)⌉₊ ∧
    t ∈ Set.Icc (((min ⌊t / ((k:ℝ) + 1)⌋₊ (⌈D / ((k:ℝ) + 1)⌉₊  - 1) : ℕ) : ℝ) * ((k:ℝ) + 1))
      (((min ⌊t / ((k:ℝ) + 1)⌋₊ (⌈D / ((k:ℝ) + 1)⌉₊ - 1) : ℕ) : ℝ) * ((k:ℝ) + 1) + ((k:ℝ)  + 1)) := by
  have hk1 : (0:ℝ) < (k:ℝ) + 1 := by positivity
  have hN : 0 < ⌈D / ((k:ℝ) + 1)⌉₊ := Nat.ceil_pos.mpr (by positivity)
  have ht0 : 0 ≤ t / ((k:ℝ) + 1) := div_nonneg ht.1 hk1.le
  refine ⟨?_, ?_, ?_⟩
  · calc min ⌊t / ((k:ℝ) + 1)⌋₊ (⌈D / ((k:ℝ) + 1)⌉₊ - 1) ≤ ⌈D / ((k:ℝ) + 1)⌉₊ - 1 :=
          min_le_right _ _
      _ < ⌈D / ((k:ℝ) + 1)⌉₊ := Nat.sub_lt hN one_pos
  · have hmin : ((min ⌊t / ((k:ℝ) + 1)⌋₊ (⌈D / ((k:ℝ) + 1)⌉₊ - 1) : ℕ) : ℝ) ≤
        (⌊t / ((k:ℝ) + 1)⌋₊ : ℝ) := by exact_mod_cast min_le_left _ _
    calc ((min ⌊t / ((k:ℝ) + 1)⌋₊ (⌈D / ((k:ℝ) + 1)⌉₊ - 1) : ℕ) : ℝ) * ((k:ℝ) + 1)
        ≤ (⌊t / ((k:ℝ) + 1)⌋₊ : ℝ) * ((k:ℝ) + 1) := mul_le_mul_of_nonneg_right hmin hk1.le
      _ ≤ t / ((k:ℝ) + 1) * ((k:ℝ) + 1) := mul_le_mul_of_nonneg_right (Nat.floor_le ht0) hk1.le
      _ = t := by field_simp
  · rcases le_total ⌊t / ((k:ℝ) + 1)⌋₊ (⌈D / ((k:ℝ) + 1)⌉₊ - 1) with h | h
    · rw [min_eq_left h]
      have h1 := Nat.lt_floor_add_one (t / ((k:ℝ) + 1))
      have h2 : t < ((⌊t / ((k:ℝ) + 1)⌋₊ : ℝ) + 1) * ((k:ℝ) + 1) := by
        rw [← div_lt_iff₀ hk1]; exact h1
      linarith
    · rw [min_eq_right h]
      have h1 : D ≤ (⌈D / ((k:ℝ) + 1)⌉₊ : ℝ) * ((k:ℝ) + 1) := by
        rw [← div_le_iff₀ hk1]; exact Nat.le_ceil _
      have h2 : ((⌈D / ((k:ℝ) + 1)⌉₊ - 1 : ℕ) : ℝ) = (⌈D / ((k:ℝ) + 1)⌉₊ : ℝ) - 1 := by
        rw [Nat.cast_sub hN, Nat.cast_one]
      rw [h2]
      linarith [ht.2]

-- N27 (assembly)
theorem angular_groups (n k : ℕ) (hk : 1 ≤ k) (D : ℝ) (hD : 0 < D) (x : Fin n → Set.Icc (-1:ℝ) 1) :
    ∃ q  : ℕ, ∃ G : Fin q → Finset (Fin n),
      (∀ l, (G l).card = k) ∧ (∀ l l', l ≠ l' → Disjoint (G l) (G l')) ∧
       (∀ l, ∃ c : ℝ, ∀ i ∈ G l, D / Real.pi * Real.arccos (x i : ℝ) ∈ Set.Icc c (c + (k:ℝ) + 1)) ∧
      (n : ℝ) ≤ (k:ℝ)  * q + ((k:ℝ) - 1) * (D / ((k:ℝ) + 1) + 1) := by
  sorry

-- N28 (extremal_averaging)
theorem disjoint_groups_card_le (n q : ℕ) (G : Fin q → Finset (Fin n))
    (hdisj : ∀ l l', l ≠ l' → Disjoint  (G l) (G l')) (E : Finset (Fin n))
    (hhit : ∀ l, ∃ i ∈ G l, i ∈ E) : q ≤ E.card := by
  choose g hgG hgE using hhit
  have hinj : Function.Injective g := by
    intro l l' h
    by_contra hne
    apply Finset.disjoint_left.mp (hdisj l l' hne) (hgG l)
    rw [h]; exact hgG l'
  calc q = (Finset.univ : Finset (Fin q)).card := by simp
    _ ≤ E.card := Finset.card_le_card_of_injOn g (fun l _ => hgE l) hinj.injOn

-- N29 (assembly)
theorem finite_degree_error_tradeoff (C ρ : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hsign : ∀ (c : ℝ) (t : Fin k → ℝ),  (∀ i, t i ∈ Set.Icc c (c + (k:ℝ) + 1)) →
      ∃ s : Fin k → ℝ, (∀ i, s i = 1 ∨ s i = -1) ∧
        ∀ f : ℂ → ℂ, Differentiable  ℂ f →
          (∀ δ > (0:ℝ), ∃ M : ℝ, ∀ z : ℂ, ‖f z‖ ≤ M * Real.exp ((Real.pi + δ) * ‖z‖)) →
          (∀ x : ℝ,  ‖f (x : ℂ)‖ ≤ C) → ∃ i, ρ < ‖f (t i : ℂ) - (s i : ℂ)‖)
    (n : ℕ) (D : ℝ) (hD : 0 < D) (x : Fin n → Set.Icc (-1:ℝ)  1) :
    ∃ y : Fin n → ℝ, (∀ i, y i = 1 ∨ y i = -1) ∧
      ∀ P : Polynomial ℝ, (P.natDegree : ℝ) ≤ D → (∀ z ∈ Set.Icc  (-1:ℝ) 1, |P.eval z| ≤ C) →
        (n : ℝ) / k - ((k:ℝ) - 1) / ((k:ℝ) * ((k:ℝ) + 1)) * D - ((k:ℝ) - 1) / k ≤
           ((Finset.univ.filter (fun i ↦ ρ < |P.eval (x i : ℝ) - y i|)).card : ℝ) := by
  sorry

-- N30 (algebraic_identity)
theorem theorem21_arithmetic (k n : ℕ) (hk : 2 ≤ k) (hn : 4 * k ^ 2 ≤ n) :
    1 / (8 * (k:ℝ) ^ 2) * n <
       (n : ℝ) / k - ((k:ℝ) - 1) / ((k:ℝ) * ((k:ℝ) + 1)) * ((1 + 1 / (8 * (k:ℝ) ^ 2)) * n) -
        ((k:ℝ) - 1) / k  := by
  have hk' : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hn' : 4 * (k:ℝ) ^ 2 ≤ n := by exact_mod_cast hn
  have hkpos : (0:ℝ) < k := by linarith
  have hk0 : (k:ℝ) ≠ 0 := hkpos.ne'
  have hk1 : (k:ℝ) + 1 ≠ 0 := by linarith
  rw [← sub_pos]
  have e : (n : ℝ) / k - ((k:ℝ) - 1) / ((k:ℝ) * ((k:ℝ) + 1)) * ((1 + 1 / (8 * (k:ℝ) ^ 2)) * n) -
      ((k:ℝ) - 1) / k - 1 / (8 * (k:ℝ) ^ 2) * n
      = ((15 * (k:ℝ)^2 - 2 * k + 1) * n - 8 * (k:ℝ)^2 * ((k:ℝ)^2 - 1)) /
        (8 * (k:ℝ)^3 * ((k:ℝ) + 1)) := by
    field_simp
    ring
  rw [e]
  apply div_pos
  · have h1 := mul_le_mul_of_nonneg_left hn' (by nlinarith : (0:ℝ) ≤ 15 * (k:ℝ)^2 - 2 * k + 1)
    have h2 : 0 < (k:ℝ)^2 * (52 * (k:ℝ)^2 - 8 * k + 12) := by
      apply mul_pos (by positivity); nlinarith
    nlinarith [h1, h2]
  · positivity

-- N31 (algebraic_identity)
theorem theorem21_constants (A0 : ℝ) (hA0 : 0 < A0) :
    ∃ A > (0:ℝ), ∀ H : ℝ, 0 ≤ H → ∀ k : ℕ, 2 ≤ k → (k:ℝ)  ≤ Real.exp (A0 * (1 + H)) →
      Real.exp (-(A * (1 + H))) ≤ 1 / (8 * (k:ℝ) ^ 2) ∧
      4 * (k:ℝ) ^ 2 ≤ Real.exp  (A * (1 + H)) := by
  refine ⟨2 * A0 + 3, by positivity, fun H hH k hk hkA => ?_⟩
  have hk' : (2:ℝ) ≤ k := by exact_mod_cast hk
  have he : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have h8 : (8:ℝ) ≤ Real.exp 3 := by
    have e3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e3]
    have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) he 3
    norm_num at this
    linarith
  have hk2 : (k:ℝ)^2 ≤ Real.exp (2 * A0 * (1 + H)) := by
    have e : Real.exp (2 * A0 * (1 + H)) = Real.exp (A0 * (1 + H)) * Real.exp (A0 * (1 + H)) := by
      rw [← Real.exp_add]; ring_nf
    rw [e, sq]
    exact mul_le_mul hkA hkA (by positivity) (Real.exp_pos _).le
  have hmain : 8 * (k:ℝ)^2 ≤ Real.exp ((2 * A0 + 3) * (1 + H)) := by
    have h1 : Real.exp 3 ≤ Real.exp (3 * (1 + H)) := Real.exp_le_exp.mpr (by nlinarith)
    have h2 : Real.exp ((2 * A0 + 3) * (1 + H)) =
        Real.exp (3 * (1 + H)) * Real.exp (2 * A0 * (1 + H)) := by
      rw [← Real.exp_add]; ring_nf
    rw [h2]
    calc 8 * (k:ℝ)^2 ≤ Real.exp 3 * Real.exp (2 * A0 * (1 + H)) :=
          mul_le_mul h8 hk2 (by positivity) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right h1 (by positivity)
  refine ⟨?_, ?_⟩
  · rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by positivity) hmain
  · nlinarith [sq_nonneg (k:ℝ)]

-- N32 (assembly)
theorem quantitative_robust_obstruction :
    ∃ A > (0:ℝ), ∀ C > (0:ℝ), ∀ ρ : ℝ, 0 ≤ ρ → ρ < 1 →
      ∃ ε  : ℝ, 0 < ε ∧ ε < 1 ∧ Real.exp (-(A * (1 + C / (1 - ρ)))) ≤ ε ∧
      ∃ n0 : ℕ, (n0 : ℝ) ≤ Real.exp (A * (1 + C / (1  - ρ))) ∧
        ∀ n : ℕ, n0 ≤ n → ∀ x : Fin n → Set.Icc (-1:ℝ) 1,
          ∃ y : Fin n → ℝ, (∀ i, y i = 1 ∨ y i  = -1) ∧
            ∀ P : Polynomial ℝ, (P.natDegree : ℝ) ≤ (1 + ε) * n →
              (∀ z ∈ Set.Icc (-1:ℝ) 1, |P.eval  z| ≤ C) →
              ε * n < ((Finset.univ.filter (fun i ↦ ρ < |P.eval (x i : ℝ) - y i|)).card : ℝ) := by
  obtain ⟨A0, hA0, hloc⟩ := local_sign_obstruction
  obtain ⟨A, hA, hconst⟩ := theorem21_constants A0 hA0
  refine ⟨A, hA, fun C hC ρ hρ0 hρ1 => ?_⟩
  have hH : 0 ≤ C / (1 - ρ) := div_nonneg hC.le (by linarith)
  obtain ⟨k, -, hk2, hkle, hsign⟩ := hloc C hC ρ hρ0 hρ1
  obtain ⟨hε, hn0⟩ := hconst (C / (1 - ρ)) hH k hk2 hkle
  have hk2r : (2:ℝ) ≤ k := by exact_mod_cast hk2
  have hkpos : (0:ℝ) < k := by linarith
  refine ⟨1 / (8 * (k:ℝ)^2), by positivity, ?_, hε, 4 * k^2, ?_, fun n hn x => ?_⟩
  · rw [div_lt_one (by positivity)]; nlinarith
  · push_cast; exact hn0
  · have hk1 : 1 ≤ k := by omega
    have hnpos : (0:ℝ) < n := by
      have h4 : 0 < 4 * k ^ 2 := by positivity
      have : 0 < n := lt_of_lt_of_le h4 hn
      exact_mod_cast this
    have hD : (0:ℝ) < (1 + 1 / (8 * (k:ℝ)^2)) * n := by positivity
    obtain ⟨y, hy, hP⟩ := finite_degree_error_tradeoff C ρ k hk1 hsign n _ hD x
    refine ⟨y, hy, fun P hdeg hb => ?_⟩
    have h1 := hP P hdeg hb
    have h2 := theorem21_arithmetic k n hk2 hn
    linarith

-- N33 (case_split)
theorem match_error_complement (n : ℕ) (P : Polynomial ℝ) (x : Fin n → Set.Icc (-1:ℝ) 1) (y : Fin n → ℝ) :
     ((Finset.univ.filter (fun i ↦ P.eval (x i : ℝ) = y i)).card : ℝ) +
      ((Finset.univ.filter (fun i ↦ (0:ℝ) < |P.eval  (x i : ℝ) - y i|)).card : ℝ) = n := by
  have h : (Finset.univ.filter (fun i ↦ (0:ℝ) < |P.eval (x i : ℝ) - y i|)) =
      Finset.univ.filter (fun i ↦ ¬ P.eval (x i : ℝ) = y i) := by
    apply Finset.filter_congr
    intro i _
    rw [abs_pos, sub_ne_zero]
  rw [h]
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun i ↦ P.eval (x i : ℝ) = y i)
  rw [Finset.card_univ, Fintype.card_fin] at this
  exact_mod_cast this

-- N34 (assembly)
theorem qualitative_robust_obstruction :
    ∀ C > (0:ℝ), ∃ ε : ℝ, 0 < ε ∧ ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x  : Fin n → Set.Icc (-1:ℝ) 1,
      ∃ y : Fin n → Set.Icc (-1:ℝ) 1,
        ∀ P : Polynomial ℝ, (P.natDegree : ℝ) ≤  (1 + ε) * n →
          (∀ z ∈ Set.Icc (-1:ℝ) 1, |P.eval z| ≤ C) →
          ε * n < ((Finset.univ.filter (fun i ↦  (0:ℝ) < |P.eval (x i : ℝ) - (y i : ℝ)|)).card : ℝ) := by
  intro C hC
  obtain ⟨A, hA, hmain⟩ := quantitative_robust_obstruction
  obtain ⟨ε, hε0, hε1, -, n0, -, hn⟩ := hmain C hC 0 le_rfl zero_lt_one
  refine ⟨ε, hε0, n0, fun n hn0 x => ?_⟩
  obtain ⟨y, hy, hP⟩ := hn n hn0 x
  refine ⟨fun i => ⟨y i, ?_⟩, fun P hdeg hb => hP P hdeg hb⟩
  rw [Set.mem_Icc]
  rcases hy i with h | h <;> rw [h] <;> constructor <;> norm_num

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
  intro C hC
  obtain ⟨ε, hε, n0, hmain⟩ := qualitative_robust_obstruction C hC
  refine ⟨ε, hε, ?_⟩
  rw [Filter.eventually_atTop]
  refine ⟨n0, fun n hn x => ?_⟩
  obtain ⟨y, hy⟩ := hmain n hn x
  refine ⟨y, fun P hdeg hcard => ?_⟩
  by_contra hcon
  push_neg at hcon
  have h1 := hy P hdeg.le hcon
  have h2 : ((Finset.univ.filter (fun i ↦ P.eval (x i : ℝ) = (y i : ℝ))).card : ℝ) +
      ((Finset.univ.filter (fun i ↦ (0:ℝ) < |P.eval (x i : ℝ) - (y i : ℝ)|)).card : ℝ) = n :=
    match_error_complement n P x (fun i => (y i : ℝ))
  linarith

end Erdos1133
