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

-- ===== Blueprint rooms (in blueprint order) =====

-- N01 bienvenu_prop21_uniform [literature_import]
theorem bienvenu_prop21_uniform (d t : ℕ) (A0 B0 L0 cV ε : ℝ) (hcV : 0 < cV) (hε : 0 < ε) :
    ∃ N0 : ℝ, ∀ (N : ℝ) (c : Fin t → ℤ) (L : Fin t → Fin d → ℤ) (K : Set (Fin d → ℝ))
      (β : ℕ → ℝ) (F : Finset (Fin d → ℤ)),
      N0 ≤ N →
      (∀ i j, i ≠ j → LinearIndependent ℚ ![fun k => (L i k : ℚ), fun k => (L j k : ℚ)]) →
      (∀ p : ℕ, β p = ((p : ℝ) / (p - 1)) ^ t / (p : ℝ) ^ d *
        ((Fintype.piFinset fun _ : Fin d => Finset.range p).filter
          (fun n => ∀ i, ¬ (p : ℤ) ∣ c i + ∑ j, L i j * (n j : ℤ))).card) →
      (∀ p : ℕ, p.Prime → 0 < β p) →
      ((∑ i, |(c i : ℝ)|) / N + ∑ i, ∑ j, |(L i j : ℝ)|) / Real.log N ^ B0 ≤ L0 →
      Convex ℝ K →
      (∀ v ∈ K, ∀ j, |v j| ≤ N) →
      cV * N ^ d * Real.log N ^ (-A0) ≤ (MeasureTheory.volume K).toReal →
      (∀ v ∈ K, ∀ i, N ^ ((9 : ℝ) / 10) ≤ (c i : ℝ) + ∑ j, (L i j : ℝ) * v j) →
      (∀ n : Fin d → ℤ, n ∈ F ↔ (fun j => (n j : ℝ)) ∈ K) →
      |(∑ n ∈ F, ∏ i, (if 0 < c i + (∑ j, L i j * n j) ∧ (c i + ∑ j, L i j * n j).natAbs.Prime
            then Real.log ((c i + ∑ j, L i j * n j : ℤ) : ℝ) else 0)) /
          ((MeasureTheory.volume K).toReal * ∏' p : Nat.Primes, β p) - 1| ≤ ε := by
  sorry

-- N02 bienvenu_lemma12_singular_series [literature_import]
theorem bienvenu_lemma12_singular_series (d t : ℕ) (c : Fin t → ℤ) (L : Fin t → Fin d → ℤ) (β : ℕ → ℝ)
    (hfc : ∀ i j, i ≠ j → LinearIndependent ℚ ![fun k => (L i k : ℚ), fun k => (L j k : ℚ)])
    (hβ : ∀ p : ℕ, β p = ((p : ℝ) / (p - 1)) ^ t / (p : ℝ) ^ d *
        ((Fintype.piFinset fun _ : Fin d => Finset.range p).filter
          (fun n => ∀ i, ¬ (p : ℤ) ∣ c i + ∑ j, L i j * (n j : ℤ))).card)
    (hpos : ∀ p : ℕ, p.Prime → 0 < β p) :
    Multipliable (fun p : Nat.Primes => β p) ∧ 0 < ∏' p : Nat.Primes, β p := by
  sorry

-- N03 sigma_values_triple [algebraic_identity]
theorem sigma_values_triple :
    σ 1 54000 = 193440 ∧ σ 1 111600 = 399776 ∧ σ 1 1828800 = 6551168 := by
  sorry

-- N04 sigma_mul_two_primes [algebraic_identity]
theorem sigma_mul_two_primes (K p r : ℕ) (hK : 0 < K) (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r)
    (hpK : ¬ p ∣ K) (hrK : ¬ r ∣ K) :
    σ 1 (K * (p * r)) = σ 1 K * ((p + 1) * (r + 1)) := by
  sorry

-- N05 shifted_product_identity [algebraic_identity]
theorem shifted_product_identity (p1 p2 p3 p4 p5 p6 : ℤ)
    (h22 : 15 * p1 * p2 + 31 * p3 * p4 = 508 * p5 * p6)
    (h23 : 15 * (p1 + p2) + 31 * (p3 + p4) - 508 * (p5 + p6) = 462) :
    15 * (p1 + 1) * (p2 + 1) + 31 * (p3 + 1) * (p4 + 1) = 508 * (p5 + 1) * (p6 + 1) := by
  sorry

-- N06 friendly_triple_activation [assembly]
theorem friendly_triple_activation (p : Fin 6 → ℕ) (hp : ∀ i, (p i).Prime ∧ 127 < p i)
    (hinj : Function.Injective p)
    (h22 : 15 * (p 0 * p 1) + 31 * (p 2 * p 3) = 508 * (p 4 * p 5))
    (h23 : 15 * (p 0 + p 1) + 31 * (p 2 + p 3) = 508 * (p 4 + p 5) + 462) :
    54000 * (p 0 * p 1) + 111600 * (p 2 * p 3) = 1828800 * (p 4 * p 5) ∧
    σ 1 (54000 * (p 0 * p 1)) + σ 1 (111600 * (p 2 * p 3)) = σ 1 (1828800 * (p 4 * p 5)) := by
  sorry

-- N07 core_from_sextuple [case_split]
theorem core_from_sextuple (p : Fin 6 → ℕ) (hp : ∀ i, (p i).Prime ∧ 127 < p i)
    (hinj : Function.Injective p)
    (h22 : 15 * (p 0 * p 1) + 31 * (p 2 * p 3) = 508 * (p 4 * p 5))
    (h23 : 15 * (p 0 + p 1) + 31 * (p 2 + p 3) = 508 * (p 4 + p 5) + 462) :
    Nat.Coprime (15 * (p 0 * p 1)) (31 * (p 2 * p 3)) ∧
    σ 1 (3600 * (15 * (p 0 * p 1))) + σ 1 (3600 * (31 * (p 2 * p 3))) =
      σ 1 (3600 * (15 * (p 0 * p 1) + 31 * (p 2 * p 3))) ∧
    (3600 * (15 * (p 0 * p 1)) * (31 * (p 2 * p 3)) * (15 * (p 0 * p 1) + 31 * (p 2 * p 3))).primeFactors.card ≤ 11 := by
  sorry

-- N08 core_fiber_le_eight [case_split]
theorem core_fiber_le_eight (Sx : Finset (Fin 6 → ℕ))
    (hS : ∀ p ∈ Sx, (∀ i, (p i).Prime ∧ 127 < p i) ∧ Function.Injective p ∧
      15 * (p 0 * p 1) + 31 * (p 2 * p 3) = 508 * (p 4 * p 5)) :
    Sx.card ≤ 8 * (Sx.image fun p => (15 * (p 0 * p 1), 31 * (p 2 * p 3))).card := by
  sorry

-- N09 multiplier_solution [algebraic_identity]
theorem multiplier_solution (u v g : ℕ) (hg : Nat.Coprime g (3600 * u * v * (u + v)))
    (h : σ 1 (3600 * u) + σ 1 (3600 * v) = σ 1 (3600 * (u + v))) :
    σ 1 (3600 * g * u) + σ 1 (3600 * g * v) = σ 1 (3600 * g * u + 3600 * g * v) := by
  sorry

-- N10 multiplier_disjoint [algebraic_identity]
theorem multiplier_disjoint (u v u' v' g g' : ℕ) (hu : 0 < u) (hv : 0 < v) (hu' : 0 < u') (hv' : 0 < v')
    (hcop : Nat.Coprime u v) (hcop' : Nat.Coprime u' v') (hg : 0 < g) (hg' : 0 < g')
    (h1 : 3600 * g * u = 3600 * g' * u') (h2 : 3600 * g * v = 3600 * g' * v') :
    g = g' ∧ u = u' ∧ v = v' := by
  sorry

-- N11 coprime_density [extremal_averaging]
theorem coprime_density : ∃ c6 X0 : ℝ, 0 < c6 ∧ ∀ (n : ℕ) (X : ℝ), n ≠ 0 → n.primeFactors.card ≤ 11 →
    X0 ≤ X → c6 * X ≤ ((Finset.Icc 1 ⌊X⌋₊).filter (fun g => Nat.Coprime g n)).card := by
  sorry

-- N12 S_ge_card [assembly]
theorem S_ge_card (x : ℝ) (F : Finset (ℕ × ℕ))
    (hF : ∀ ab ∈ F, 1 ≤ ab.1 ∧ 1 ≤ ab.2 ∧ (ab.1 : ℝ) + ab.2 ≤ x ∧ σ 1 ab.1 + σ 1 ab.2 = σ 1 (ab.1 + ab.2)) :
    (F.card : ℝ) ≤ S x := by
  sorry

-- N13 ruling_plane_identity [algebraic_identity]
theorem ruling_plane_identity (α β γ r s x1 x2 x3 x4 x5 x6 : ℝ)
    (hx1 : x1 = -1 + (1 / 15 - β) * r - γ * s)
    (hx2 : x2 = -1 - 462 * β + (-462 * β ^ 2 - β) * r + (α - 462 * β * γ - γ) * s)
    (hx3 : x3 = -1 - β * r + (1 / 31 - γ) * s)
    (hx4 : x4 = -1 - 462 * γ + (-α - 462 * β * γ - β) * r + (-462 * γ ^ 2 - γ) * s)
    (hx5 : x5 = -1 - β * r - γ * s)
    (hx6 : x6 = (15 * (x1 + x2) + 31 * (x3 + x4) - 508 * x5 - 462) / 508) :
    15 * x1 * x2 + 31 * x3 * x4 = 508 * x5 * x6 ∧
    15 * (x1 + x2) + 31 * (x3 + x4) - 508 * (x5 + x6) = 462 ∧
    508 * x6 = -(6930 * β + 14322 * γ + 46) +
      (-31 * α - 6930 * β ^ 2 - 14322 * β * γ + 416 * β + 1) * r +
      (15 * α - 6930 * β * γ - 14322 * γ ^ 2 + 416 * γ + 1) * s := by
  sorry

-- N14 determinant_table [algebraic_identity]
theorem determinant_table (α β γ a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 : ℝ)
    (ha1 : a1 = 1 / 15 - β) (hb1 : b1 = -γ)
    (ha2 : a2 = -462 * β ^ 2 - β) (hb2 : b2 = α - 462 * β * γ - γ)
    (ha3 : a3 = -β) (hb3 : b3 = 1 / 31 - γ)
    (ha4 : a4 = -α - 462 * β * γ - β) (hb4 : b4 = -462 * γ ^ 2 - γ)
    (ha5 : a5 = -β) (hb5 : b5 = -γ)
    (ha6 : a6 = (15 * (a1 + a2) + 31 * (a3 + a4) - 508 * a5) / 508)
    (hb6 : b6 = (15 * (b1 + b2) + 31 * (b3 + b4) - 508 * b5) / 508) :
    a1 * b2 - b1 * a2 = -(15 * α * β - α + 462 * β * γ + γ) / 15 ∧
    a1 * b3 - b1 * a3 = -(15 * β + 31 * γ - 1) / 465 ∧
    a1 * b4 - b1 * a4 = -γ * (15 * α + 462 * γ + 1) / 15 ∧
    a1 * b5 - b1 * a5 = -γ / 15 ∧
    a1 * b6 - b1 * a6 = -(15 * α + 462 * γ + 1) * (15 * β + 31 * γ - 1) / 7620 ∧
    a2 * b3 - b2 * a3 = β * (31 * α - 462 * β - 1) / 31 ∧
    a2 * b4 - b2 * a4 = α * (α + β - γ) ∧
    a2 * b5 - b2 * a5 = α * β ∧
    a2 * b6 - b2 * a6 = (α + β - γ) * (31 * α - 462 * β - 1) / 508 ∧
    a3 * b4 - b3 * a4 = -(31 * α * γ - α - 462 * β * γ - β) / 31 ∧
    a3 * b5 - b3 * a5 = β / 31 ∧
    a3 * b6 - b3 * a6 = -(31 * α - 462 * β - 1) * (15 * β + 31 * γ - 1) / 15748 ∧
    a4 * b5 - b4 * a5 = α * γ ∧
    a4 * b6 - b4 * a6 = -(α + β - γ) * (15 * α + 462 * γ + 1) / 508 ∧
    a5 * b6 - b5 * a6 = -(15 * α * β + 31 * α * γ + β - γ) / 508 := by
  sorry

-- N15 finite_complexity_real [case_split]
theorem finite_complexity_real (Z α β γ a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 : ℝ)
    (hZ : 100 ≤ Z) (hα1 : Z ^ 2 ≤ α) (hα2 : α ≤ 2 * Z ^ 2) (hβ1 : Z ≤ β) (hβ2 : β ≤ 2 * Z)
    (hγ1 : Z ≤ γ) (hγ2 : γ ≤ 2 * Z)
    (ha1 : a1 = 1 / 15 - β) (hb1 : b1 = -γ)
    (ha2 : a2 = -462 * β ^ 2 - β) (hb2 : b2 = α - 462 * β * γ - γ)
    (ha3 : a3 = -β) (hb3 : b3 = 1 / 31 - γ)
    (ha4 : a4 = -α - 462 * β * γ - β) (hb4 : b4 = -462 * γ ^ 2 - γ)
    (ha5 : a5 = -β) (hb5 : b5 = -γ)
    (ha6 : a6 = (15 * (a1 + a2) + 31 * (a3 + a4) - 508 * a5) / 508)
    (hb6 : b6 = (15 * (b1 + b2) + 31 * (b3 + b4) - 508 * b5) / 508) :
    a1 * b2 - b1 * a2 ≠ 0 ∧
    a1 * b3 - b1 * a3 ≠ 0 ∧
    a1 * b4 - b1 * a4 ≠ 0 ∧
    a1 * b5 - b1 * a5 ≠ 0 ∧
    a1 * b6 - b1 * a6 ≠ 0 ∧
    a2 * b3 - b2 * a3 ≠ 0 ∧
    a2 * b4 - b2 * a4 ≠ 0 ∧
    a2 * b5 - b2 * a5 ≠ 0 ∧
    a2 * b6 - b2 * a6 ≠ 0 ∧
    a3 * b4 - b3 * a4 ≠ 0 ∧
    a3 * b5 - b3 * a5 ≠ 0 ∧
    a3 * b6 - b3 * a6 ≠ 0 ∧
    a4 * b5 - b4 * a5 ≠ 0 ∧
    a4 * b6 - b4 * a6 ≠ 0 ∧
    a5 * b6 - b5 * a6 ≠ 0 := by
  sorry

-- N16 archimedean_bounds [extremal_averaging]
theorem archimedean_bounds : ∃ c C : ℝ, 0 < c ∧ c < C ∧
    ∀ (Z T α β γ r s x1 x2 x3 x4 x5 x6 : ℝ),
      100 ≤ Z → 10 ≤ T → Z ^ 2 ≤ α → α ≤ 2 * Z ^ 2 → Z ≤ β → β ≤ 2 * Z → Z ≤ γ → γ ≤ 2 * Z →
      -2 * T ≤ r → r ≤ -T → |s| ≤ 1 / 100000 * |r| →
      x1 = -1 + (1 / 15 - β) * r - γ * s →
      x2 = -1 - 462 * β + (-462 * β ^ 2 - β) * r + (α - 462 * β * γ - γ) * s →
      x3 = -1 - β * r + (1 / 31 - γ) * s →
      x4 = -1 - 462 * γ + (-α - 462 * β * γ - β) * r + (-462 * γ ^ 2 - γ) * s →
      x5 = -1 - β * r - γ * s →
      x6 = (15 * (x1 + x2) + 31 * (x3 + x4) - 508 * x5 - 462) / 508 →
      (c * Z * T ≤ x1 ∧ x1 ≤ C * Z * T ∧ c * Z * T ≤ x3 ∧ x3 ≤ C * Z * T ∧
       c * Z * T ≤ x5 ∧ x5 ≤ C * Z * T ∧
       c * Z ^ 2 * T ≤ x2 ∧ x2 ≤ C * Z ^ 2 * T ∧ c * Z ^ 2 * T ≤ x4 ∧ x4 ≤ C * Z ^ 2 * T ∧
       c * Z ^ 2 * T ≤ x6 ∧ x6 ≤ C * Z ^ 2 * T) := by
  sorry

-- N17 zero_form_criteria [algebraic_identity]
theorem zero_form_criteria {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (h7 : (7 : F) ≠ 0) (h11 : (11 : F) ≠ 0) (α β γ : F) :
    ((-1 - 462 * β = 0 ∧ -462 * β ^ 2 - β = 0 ∧ α - 462 * β * γ - γ = 0) ↔ (α = 0 ∧ 462 * β + 1 = 0)) ∧
    ((-1 - 462 * γ = 0 ∧ -α - 462 * β * γ - β = 0 ∧ -462 * γ ^ 2 - γ = 0) ↔ (α = 0 ∧ 462 * γ + 1 = 0)) ∧
    ((6930 * β + 14322 * γ + 46 = 0 ∧
      -31 * α - 6930 * β ^ 2 - 14322 * β * γ + 416 * β + 1 = 0 ∧
      15 * α - 6930 * β * γ - 14322 * γ ^ 2 + 416 * γ + 1 = 0) ↔
     (31 * α - 462 * β - 1 = 0 ∧ 15 * α + 462 * γ + 1 = 0)) := by
  sorry

-- N18 integral_lift [algebraic_identity]
theorem integral_lift (OnPl : ℤ → ℤ → ℤ → ℤ → (Fin 6 → ℤ) → Prop)
    (hOnPl : ∀ q A B C (x : Fin 6 → ℤ), OnPl q A B C x ↔
      (q * (x 1 - x 4) = 31 * A * (x 2 - x 4) + 462 * B * x 4 ∧
       q * (x 3 - x 4) = -15 * A * (x 0 - x 4) + 462 * C * x 4 ∧
       q * (x 4 + 1) = -(15 * B * (x 0 - x 4) + 31 * C * (x 2 - x 4)) ∧
       508 * x 5 = 15 * (x 0 + x 1) + 31 * (x 2 + x 3) - 508 * x 4 - 462))
    (q A B C : ℤ) (x : Fin 6 → ℤ) (hq : q ≠ 0) (hx : OnPl q A B C x) :
    ∀ α β γ r s : ℝ, α = A / q → β = B / q → γ = C / q →
      r = 15 * ((x 0 : ℝ) - x 4) → s = 31 * ((x 2 : ℝ) - x 4) →
      (x 0 : ℝ) = -1 + (1 / 15 - β) * r - γ * s ∧
      (x 1 : ℝ) = -1 - 462 * β + (-462 * β ^ 2 - β) * r + (α - 462 * β * γ - γ) * s ∧
      (x 2 : ℝ) = -1 - β * r + (1 / 31 - γ) * s ∧
      (x 3 : ℝ) = -1 - 462 * γ + (-α - 462 * β * γ - β) * r + (-462 * γ ^ 2 - γ) * s ∧
      (x 4 : ℝ) = -1 - β * r - γ * s ∧
      (x 5 : ℝ) = (15 * ((x 0 : ℝ) + x 1) + 31 * ((x 2 : ℝ) + x 3) - 508 * (x 4 : ℝ) - 462) / 508 := by
  sorry

-- N19 onPlane_equations [algebraic_identity]
theorem onPlane_equations (OnPl : ℤ → ℤ → ℤ → ℤ → (Fin 6 → ℤ) → Prop)
    (hOnPl : ∀ q A B C (x : Fin 6 → ℤ), OnPl q A B C x ↔
      (q * (x 1 - x 4) = 31 * A * (x 2 - x 4) + 462 * B * x 4 ∧
       q * (x 3 - x 4) = -15 * A * (x 0 - x 4) + 462 * C * x 4 ∧
       q * (x 4 + 1) = -(15 * B * (x 0 - x 4) + 31 * C * (x 2 - x 4)) ∧
       508 * x 5 = 15 * (x 0 + x 1) + 31 * (x 2 + x 3) - 508 * x 4 - 462))
    (q A B C : ℤ) (x : Fin 6 → ℤ) (hq : q ≠ 0) (hx : OnPl q A B C x) :
    15 * x 0 * x 1 + 31 * x 2 * x 3 = 508 * x 4 * x 5 ∧
    15 * (x 0 + x 1) + 31 * (x 2 + x 3) - 508 * (x 4 + x 5) = 462 := by
  sorry

-- N20 good_coprime [case_split]
theorem good_coprime (Good : ℝ → ℕ → ℤ → ℤ → ℤ → Prop)
    (hGood : ∀ Z q A B C, Good Z q A B C ↔
      ((4619990760 : ℤ) ∣ A ∧ (4619990760 : ℤ) ∣ B ∧ (4619990760 : ℤ) ∣ C ∧
       (q : ℝ) * Z ^ 2 ≤ A ∧ (A : ℝ) < 2 * q * Z ^ 2 ∧
       (q : ℝ) * Z ≤ B ∧ (B : ℝ) < 2 * q * Z ∧
       (q : ℝ) * Z ≤ C ∧ (C : ℝ) < 2 * q * Z ∧
       (∀ p : ℕ, p.Prime → p ∣ q →
         ¬ (p : ℤ) ∣ A * B * C * (462 * C + 15 * A) * (31 * A - 462 * B) * (15 * B + 31 * C)) ∧
       (∀ p : ℕ, p.Prime → ¬ p ∣ 4619990760 * q →
         ¬ (((p : ℤ) ∣ A ∧ (p : ℤ) ∣ 462 * B + q) ∨ ((p : ℤ) ∣ A ∧ (p : ℤ) ∣ 462 * C + q) ∨
           ((p : ℤ) ∣ 31 * A - 462 * B - q ∧ (p : ℤ) ∣ 15 * A + 462 * C + q)))))
    (Z : ℝ) (q : ℕ) (A B C : ℤ) (hG : Good Z q A B C) :
    IsCoprime A (q : ℤ) ∧ IsCoprime B (q : ℤ) ∧ IsCoprime C (q : ℤ) ∧ IsCoprime (A * B * C) (q : ℤ) := by
  sorry

-- N21 local_witness [algebraic_identity]
theorem local_witness (OnPl : ℤ → ℤ → ℤ → ℤ → (Fin 6 → ℤ) → Prop)
    (hOnPl : ∀ q A B C (x : Fin 6 → ℤ), OnPl q A B C x ↔
      (q * (x 1 - x 4) = 31 * A * (x 2 - x 4) + 462 * B * x 4 ∧
       q * (x 3 - x 4) = -15 * A * (x 0 - x 4) + 462 * C * x 4 ∧
       q * (x 4 + 1) = -(15 * B * (x 0 - x 4) + 31 * C * (x 2 - x 4)) ∧
       508 * x 5 = 15 * (x 0 + x 1) + 31 * (x 2 + x 3) - 508 * x 4 - 462))
    (q : ℕ) (A B C : ℤ) (hq1 : 1 ≤ q) (hqW : q % 4619990760 = 1) (hA : (4619990760 : ℤ) ∣ A) (hB : (4619990760 : ℤ) ∣ B) (hC : (4619990760 : ℤ) ∣ C)
    (hCq : IsCoprime C (q : ℤ)) :
    ∃ x : Fin 6 → ℤ, OnPl q A B C x ∧ ∀ p : ℕ, p.Prime → p ∣ 4619990760 → ∀ i, ¬ (p : ℤ) ∣ x i := by
  sorry

-- N22 projected_index [two_structure_coupling]
theorem projected_index (OnPl : ℤ → ℤ → ℤ → ℤ → (Fin 6 → ℤ) → Prop)
    (hOnPl : ∀ q A B C (x : Fin 6 → ℤ), OnPl q A B C x ↔
      (q * (x 1 - x 4) = 31 * A * (x 2 - x 4) + 462 * B * x 4 ∧
       q * (x 3 - x 4) = -15 * A * (x 0 - x 4) + 462 * C * x 4 ∧
       q * (x 4 + 1) = -(15 * B * (x 0 - x 4) + 31 * C * (x 2 - x 4)) ∧
       508 * x 5 = 15 * (x 0 + x 1) + 31 * (x 2 + x 3) - 508 * x 4 - 462))
    (q : ℕ) (A B C : ℤ) (hq1 : 1 ≤ q) (hqW : q % 4619990760 = 1) (hA : (4619990760 : ℤ) ∣ A) (hB : (4619990760 : ℤ) ∣ B) (hC : (4619990760 : ℤ) ∣ C)
    (hcop : IsCoprime (A * B * C) (q : ℤ)) :
    ∃ (z : ℤ × ℤ) (Γ : AddSubgroup (ℤ × ℤ)) (δ : ℕ), δ ∣ 508 ∧ Γ.index = q ^ 2 * δ ∧
      ∀ y : ℤ × ℤ, (∃ x : Fin 6 → ℤ, OnPl q A B C x ∧ x 0 - x 4 = y.1 ∧ x 2 - x 4 = y.2) ↔ y - z ∈ Γ := by
  sorry

-- N23 lattice_coords [extremal_averaging]
theorem lattice_coords (OnPl : ℤ → ℤ → ℤ → ℤ → (Fin 6 → ℤ) → Prop)
    (hOnPl : ∀ q A B C (x : Fin 6 → ℤ), OnPl q A B C x ↔
      (q * (x 1 - x 4) = 31 * A * (x 2 - x 4) + 462 * B * x 4 ∧
       q * (x 3 - x 4) = -15 * A * (x 0 - x 4) + 462 * C * x 4 ∧
       q * (x 4 + 1) = -(15 * B * (x 0 - x 4) + 31 * C * (x 2 - x 4)) ∧
       508 * x 5 = 15 * (x 0 + x 1) + 31 * (x 2 + x 3) - 508 * x 4 - 462)) :
    ∃ C0 C1 C2 : ℝ, 0 < C1 ∧ ∀ (q : ℕ) (A B C : ℤ) (Z T : ℝ),
      1 ≤ q → q % 4619990760 = 1 → (4619990760 : ℤ) ∣ A → (4619990760 : ℤ) ∣ B → (4619990760 : ℤ) ∣ C →
      IsCoprime (A * B * C) (q : ℤ) → 100 ≤ Z →
      (q : ℝ) * Z ^ 2 ≤ A → (A : ℝ) < 2 * q * Z ^ 2 → (q : ℝ) * Z ≤ B → (B : ℝ) < 2 * q * Z →
      (q : ℝ) * Z ≤ C → (C : ℝ) < 2 * q * Z → C0 * (q : ℝ) ^ 2 ≤ T →
      ∃ (c : Fin 6 → ℤ) (L : Fin 6 → Fin 2 → ℤ) (δ : ℕ), δ ∣ 508 ∧
        (∀ n : Fin 2 → ℤ, OnPl q A B C (fun i => c i + ∑ j, L i j * n j)) ∧
        (∀ x, OnPl q A B C x → ∃! n : Fin 2 → ℤ, x = fun i => c i + ∑ j, L i j * n j) ∧
        |15 * (L 0 0 - L 4 0) * (31 * (L 2 1 - L 4 1)) - 15 * (L 0 1 - L 4 1) * (31 * (L 2 0 - L 4 0))| = 465 * (q : ℤ) ^ 2 * δ ∧
        (∀ i, |(c i : ℝ)| ≤ C2 * Z ^ 2 * (q : ℝ) ^ 2 ∧ ∀ j, |(L i j : ℝ)| ≤ C2 * Z ^ 2 * (q : ℝ) ^ 2) ∧
        ∀ K : Set (Fin 2 → ℝ),
          (∀ v, v ∈ K ↔
            (-2 * T ≤ 15 * (((c 0 : ℝ) + ∑ j, (L 0 j : ℝ) * v j) - ((c 4 : ℝ) + ∑ j, (L 4 j : ℝ) * v j)) ∧ 15 * (((c 0 : ℝ) + ∑ j, (L 0 j : ℝ) * v j) - ((c 4 : ℝ) + ∑ j, (L 4 j : ℝ) * v j)) ≤ -T ∧
             |31 * (((c 2 : ℝ) + ∑ j, (L 2 j : ℝ) * v j) - ((c 4 : ℝ) + ∑ j, (L 4 j : ℝ) * v j))| ≤ 1 / 100000 * |15 * (((c 0 : ℝ) + ∑ j, (L 0 j : ℝ) * v j) - ((c 4 : ℝ) + ∑ j, (L 4 j : ℝ) * v j))|)) →
          Convex ℝ K ∧
          MeasureTheory.volume K = ENNReal.ofReal (3 / 100000 * T ^ 2 / (465 * (q : ℝ) ^ 2 * δ)) ∧
          ∀ v ∈ K, ∀ j, |v j| ≤ C1 * T := by
  sorry

-- N24 region_bounds_int [assembly]
theorem region_bounds_int (OnPl : ℤ → ℤ → ℤ → ℤ → (Fin 6 → ℤ) → Prop)
    (hOnPl : ∀ q A B C (x : Fin 6 → ℤ), OnPl q A B C x ↔
      (q * (x 1 - x 4) = 31 * A * (x 2 - x 4) + 462 * B * x 4 ∧
       q * (x 3 - x 4) = -15 * A * (x 0 - x 4) + 462 * C * x 4 ∧
       q * (x 4 + 1) = -(15 * B * (x 0 - x 4) + 31 * C * (x 2 - x 4)) ∧
       508 * x 5 = 15 * (x 0 + x 1) + 31 * (x 2 + x 3) - 508 * x 4 - 462))
    (InReg : ℝ → (Fin 6 → ℤ) → Prop)
    (hInReg : ∀ T (x : Fin 6 → ℤ), InReg T x ↔
      (-2 * T ≤ 15 * ((x 0 : ℝ) - x 4) ∧ 15 * ((x 0 : ℝ) - x 4) ≤ -T ∧
       |31 * ((x 2 : ℝ) - x 4)| ≤ 1 / 100000 * |15 * ((x 0 : ℝ) - x 4)|)) :
    ∃ cl Cu ch Ch : ℝ, 0 < cl ∧ 0 < ch ∧ ch < Ch ∧ ∀ (q : ℕ) (A B C : ℤ) (Z T : ℝ) (x : Fin 6 → ℤ),
      1 ≤ q → 100 ≤ Z → 10 ≤ T →
      (q : ℝ) * Z ^ 2 ≤ A → (A : ℝ) ≤ 2 * q * Z ^ 2 → (q : ℝ) * Z ≤ B → (B : ℝ) ≤ 2 * q * Z →
      (q : ℝ) * Z ≤ C → (C : ℝ) ≤ 2 * q * Z → OnPl q A B C x → InReg T x →
      (cl * Z * T ≤ x 0 ∧ cl * Z * T ≤ x 2 ∧ cl * Z * T ≤ x 4 ∧
       cl * Z ^ 2 * T ≤ x 1 ∧ cl * Z ^ 2 * T ≤ x 3 ∧ cl * Z ^ 2 * T ≤ x 5 ∧
       (∀ i, (x i : ℝ) ≤ Cu * Z ^ 2 * T) ∧
       ch * Z ^ 3 * T ^ 2 ≤ 508 * (x 4 : ℝ) * x 5 ∧ 508 * (x 4 : ℝ) * x 5 ≤ Ch * Z ^ 3 * T ^ 2) := by
  sorry

-- N25 sqfree_progression_count [extremal_averaging]
theorem sqfree_progression_count : ∃ csf Q1 : ℝ, 0 < csf ∧ ∀ Q : ℝ, Q1 ≤ Q →
    ∃ F : Finset ℕ, (∀ q ∈ F, Q ≤ q ∧ (q : ℝ) ≤ 2 * Q ∧ q % 4619990760 = 1 ∧ Squarefree q) ∧ csf * Q ≤ F.card := by
  sorry

-- N26 H_sum_bound [extremal_averaging]
theorem H_sum_bound : ∃ CH Q1 : ℝ, ∀ Q : ℝ, Q1 ≤ Q →
    ∑ q ∈ (Finset.Icc ⌈Q⌉₊ ⌊2 * Q⌋₊).filter (fun q => q % 4619990760 = 1),
      ∑ p ∈ q.primeFactors, (1 : ℝ) / p ≤ CH * Q := by
  sorry

-- N27 good_denominators [extremal_averaging]
theorem good_denominators : ∃ M0 cW Q0 : ℝ, 0 < cW ∧ ∀ Q : ℝ, Q0 ≤ Q →
    ∃ F : Finset ℕ, (∀ q ∈ F, Q ≤ q ∧ (q : ℝ) ≤ 2 * Q ∧ q % 4619990760 = 1 ∧ Squarefree q ∧
      ∑ p ∈ q.primeFactors, (1 : ℝ) / p ≤ M0) ∧ cW * Q ≤ F.card := by
  sorry

-- N28 residue_blocks [extremal_averaging]
theorem residue_blocks (m : ℕ) [NeZero m] (Ω : Finset (ZMod m × ZMod m × ZMod m))
    (a1 a2 a3 : ℤ) (L1 L2 L3 : ℕ) :
    Ω.card * ((L1 / m - 1) * (L2 / m - 1) * (L3 / m - 1)) ≤
      ((Finset.Ico a1 (a1 + L1) ×ˢ (Finset.Ico a2 (a2 + L2) ×ˢ Finset.Ico a3 (a3 + L3))).filter
        (fun x => ((x.1 : ZMod m), (x.2.1 : ZMod m), (x.2.2 : ZMod m)) ∈ Ω)).card := by
  sorry

-- N29 local_density [case_split]
theorem local_density (M0 : ℝ) : ∃ ϑ : ℝ, 0 < ϑ ∧ ∀ (q P m : ℕ), Squarefree q → q % 4619990760 = 1 →
    ∑ p ∈ q.primeFactors, (1 : ℝ) / p ≤ M0 →
    m = q * ∏ p ∈ (Finset.range (P + 1)).filter (fun p => p.Prime ∧ ¬ p ∣ 4619990760 * q), p →
    ∃ Ω : Finset (ZMod m × ZMod m × ZMod m), ϑ * (m : ℝ) ^ 3 ≤ Ω.card ∧
      ∀ a b c : ℤ, ((a : ZMod m), (b : ZMod m), (c : ZMod m)) ∈ Ω →
        (∀ p : ℕ, p.Prime → p ∣ q →
          ¬ (p : ℤ) ∣ (4619990760 * a) * (4619990760 * b) * (4619990760 * c) *
            (462 * (4619990760 * c) + 15 * (4619990760 * a)) * (31 * (4619990760 * a) - 462 * (4619990760 * b)) *
            (15 * (4619990760 * b) + 31 * (4619990760 * c))) ∧
        (∀ p : ℕ, p.Prime → p ≤ P → ¬ p ∣ 4619990760 * q →
          ¬ (((p : ℤ) ∣ 4619990760 * a ∧ (p : ℤ) ∣ 462 * (4619990760 * b) + q) ∨
             ((p : ℤ) ∣ 4619990760 * a ∧ (p : ℤ) ∣ 462 * (4619990760 * c) + q) ∨
             ((p : ℤ) ∣ 31 * (4619990760 * a) - 462 * (4619990760 * b) - q ∧
              (p : ℤ) ∣ 15 * (4619990760 * a) + 462 * (4619990760 * c) + q))) := by
  sorry

-- N30 large_prime_tail [extremal_averaging]
theorem large_prime_tail : ∃ Ct : ℝ, ∀ (q P : ℕ) (Z : ℝ), 2 ≤ q → 100 ≤ Z → 1 ≤ P →
    ∀ F : Finset (ℤ × ℤ × ℤ), (∀ t ∈ F, (q : ℝ) * Z ^ 2 ≤ t.1 ∧ (t.1 : ℝ) < 2 * q * Z ^ 2 ∧
        (q : ℝ) * Z ≤ t.2.1 ∧ (t.2.1 : ℝ) < 2 * q * Z ∧ (q : ℝ) * Z ≤ t.2.2 ∧ (t.2.2 : ℝ) < 2 * q * Z ∧
        ∃ p : ℕ, p.Prime ∧ P < p ∧ ¬ p ∣ 4619990760 * q ∧
          (((p : ℤ) ∣ t.1 ∧ (p : ℤ) ∣ 462 * t.2.1 + q) ∨ ((p : ℤ) ∣ t.1 ∧ (p : ℤ) ∣ 462 * t.2.2 + q) ∨
           ((p : ℤ) ∣ 31 * t.1 - 462 * t.2.1 - q ∧ (p : ℤ) ∣ 15 * t.1 + 462 * t.2.2 + q))) →
      (F.card : ℝ) ≤ Ct * ((q : ℝ) ^ 3 * Z ^ 4 / P + (q : ℝ) ^ 2 * Z ^ 3 * Real.log (q * Z) + (q : ℝ) ^ 2 * Z ^ 4) := by
  sorry

-- N31 parameter_sieve [assembly]
theorem parameter_sieve (Good : ℝ → ℕ → ℤ → ℤ → ℤ → Prop)
    (hGood : ∀ Z q A B C, Good Z q A B C ↔
      ((4619990760 : ℤ) ∣ A ∧ (4619990760 : ℤ) ∣ B ∧ (4619990760 : ℤ) ∣ C ∧
       (q : ℝ) * Z ^ 2 ≤ A ∧ (A : ℝ) < 2 * q * Z ^ 2 ∧
       (q : ℝ) * Z ≤ B ∧ (B : ℝ) < 2 * q * Z ∧
       (q : ℝ) * Z ≤ C ∧ (C : ℝ) < 2 * q * Z ∧
       (∀ p : ℕ, p.Prime → p ∣ q →
         ¬ (p : ℤ) ∣ A * B * C * (462 * C + 15 * A) * (31 * A - 462 * B) * (15 * B + 31 * C)) ∧
       (∀ p : ℕ, p.Prime → ¬ p ∣ 4619990760 * q →
         ¬ (((p : ℤ) ∣ A ∧ (p : ℤ) ∣ 462 * B + q) ∨ ((p : ℤ) ∣ A ∧ (p : ℤ) ∣ 462 * C + q) ∨
           ((p : ℤ) ∣ 31 * A - 462 * B - q ∧ (p : ℤ) ∣ 15 * A + 462 * C + q))))) (M0 : ℝ) :
    ∃ Z0 q0 c2 : ℝ, 100 ≤ Z0 ∧ 0 < c2 ∧ ∀ (q : ℕ) (Z : ℝ),
      Squarefree q → q % 4619990760 = 1 → ∑ p ∈ q.primeFactors, (1 : ℝ) / p ≤ M0 → q0 ≤ q → Z0 ≤ Z →
      ∃ F : Finset (ℤ × ℤ × ℤ), (∀ t ∈ F, Good Z q t.1 t.2.1 t.2.2) ∧ c2 * (q : ℝ) ^ 3 * Z ^ 4 ≤ F.card := by
  sorry

-- N32 planes_meet_once [algebraic_identity]
theorem planes_meet_once (OnPl : ℤ → ℤ → ℤ → ℤ → (Fin 6 → ℤ) → Prop)
    (hOnPl : ∀ q A B C (x : Fin 6 → ℤ), OnPl q A B C x ↔
      (q * (x 1 - x 4) = 31 * A * (x 2 - x 4) + 462 * B * x 4 ∧
       q * (x 3 - x 4) = -15 * A * (x 0 - x 4) + 462 * C * x 4 ∧
       q * (x 4 + 1) = -(15 * B * (x 0 - x 4) + 31 * C * (x 2 - x 4)) ∧
       508 * x 5 = 15 * (x 0 + x 1) + 31 * (x 2 + x 3) - 508 * x 4 - 462))
    (q q' A B C A' B' C' : ℤ) (x x' : Fin 6 → ℤ) (hq : 0 < q) (hq' : 0 < q')
    (hA : IsCoprime A q) (hB : IsCoprime B q) (hC : IsCoprime C q)
    (hA' : IsCoprime A' q') (hB' : IsCoprime B' q') (hC' : IsCoprime C' q')
    (hne : (q, A, B, C) ≠ (q', A', B', C'))
    (h1 : OnPl q A B C x) (h2 : OnPl q A B C x') (h3 : OnPl q' A' B' C' x) (h4 : OnPl q' A' B' C' x') :
    x = x' := by
  sorry

-- N33 union_card_bound [extremal_averaging]
theorem union_card_bound {ι α : Type*} [DecidableEq α] (s : Finset ι) (f : ι → Finset α)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (f i ∩ f j).card ≤ 1) :
    ∑ i ∈ s, (f i).card ≤ (s.biUnion f).card + s.card.choose 2 := by
  sorry

-- N34 lattice_reduction [algebraic_identity]
theorem lattice_reduction {ι : Type*} [Fintype ι] (p : ℕ) (L L' : AddSubgroup (ι → ℤ)) (hle : L' ≤ L)
    (hp : ¬ p ∣ L'.relIndex L) :
    (∀ x ∈ L, ∃ y ∈ L', ∃ z ∈ L, x = y + p • z) ∧
    (∀ y ∈ L', (∃ z ∈ L, y = p • z) → ∃ z' ∈ L', y = p • z') := by
  sorry

-- N35 nonzero_forms_count [extremal_averaging]
theorem nonzero_forms_count (p : ℕ) (hp : p.Prime) (c : Fin 6 → ℤ) (L : Fin 6 → Fin 2 → ℤ)
    (hnz : ∀ i, ¬ ((p : ℤ) ∣ c i ∧ ∀ j, (p : ℤ) ∣ L i j)) :
    p ^ 2 - 6 * p ≤ ((Fintype.piFinset fun _ : Fin 2 => Finset.range p).filter
      (fun n => ∀ i, ¬ (p : ℤ) ∣ c i + ∑ j, L i j * (n j : ℤ))).card := by
  sorry

-- N36 local_W [assembly]
theorem local_W (OnPl : ℤ → ℤ → ℤ → ℤ → (Fin 6 → ℤ) → Prop)
    (hOnPl : ∀ q A B C (x : Fin 6 → ℤ), OnPl q A B C x ↔
      (q * (x 1 - x 4) = 31 * A * (x 2 - x 4) + 462 * B * x 4 ∧
       q * (x 3 - x 4) = -15 * A * (x 0 - x 4) + 462 * C * x 4 ∧
       q * (x 4 + 1) = -(15 * B * (x 0 - x 4) + 31 * C * (x 2 - x 4)) ∧
       508 * x 5 = 15 * (x 0 + x 1) + 31 * (x 2 + x 3) - 508 * x 4 - 462))
    (q : ℕ) (A B C : ℤ) (hq1 : 1 ≤ q) (hqW : q % 4619990760 = 1) (hA : (4619990760 : ℤ) ∣ A) (hB : (4619990760 : ℤ) ∣ B) (hC : (4619990760 : ℤ) ∣ C)
    (hCq : IsCoprime C (q : ℤ)) (c : Fin 6 → ℤ) (L : Fin 6 → Fin 2 → ℤ)
    (hpar : ∀ n : Fin 2 → ℤ, OnPl q A B C (fun i => c i + ∑ j, L i j * n j))
    (hsurj : ∀ x, OnPl q A B C x → ∃ n : Fin 2 → ℤ, x = fun i => c i + ∑ j, L i j * n j) :
    ∀ p : ℕ, p.Prime → p ∣ 4619990760 →
      ∃ n : Fin 2 → ℕ, (∀ j, n j < p) ∧ ∀ i, ¬ (p : ℤ) ∣ c i + ∑ j, L i j * (n j : ℤ) := by
  sorry

-- N37 local_away [two_structure_coupling]
theorem local_away (OnPl : ℤ → ℤ → ℤ → ℤ → (Fin 6 → ℤ) → Prop)
    (hOnPl : ∀ q A B C (x : Fin 6 → ℤ), OnPl q A B C x ↔
      (q * (x 1 - x 4) = 31 * A * (x 2 - x 4) + 462 * B * x 4 ∧
       q * (x 3 - x 4) = -15 * A * (x 0 - x 4) + 462 * C * x 4 ∧
       q * (x 4 + 1) = -(15 * B * (x 0 - x 4) + 31 * C * (x 2 - x 4)) ∧
       508 * x 5 = 15 * (x 0 + x 1) + 31 * (x 2 + x 3) - 508 * x 4 - 462))
    (Good : ℝ → ℕ → ℤ → ℤ → ℤ → Prop)
    (hGood : ∀ Z q A B C, Good Z q A B C ↔
      ((4619990760 : ℤ) ∣ A ∧ (4619990760 : ℤ) ∣ B ∧ (4619990760 : ℤ) ∣ C ∧
       (q : ℝ) * Z ^ 2 ≤ A ∧ (A : ℝ) < 2 * q * Z ^ 2 ∧
       (q : ℝ) * Z ≤ B ∧ (B : ℝ) < 2 * q * Z ∧
       (q : ℝ) * Z ≤ C ∧ (C : ℝ) < 2 * q * Z ∧
       (∀ p : ℕ, p.Prime → p ∣ q →
         ¬ (p : ℤ) ∣ A * B * C * (462 * C + 15 * A) * (31 * A - 462 * B) * (15 * B + 31 * C)) ∧
       (∀ p : ℕ, p.Prime → ¬ p ∣ 4619990760 * q →
         ¬ (((p : ℤ) ∣ A ∧ (p : ℤ) ∣ 462 * B + q) ∨ ((p : ℤ) ∣ A ∧ (p : ℤ) ∣ 462 * C + q) ∨
           ((p : ℤ) ∣ 31 * A - 462 * B - q ∧ (p : ℤ) ∣ 15 * A + 462 * C + q)))))
    (q : ℕ) (A B C : ℤ) (Z : ℝ)
    (hq1 : 1 ≤ q) (hqW : q % 4619990760 = 1) (hZ : 100 ≤ Z) (hG : Good Z q A B C)
    (c : Fin 6 → ℤ) (L : Fin 6 → Fin 2 → ℤ)
    (hpar : ∀ n : Fin 2 → ℤ, OnPl q A B C (fun i => c i + ∑ j, L i j * n j))
    (hsurj : ∀ x, OnPl q A B C x → ∃ n : Fin 2 → ℤ, x = fun i => c i + ∑ j, L i j * n j)
    (hdet : ∃ δ : ℕ, δ ∣ 508 ∧
      |15 * (L 0 0 - L 4 0) * (31 * (L 2 1 - L 4 1)) - 15 * (L 0 1 - L 4 1) * (31 * (L 2 0 - L 4 0))|
        = 465 * (q : ℤ) ^ 2 * δ) :
    ∀ p : ℕ, p.Prime → ¬ p ∣ 4619990760 * q → ∀ i, ¬ ((p : ℤ) ∣ c i ∧ ∀ j, (p : ℤ) ∣ L i j) := by
  sorry

-- N38 local_denominator [two_structure_coupling]
theorem local_denominator (OnPl : ℤ → ℤ → ℤ → ℤ → (Fin 6 → ℤ) → Prop)
    (hOnPl : ∀ q A B C (x : Fin 6 → ℤ), OnPl q A B C x ↔
      (q * (x 1 - x 4) = 31 * A * (x 2 - x 4) + 462 * B * x 4 ∧
       q * (x 3 - x 4) = -15 * A * (x 0 - x 4) + 462 * C * x 4 ∧
       q * (x 4 + 1) = -(15 * B * (x 0 - x 4) + 31 * C * (x 2 - x 4)) ∧
       508 * x 5 = 15 * (x 0 + x 1) + 31 * (x 2 + x 3) - 508 * x 4 - 462))
    (Good : ℝ → ℕ → ℤ → ℤ → ℤ → Prop)
    (hGood : ∀ Z q A B C, Good Z q A B C ↔
      ((4619990760 : ℤ) ∣ A ∧ (4619990760 : ℤ) ∣ B ∧ (4619990760 : ℤ) ∣ C ∧
       (q : ℝ) * Z ^ 2 ≤ A ∧ (A : ℝ) < 2 * q * Z ^ 2 ∧
       (q : ℝ) * Z ≤ B ∧ (B : ℝ) < 2 * q * Z ∧
       (q : ℝ) * Z ≤ C ∧ (C : ℝ) < 2 * q * Z ∧
       (∀ p : ℕ, p.Prime → p ∣ q →
         ¬ (p : ℤ) ∣ A * B * C * (462 * C + 15 * A) * (31 * A - 462 * B) * (15 * B + 31 * C)) ∧
       (∀ p : ℕ, p.Prime → ¬ p ∣ 4619990760 * q →
         ¬ (((p : ℤ) ∣ A ∧ (p : ℤ) ∣ 462 * B + q) ∨ ((p : ℤ) ∣ A ∧ (p : ℤ) ∣ 462 * C + q) ∨
           ((p : ℤ) ∣ 31 * A - 462 * B - q ∧ (p : ℤ) ∣ 15 * A + 462 * C + q)))))
    (q : ℕ) (A B C : ℤ) (Z : ℝ)
    (hq1 : 1 ≤ q) (hqW : q % 4619990760 = 1) (hZ : 100 ≤ Z) (hG : Good Z q A B C)
    (hsq : Squarefree q)
    (c : Fin 6 → ℤ) (L : Fin 6 → Fin 2 → ℤ)
    (hpar : ∀ n : Fin 2 → ℤ, OnPl q A B C (fun i => c i + ∑ j, L i j * n j))
    (hsurj : ∀ x, OnPl q A B C x → ∃ n : Fin 2 → ℤ, x = fun i => c i + ∑ j, L i j * n j) :
    ∀ p : ℕ, p.Prime → p ∣ q → ∀ i, ¬ ((p : ℤ) ∣ c i ∧ ∀ j, (p : ℤ) ∣ L i j) := by
  sorry

-- N39 fc_lattice [algebraic_identity]
theorem fc_lattice (OnPl : ℤ → ℤ → ℤ → ℤ → (Fin 6 → ℤ) → Prop)
    (hOnPl : ∀ q A B C (x : Fin 6 → ℤ), OnPl q A B C x ↔
      (q * (x 1 - x 4) = 31 * A * (x 2 - x 4) + 462 * B * x 4 ∧
       q * (x 3 - x 4) = -15 * A * (x 0 - x 4) + 462 * C * x 4 ∧
       q * (x 4 + 1) = -(15 * B * (x 0 - x 4) + 31 * C * (x 2 - x 4)) ∧
       508 * x 5 = 15 * (x 0 + x 1) + 31 * (x 2 + x 3) - 508 * x 4 - 462))
    (Good : ℝ → ℕ → ℤ → ℤ → ℤ → Prop)
    (hGood : ∀ Z q A B C, Good Z q A B C ↔
      ((4619990760 : ℤ) ∣ A ∧ (4619990760 : ℤ) ∣ B ∧ (4619990760 : ℤ) ∣ C ∧
       (q : ℝ) * Z ^ 2 ≤ A ∧ (A : ℝ) < 2 * q * Z ^ 2 ∧
       (q : ℝ) * Z ≤ B ∧ (B : ℝ) < 2 * q * Z ∧
       (q : ℝ) * Z ≤ C ∧ (C : ℝ) < 2 * q * Z ∧
       (∀ p : ℕ, p.Prime → p ∣ q →
         ¬ (p : ℤ) ∣ A * B * C * (462 * C + 15 * A) * (31 * A - 462 * B) * (15 * B + 31 * C)) ∧
       (∀ p : ℕ, p.Prime → ¬ p ∣ 4619990760 * q →
         ¬ (((p : ℤ) ∣ A ∧ (p : ℤ) ∣ 462 * B + q) ∨ ((p : ℤ) ∣ A ∧ (p : ℤ) ∣ 462 * C + q) ∨
           ((p : ℤ) ∣ 31 * A - 462 * B - q ∧ (p : ℤ) ∣ 15 * A + 462 * C + q)))))
    (q : ℕ) (A B C : ℤ) (Z : ℝ)
    (hq1 : 1 ≤ q) (hqW : q % 4619990760 = 1) (hZ : 100 ≤ Z) (hG : Good Z q A B C)
    (c : Fin 6 → ℤ) (L : Fin 6 → Fin 2 → ℤ)
    (hpar : ∀ n : Fin 2 → ℤ, OnPl q A B C (fun i => c i + ∑ j, L i j * n j))
    (hsurj : ∀ x, OnPl q A B C x → ∃ n : Fin 2 → ℤ, x = fun i => c i + ∑ j, L i j * n j)
    (hdet : ∃ δ : ℕ, δ ∣ 508 ∧
      |15 * (L 0 0 - L 4 0) * (31 * (L 2 1 - L 4 1)) - 15 * (L 0 1 - L 4 1) * (31 * (L 2 0 - L 4 0))|
        = 465 * (q : ℤ) ^ 2 * δ) :
    ∀ i j : Fin 6, i ≠ j → L i 0 * L j 1 - L i 1 * L j 0 ≠ 0 := by
  sorry

-- N40 beta_local [assembly]
theorem beta_local (OnPl : ℤ → ℤ → ℤ → ℤ → (Fin 6 → ℤ) → Prop)
    (hOnPl : ∀ q A B C (x : Fin 6 → ℤ), OnPl q A B C x ↔
      (q * (x 1 - x 4) = 31 * A * (x 2 - x 4) + 462 * B * x 4 ∧
       q * (x 3 - x 4) = -15 * A * (x 0 - x 4) + 462 * C * x 4 ∧
       q * (x 4 + 1) = -(15 * B * (x 0 - x 4) + 31 * C * (x 2 - x 4)) ∧
       508 * x 5 = 15 * (x 0 + x 1) + 31 * (x 2 + x 3) - 508 * x 4 - 462))
    (Good : ℝ → ℕ → ℤ → ℤ → ℤ → Prop)
    (hGood : ∀ Z q A B C, Good Z q A B C ↔
      ((4619990760 : ℤ) ∣ A ∧ (4619990760 : ℤ) ∣ B ∧ (4619990760 : ℤ) ∣ C ∧
       (q : ℝ) * Z ^ 2 ≤ A ∧ (A : ℝ) < 2 * q * Z ^ 2 ∧
       (q : ℝ) * Z ≤ B ∧ (B : ℝ) < 2 * q * Z ∧
       (q : ℝ) * Z ≤ C ∧ (C : ℝ) < 2 * q * Z ∧
       (∀ p : ℕ, p.Prime → p ∣ q →
         ¬ (p : ℤ) ∣ A * B * C * (462 * C + 15 * A) * (31 * A - 462 * B) * (15 * B + 31 * C)) ∧
       (∀ p : ℕ, p.Prime → ¬ p ∣ 4619990760 * q →
         ¬ (((p : ℤ) ∣ A ∧ (p : ℤ) ∣ 462 * B + q) ∨ ((p : ℤ) ∣ A ∧ (p : ℤ) ∣ 462 * C + q) ∨
           ((p : ℤ) ∣ 31 * A - 462 * B - q ∧ (p : ℤ) ∣ 15 * A + 462 * C + q)))))
    (q : ℕ) (A B C : ℤ) (Z : ℝ)
    (hq1 : 1 ≤ q) (hqW : q % 4619990760 = 1) (hZ : 100 ≤ Z) (hG : Good Z q A B C)
    (hsq : Squarefree q)
    (c : Fin 6 → ℤ) (L : Fin 6 → Fin 2 → ℤ)
    (hpar : ∀ n : Fin 2 → ℤ, OnPl q A B C (fun i => c i + ∑ j, L i j * n j))
    (hsurj : ∀ x, OnPl q A B C x → ∃ n : Fin 2 → ℤ, x = fun i => c i + ∑ j, L i j * n j)
    (hdet : ∃ δ : ℕ, δ ∣ 508 ∧
      |15 * (L 0 0 - L 4 0) * (31 * (L 2 1 - L 4 1)) - 15 * (L 0 1 - L 4 1) * (31 * (L 2 0 - L 4 0))|
        = 465 * (q : ℤ) ^ 2 * δ)
    (β : ℕ → ℝ)
    (hβ : ∀ p : ℕ, β p = ((p : ℝ) / (p - 1)) ^ 6 / (p : ℝ) ^ 2 *
      ((Fintype.piFinset fun _ : Fin 2 => Finset.range p).filter
        (fun n => ∀ i, ¬ (p : ℤ) ∣ c i + ∑ j, L i j * (n j : ℤ))).card) :
    ∀ p : ℕ, p.Prime →
      (p ∣ 4619990760 → 1 / (p : ℝ) ^ 2 * ((p : ℝ) / (p - 1)) ^ 6 ≤ β p) ∧
      (¬ p ∣ 4619990760 → (1 - 6 / (p : ℝ)) * ((p : ℝ) / (p - 1)) ^ 6 ≤ β p) := by
  sorry

-- N41 ap_product [extremal_averaging]
theorem ap_product :
    Multipliable (fun p : Nat.Primes => (if ((p : ℕ) ∣ 4619990760) then 1 / ((p : ℕ) : ℝ) ^ 2 * (((p : ℕ) : ℝ) / (((p : ℕ) : ℝ) - 1)) ^ 6 else (1 - 6 / ((p : ℕ) : ℝ)) * (((p : ℕ) : ℝ) / (((p : ℕ) : ℝ) - 1)) ^ 6)) ∧
    0 < ∏' p : Nat.Primes, (if ((p : ℕ) ∣ 4619990760) then 1 / ((p : ℕ) : ℝ) ^ 2 * (((p : ℕ) : ℝ) / (((p : ℕ) : ℝ) - 1)) ^ 6 else (1 - 6 / ((p : ℕ) : ℝ)) * (((p : ℕ) : ℝ) / (((p : ℕ) : ℝ) - 1)) ^ 6) := by
  sorry

-- N42 singular_series_lower [assembly]
theorem singular_series_lower (OnPl : ℤ → ℤ → ℤ → ℤ → (Fin 6 → ℤ) → Prop)
    (hOnPl : ∀ q A B C (x : Fin 6 → ℤ), OnPl q A B C x ↔
      (q * (x 1 - x 4) = 31 * A * (x 2 - x 4) + 462 * B * x 4 ∧
       q * (x 3 - x 4) = -15 * A * (x 0 - x 4) + 462 * C * x 4 ∧
       q * (x 4 + 1) = -(15 * B * (x 0 - x 4) + 31 * C * (x 2 - x 4)) ∧
       508 * x 5 = 15 * (x 0 + x 1) + 31 * (x 2 + x 3) - 508 * x 4 - 462))
    (Good : ℝ → ℕ → ℤ → ℤ → ℤ → Prop)
    (hGood : ∀ Z q A B C, Good Z q A B C ↔
      ((4619990760 : ℤ) ∣ A ∧ (4619990760 : ℤ) ∣ B ∧ (4619990760 : ℤ) ∣ C ∧
       (q : ℝ) * Z ^ 2 ≤ A ∧ (A : ℝ) < 2 * q * Z ^ 2 ∧
       (q : ℝ) * Z ≤ B ∧ (B : ℝ) < 2 * q * Z ∧
       (q : ℝ) * Z ≤ C ∧ (C : ℝ) < 2 * q * Z ∧
       (∀ p : ℕ, p.Prime → p ∣ q →
         ¬ (p : ℤ) ∣ A * B * C * (462 * C + 15 * A) * (31 * A - 462 * B) * (15 * B + 31 * C)) ∧
       (∀ p : ℕ, p.Prime → ¬ p ∣ 4619990760 * q →
         ¬ (((p : ℤ) ∣ A ∧ (p : ℤ) ∣ 462 * B + q) ∨ ((p : ℤ) ∣ A ∧ (p : ℤ) ∣ 462 * C + q) ∨
           ((p : ℤ) ∣ 31 * A - 462 * B - q ∧ (p : ℤ) ∣ 15 * A + 462 * C + q))))) :
    ∃ cstar : ℝ, 0 < cstar ∧ ∀ (q : ℕ) (A B C : ℤ) (Z : ℝ), 1 ≤ q → q % 4619990760 = 1 → 100 ≤ Z →
      Good Z q A B C → Squarefree q →
      ∀ (c : Fin 6 → ℤ) (L : Fin 6 → Fin 2 → ℤ) (β : ℕ → ℝ),
        (∀ n : Fin 2 → ℤ, OnPl q A B C (fun i => c i + ∑ j, L i j * n j)) →
        (∀ x, OnPl q A B C x → ∃ n : Fin 2 → ℤ, x = fun i => c i + ∑ j, L i j * n j) →
        (∃ δ : ℕ, δ ∣ 508 ∧ |15 * (L 0 0 - L 4 0) * (31 * (L 2 1 - L 4 1)) - 15 * (L 0 1 - L 4 1) * (31 * (L 2 0 - L 4 0))| = 465 * (q : ℤ) ^ 2 * δ) →
        (∀ p : ℕ, β p = ((p : ℝ) / (p - 1)) ^ 6 / (p : ℝ) ^ 2 *
          ((Fintype.piFinset fun _ : Fin 2 => Finset.range p).filter
            (fun n => ∀ i, ¬ (p : ℤ) ∣ c i + ∑ j, L i j * (n j : ℤ))).card) →
        (∀ p : ℕ, p.Prime → 0 < β p) ∧ Multipliable (fun p : Nat.Primes => β p) ∧
          cstar ≤ ∏' p : Nat.Primes, β p := by
  sorry

-- N43 collision_line [case_split]
theorem collision_line (a b e : ℤ) (M : ℕ) (hab : a ≠ 0 ∨ b ≠ 0) :
    ((Finset.Icc (-(M : ℤ)) M ×ˢ Finset.Icc (-(M : ℤ)) M).filter
      (fun n => a * n.1 + b * n.2 = e)).card ≤ 2 * M + 1 := by
  sorry

-- N44 prime_weight_to_count [extremal_averaging]
theorem prime_weight_to_count {d t : ℕ} (F : Finset (Fin d → ℤ)) (f : (Fin d → ℤ) → Fin t → ℤ) (V : ℝ)
    (hV : 1 ≤ V) (hf : ∀ n ∈ F, ∀ i, (f n i : ℝ) ≤ V) :
    ∑ n ∈ F, ∏ i, (if 0 < f n i ∧ (f n i).natAbs.Prime then Real.log (f n i : ℝ) else 0) ≤
      Real.log V ^ t * ((F.filter (fun n => ∀ i, 0 < f n i ∧ (f n i).natAbs.Prime)).card : ℝ) := by
  sorry

-- N45 plane_prime_count [two_structure_coupling]
theorem plane_prime_count (OnPl : ℤ → ℤ → ℤ → ℤ → (Fin 6 → ℤ) → Prop)
    (hOnPl : ∀ q A B C (x : Fin 6 → ℤ), OnPl q A B C x ↔
      (q * (x 1 - x 4) = 31 * A * (x 2 - x 4) + 462 * B * x 4 ∧
       q * (x 3 - x 4) = -15 * A * (x 0 - x 4) + 462 * C * x 4 ∧
       q * (x 4 + 1) = -(15 * B * (x 0 - x 4) + 31 * C * (x 2 - x 4)) ∧
       508 * x 5 = 15 * (x 0 + x 1) + 31 * (x 2 + x 3) - 508 * x 4 - 462))
    (InReg : ℝ → (Fin 6 → ℤ) → Prop)
    (hInReg : ∀ T (x : Fin 6 → ℤ), InReg T x ↔
      (-2 * T ≤ 15 * ((x 0 : ℝ) - x 4) ∧ 15 * ((x 0 : ℝ) - x 4) ≤ -T ∧
       |31 * ((x 2 : ℝ) - x 4)| ≤ 1 / 100000 * |15 * ((x 0 : ℝ) - x 4)|))
    (Good : ℝ → ℕ → ℤ → ℤ → ℤ → Prop)
    (hGood : ∀ Z q A B C, Good Z q A B C ↔
      ((4619990760 : ℤ) ∣ A ∧ (4619990760 : ℤ) ∣ B ∧ (4619990760 : ℤ) ∣ C ∧
       (q : ℝ) * Z ^ 2 ≤ A ∧ (A : ℝ) < 2 * q * Z ^ 2 ∧
       (q : ℝ) * Z ≤ B ∧ (B : ℝ) < 2 * q * Z ∧
       (q : ℝ) * Z ≤ C ∧ (C : ℝ) < 2 * q * Z ∧
       (∀ p : ℕ, p.Prime → p ∣ q →
         ¬ (p : ℤ) ∣ A * B * C * (462 * C + 15 * A) * (31 * A - 462 * B) * (15 * B + 31 * C)) ∧
       (∀ p : ℕ, p.Prime → ¬ p ∣ 4619990760 * q →
         ¬ (((p : ℤ) ∣ A ∧ (p : ℤ) ∣ 462 * B + q) ∨ ((p : ℤ) ∣ A ∧ (p : ℤ) ∣ 462 * C + q) ∨
           ((p : ℤ) ∣ 31 * A - 462 * B - q ∧ (p : ℤ) ∣ 15 * A + 462 * C + q))))) :
    ∀ τ : ℝ, 0 < τ → ∃ T0 c3 : ℝ, 0 < c3 ∧ ∀ (T Z : ℝ) (q : ℕ) (A B C : ℤ),
      T0 ≤ T → 100 ≤ Z → 1 ≤ q → Squarefree q → q % 4619990760 = 1 →
      (q : ℝ) ≤ Real.log T ^ τ → Z ≤ Real.log T ^ τ → Good Z q A B C →
      ∃ F : Finset (Fin 6 → ℤ),
        (∀ x ∈ F, OnPl q A B C x ∧ InReg T x ∧ Function.Injective x ∧ ∀ i, 0 < x i ∧ (x i).natAbs.Prime) ∧
        c3 * T ^ 2 / ((q : ℝ) ^ 2 * Real.log T ^ 6) ≤ F.card := by
  sorry

-- N46 threshold_lemma [assembly]
theorem threshold_lemma (κ : ℝ) (hκ : 0 < κ) (Ch T0 C0 ε : ℝ) (hCh : 0 < Ch) (hε : 0 < ε) :
    ∃ Y0 : ℝ, ∀ Y Q Z : ℝ, Y0 ≤ Y → 1 ≤ Q → Q ≤ Real.log Y ^ κ → 1 ≤ Z → Z ≤ Real.log Y ^ κ →
      Real.log Y / 3 ≤ Real.log (Real.sqrt (Y / (Ch * Z ^ 3))) ∧
      Real.log (Real.sqrt (Y / (Ch * Z ^ 3))) ≤ Real.log Y ∧
      T0 ≤ Real.sqrt (Y / (Ch * Z ^ 3)) ∧
      T0 ≤ Z * Real.sqrt (Y / (Ch * Z ^ 3)) ∧
      2 * Q ≤ Real.log (Real.sqrt (Y / (Ch * Z ^ 3))) ^ (κ + 1) ∧
      Z ≤ Real.log (Real.sqrt (Y / (Ch * Z ^ 3))) ^ (κ + 1) ∧
      C0 * (2 * Q) ^ 2 ≤ Real.sqrt (Y / (Ch * Z ^ 3)) ∧
      (2 * Q) ^ 2 * Real.log (Real.sqrt (Y / (Ch * Z ^ 3))) ^ 6 ≤ ε * Real.sqrt (Y / (Ch * Z ^ 3)) ∧
      Q ^ 6 * Z ^ 4 * Real.log (Real.sqrt (Y / (Ch * Z ^ 3))) ^ 6 ≤ ε * Real.sqrt (Y / (Ch * Z ^ 3)) ^ 2 := by
  sorry

-- N47 two_height_core [assembly]
theorem two_height_core : ∃ c0 : ℝ, 0 < c0 ∧ c0 < 1 ∧ ∀ κ : ℝ, 0 < κ →
    ∃ cκ Yκ Qκ Zκ : ℝ, 0 < cκ ∧ ∀ Y Q Z : ℝ, Yκ ≤ Y → Qκ ≤ Q → Q ≤ Real.log Y ^ κ → Zκ ≤ Z →
      Z ≤ Real.log Y ^ κ →
      ∃ F : Finset (ℕ × ℕ),
        (∀ uv ∈ F, 0 < uv.1 ∧ 0 < uv.2 ∧ Nat.Coprime uv.1 uv.2 ∧
          c0 * Y ≤ ((uv.1 + uv.2 : ℕ) : ℝ) ∧ ((uv.1 + uv.2 : ℕ) : ℝ) ≤ Y ∧
          σ 1 (3600 * uv.1) + σ 1 (3600 * uv.2) = σ 1 (3600 * (uv.1 + uv.2)) ∧
          (3600 * uv.1 * uv.2 * (uv.1 + uv.2)).primeFactors.card ≤ 11) ∧
        cκ * Y * Q ^ 2 * Z / Real.log Y ^ 6 ≤ F.card := by
  sorry

-- N48 S_lower_bound [quantitative_improvement]
theorem S_lower_bound : ∀ κ : ℝ, 0 < κ → ∃ c X1 : ℝ, 0 < c ∧ ∀ x : ℝ, X1 ≤ x →
    c * x * Real.log x ^ (3 * κ - 5) ≤ S x := by
  sorry

-- ===== Target =====

/-- Li's Theorem 1.1: for every fixed `R > 0`, `S x / (x (log x)^R)` tends to infinity. In particular `S` is not
asymptotic to `c * x` for any finite `c > 0`. -/
theorem li_1061 : ∀ R : ℝ, 0 < R →
    Tendsto (fun x : ℝ ↦ S x / (x * Real.log x ^ R)) atTop atTop := by
  sorry

end Erdos1061
