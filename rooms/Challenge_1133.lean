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
  sorry

end Erdos1133
