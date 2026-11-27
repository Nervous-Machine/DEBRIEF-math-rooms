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

/-- Li's Theorem 1.1: for every fixed `R > 0`, `S x / (x (log x)^R)` tends to infinity. In particular `S` is not
asymptotic to `c * x` for any finite `c > 0`. -/
theorem li_1061 : ∀ R : ℝ, 0 < R →
    Tendsto (fun x : ℝ ↦ S x / (x * Real.log x ^ R)) atTop atTop := by
  sorry

end Erdos1061
