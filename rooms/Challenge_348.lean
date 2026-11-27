/-
Erdős Problem 348: the statement copied verbatim from google-deepmind/formal-conjectures,
FormalConjectures/ErdosProblems/348.lean at commit f606af16 (Apache-2.0; Copyright 2026 The Formal Conjectures Authors),
with the FormalConjecturesUtil import replaced by Mathlib and the two definitions it uses, `subseqSums'` and
`IsAddCompleteNatSeq'`, copied verbatim with the section variables they sit under (`[AddCommMonoid M]`, `[Preorder M]`) from FormalConjecturesForMathlib/NumberTheory/AdditivelyComplete.lean at the
same commit (Apache-2.0; Copyright 2025 The Formal Conjectures Authors). The answer is Geneson's Theorem 1
(arXiv:2609.25107): the pairs are exactly those with m ≤ 1. The searcher may not alter the definitions or the statement.
References: erdosproblems.com/348.
-/
module

public import Mathlib

@[expose] public section

variable {M : Type*} [AddCommMonoid M]

/-- The set of subset sums of a sequence `ℕ → M`, where repetition is allowed. -/
def subseqSums' (A : ℕ → M) : Set M :=
  {n | ∃ B : Finset ℕ, n = ∑ i ∈ B, A i}

variable [Preorder M]

/-- A sequence `A` is complete if every sufficiently large element of `M` is a sum of
(not necessarily distinct) terms of `A`. -/
def IsAddCompleteNatSeq' (A : ℕ → M) : Prop :=
  ∀ᶠ k in Filter.atTop, k ∈ subseqSums' A

namespace Erdos348

open Erdos348

def erdos_348.answer : Set (ℕ × ℕ) := {(m, n) : ℕ × ℕ | m < n ∧ m ≤ 1}

/--
For what values of $0 \leq m < n$ is there a complete sequence
$A = \{a_1 \leq a_2 \leq \cdots\}$ of integers such that
 1. $A$ remains complete after removing any $m$ elements, but
 2. $A$ is not complete after removing any $n$ elements.

Geneson [Ge26, Theorem 1] proved that the pairs are exactly those with $m \leq 1$.
Completeness allows finitely many exceptions, and deletions remove indexed occurrences.
-/
theorem erdos_348 :
    { (m, n) | (m) (n) (_ : m < n) (a : ℕ → ℕ) (_ : Monotone a)
      (_ : ∀ s, s.card = m → IsAddCompleteNatSeq' (Function.updateFinset a s 0))
        (_ : ∀ t, t.card = n → ¬IsAddCompleteNatSeq' (Function.updateFinset a t 0)) } =
    erdos_348.answer := by
  sorry

end Erdos348
