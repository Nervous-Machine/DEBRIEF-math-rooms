/-
Copyright 2026 The Formal Conjectures Authors (the definition `SimpleGraph.graphRamsey`, copied verbatim from
FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Ramsey.lean of google-deepmind/formal-conjectures at commit
9097e2f90e66d2f6244209cb1c07f7120d17ec53, 2026-11-24, Apache-2.0).
Copyright 2026 Nervous Machine (this file's arrangement). Licensed under the Apache License, Version 2.0.
-/
module

public import Mathlib

@[expose] public section

namespace SimpleGraph

/--
The two-color Ramsey number `graphRamsey G H` is the minimum number of vertices `n`
such that every 2-coloring of the edges of the complete graph on `n` vertices contains
a copy of `G` in the first color or a copy of `H` in the second color.

A 2-coloring of the complete graph on `Fin n` is represented by a graph `C` (the edges of the
first color) and its complement `Cᶜ` (the edges of the second color).
-/
noncomputable def graphRamsey {α β : Type*} [Fintype α] [Fintype β]
    (G : SimpleGraph α) (H : SimpleGraph β) : ℕ :=
  sInf { n : ℕ | ∀ (C : SimpleGraph (Fin n)), G.IsContained C ∨ H.IsContained Cᶜ }

end SimpleGraph

namespace Erdos159

/-!
The statement below is `erdos_159` of FormalConjectures/ErdosProblems/159.lean in google-deepmind/formal-conjectures
at commit 9097e2f90e66d2f6244209cb1c07f7120d17ec53, copied verbatim (category: research open). It is an OPEN problem.
Nobody knows whether it is true.
-/

/--
There exists some constant $c>0$ such that
$$R(C_4,K_n) \ll n^{2-c}.$$

The prize of $100 is offered in [Er78] for a proof or disproof.

This problem is #17 in Ramsey Theory in the graphs problem collection.
-/
theorem erdos_159 :
    ∃ (c : ℝ) (_ : 0 < c) (C : ℝ),
      ∀ (n : ℕ), 1 ≤ n →
        (SimpleGraph.graphRamsey (SimpleGraph.cycleGraph 4)
          (SimpleGraph.completeGraph (Fin n)) : ℝ) ≤ C * (n : ℝ) ^ (2 - c) := by
  sorry

end Erdos159
