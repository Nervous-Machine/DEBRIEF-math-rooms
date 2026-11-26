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

namespace Erdos569

/-!
Theorem 3 of Cambie and Freschi, "A general bound on R(C_k, H)", arXiv:2606.11174v1 (9 June 2026), which settles
Erdős Problem 569 (Erdős, Faudree, Rousseau and Schelp 1993; problem 34 in Chung–Graham): for every graph H with m
edges and no isolated vertices and every k ≥ 3, R(C_k, H) ≤ (k − 1)m + 1.

Stated here by the registrar of the rooms experiment on 2026-11-26 in the definitions of
FormalConjectures/ErdosProblems/569.lean (the quantification over `m`, `W`, `H`, the no-isolated-vertex condition
`∀ v, 0 < H.degree v` and `H.edgeSet.ncard = m` are that file's), with the cycle of length `k` as
`SimpleGraph.cycleGraph k`. Nobody else has read this statement against the paper.
-/

/-- **Cambie–Freschi (2026), Theorem 3.** For every `k ≥ 3` and every graph `H` with `m` edges and no isolated
vertices, `R(C_k, H) ≤ (k - 1) * m + 1`. -/
theorem cambie_freschi (k : ℕ) (hk : 3 ≤ k) (m : ℕ) (W : Type) [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (h0 : ∀ v, 0 < H.degree v) (hm : H.edgeSet.ncard = m) :
    SimpleGraph.graphRamsey (SimpleGraph.cycleGraph k) H ≤ (k - 1) * m + 1 := by
  sorry

end Erdos569
