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

/-! ## Rooms (blueprint nodes N01–N59, in order) -/

/-! N01 cycleGraph_no_isolated [leaf, believed provable] deps:  -/
theorem cycleGraph_no_isolated (k : ℕ) (hk : 3 ≤ k) :
    ∀ v : Fin k, ∃ w, (SimpleGraph.cycleGraph k).Adj v w := by
  sorry

/-! N02 cycleGraph_edgeSet_ncard [leaf, believed provable] deps:  -/
theorem cycleGraph_edgeSet_ncard (k : ℕ) (hk : 3 ≤ k) :
    (SimpleGraph.cycleGraph k).edgeSet.ncard = k := by
  sorry

/-! N03 isContained_top_of_card_le [join, believed provable] deps:  -/
theorem isContained_top_of_card_le {W V : Type} [Fintype W] [Fintype V] (H : SimpleGraph W)
    (h : Fintype.card W ≤ Fintype.card V) : H.IsContained (⊤ : SimpleGraph V) := by
  sorry

/-! N04 isContained_of_induce [join, believed provable] deps:  -/
theorem isContained_of_induce {W V : Type} {H : SimpleGraph W} {C : SimpleGraph V} (s : Set V)
    (h : H.IsContained (C.induce s)) : H.IsContained C := by
  sorry

/-! N05 isContained_compl_of_compl_induce [join, believed provable] deps:  -/
theorem isContained_compl_of_compl_induce {W V : Type} {H : SimpleGraph W} {C : SimpleGraph V}
    (s : Set V) (h : H.IsContained (C.induce s)ᶜ) : H.IsContained Cᶜ := by
  sorry

/-! N06 degree_sum_ncard [join, believed provable] deps:  -/
theorem degree_sum_ncard {W : Type} [Fintype W] (H : SimpleGraph W) :
    ∑ v, (H.neighborSet v).ncard = 2 * H.edgeSet.ncard := by
  sorry

/-! N07 card_le_two_mul_ncard [leaf, believed provable] deps: N06 -/
theorem card_le_two_mul_ncard {W : Type} [Fintype W] (H : SimpleGraph W)
    (h0 : ∀ v, ∃ w, H.Adj v w) : Fintype.card W ≤ 2 * H.edgeSet.ncard := by
  sorry

/-! N08 connected_card_le_ncard_add_one [join, believed provable] deps:  -/
theorem connected_card_le_ncard_add_one {W : Type} [Fintype W] (H : SimpleGraph W)
    (hc : H.Connected) : Fintype.card W ≤ H.edgeSet.ncard + 1 := by
  sorry

/-! N09 ramsey_zero_edges [leaf, believed provable] deps:  -/
theorem ramsey_zero_edges {W : Type} [Fintype W] (H : SimpleGraph W) (h0 : ∀ v, ∃ w, H.Adj v w)
    (hm : H.edgeSet.ncard = 0) {V : Type} (C : SimpleGraph V) : H.IsContained Cᶜ := by
  sorry

/-! N10 one_edge_isContained_of_adj [leaf, believed provable] deps:  -/
theorem one_edge_isContained_of_adj {W V : Type} [Fintype W] (H : SimpleGraph W)
    (h0 : ∀ v, ∃ w, H.Adj v w) (hm : H.edgeSet.ncard = 1) (D : SimpleGraph V) {x y : V}
    (hxy : D.Adj x y) : H.IsContained D := by
  sorry

/-! N11 ramsey_one_edge [leaf, believed provable] deps: N03 N10 -/
theorem ramsey_one_edge (k : ℕ) (hk : 3 ≤ k) {W : Type} [Fintype W] (H : SimpleGraph W)
    (h0 : ∀ v, ∃ w, H.Adj v w) (hm : H.edgeSet.ncard = 1) (V : Type) [Fintype V]
    (C : SimpleGraph V) (hV : (k - 1) * 1 + 1 ≤ Fintype.card V) :
    (SimpleGraph.cycleGraph k).IsContained C ∨ H.IsContained Cᶜ := by
  sorry

/-! N12 cycle_of_closed_seq [join, believed provable] deps:  -/
theorem cycle_of_closed_seq {V : Type} (C : SimpleGraph V) (k : ℕ) (hk : 3 ≤ k) (f : ℕ → V)
    (hinj : Set.InjOn f (Set.Iio k)) (hadj : ∀ i, i + 1 < k → C.Adj (f i) (f (i + 1)))
    (hclose : C.Adj (f (k - 1)) (f 0)) : (SimpleGraph.cycleGraph k).IsContained C := by
  sorry

/-! N13 cycle_of_path_in_nbhd [join, believed provable] deps: N12 -/
theorem cycle_of_path_in_nbhd {V : Type} (C : SimpleGraph V) (k : ℕ) (hk : 3 ≤ k) (v : V)
    (S : Set V) (hS : ∀ s ∈ S, C.Adj v s) (hv : v ∉ S)
    (hP : (SimpleGraph.pathGraph (k - 1)).IsContained (C.induce S)) :
    (SimpleGraph.cycleGraph k).IsContained C := by
  sorry

/-! N14 goddard_kleitman_sidorenko [join, believed likely_false] deps:  -/
theorem goddard_kleitman_sidorenko {W : Type} [Fintype W] (H : SimpleGraph W)
    (h0 : ∀ v, ∃ w, H.Adj v w) (m : ℕ) (hm : H.edgeSet.ncard = m) (V : Type) [Fintype V]
    (C : SimpleGraph V) (hV : 2 * m + 1 ≤ Fintype.card V) :
    (SimpleGraph.cycleGraph 3).IsContained C ∨ H.IsContained Cᶜ := by
  sorry

/-! N15 step_triangle [leaf, believed provable] deps: N14 N01 N02 N03 -/
theorem step_triangle (k : ℕ) (hk : 3 ≤ k) {W : Type} [Fintype W] (H : SimpleGraph W)
    (hW : Fintype.card W = 3) (V : Type) [Fintype V] (C : SimpleGraph V)
    (hV : 2 * k + 1 ≤ Fintype.card V) :
    (SimpleGraph.cycleGraph k).IsContained C ∨ H.IsContained Cᶜ := by
  sorry

/-! N16 haggkvist [leaf, believed unsure] deps:  -/
theorem haggkvist (k a b : ℕ) (hk : 2 ≤ k) (ha : 1 ≤ a) (hb : 1 ≤ b) (V : Type) [Fintype V]
    (C : SimpleGraph V) (hV : a + b + k - 2 ≤ Fintype.card V) :
    (SimpleGraph.pathGraph k).IsContained C ∨
      (completeBipartiteGraph (Fin a) (Fin b)).IsContained Cᶜ := by
  sorry

/-! N17 haggkvist_parts [leaf, believed provable] deps: N16 N04 -/
theorem haggkvist_parts (k a b : ℕ) (hk : 2 ≤ k) {V : Type} [Fintype V] (C : SimpleGraph V)
    (X : Finset V) (hX : a + b + k - 2 ≤ X.card) :
    (SimpleGraph.pathGraph k).IsContained C ∨
      ∃ P Q : Finset V, P ⊆ X ∧ Q ⊆ X ∧ a ≤ P.card ∧ b ≤ Q.card ∧
        ∀ x ∈ P, ∀ y ∈ Q, Cᶜ.Adj x y := by
  sorry

/-! N18 multipartite_parts [leaf, believed provable] deps: N17 -/
theorem multipartite_parts (k : ℕ) (hk : 2 ≤ k) (t : ℕ) (n : Fin t → ℕ) {V : Type} [Fintype V]
    (C : SimpleGraph V) (X : Finset V) (hX : (k - 2) * (t - 1) + ∑ i, n i ≤ X.card) :
    (SimpleGraph.pathGraph k).IsContained C ∨
      ∃ P : Fin t → Finset V, (∀ i, P i ⊆ X) ∧ (∀ i, n i ≤ (P i).card) ∧
        ∀ i j, i ≠ j → ∀ x ∈ P i, ∀ y ∈ P j, Cᶜ.Adj x y := by
  sorry

/-! N19 embed_colored_into_parts [leaf, believed provable] deps:  -/
theorem embed_colored_into_parts {W V : Type} [Fintype W] (H : SimpleGraph W) (t : ℕ)
    (c : H.Coloring (Fin t)) (D : SimpleGraph V) (P : Fin t → Finset V)
    (hP : ∀ i, (Finset.univ.filter (fun w => c w = i)).card ≤ (P i).card)
    (hcross : ∀ i j, i ≠ j → ∀ x ∈ P i, ∀ y ∈ P j, D.Adj x y) : H.IsContained D := by
  sorry

/-! N20 lemma5_path_coloring [join, believed provable] deps: N18 N19 -/
theorem lemma5_path_coloring (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] (H : SimpleGraph W)
    (t : ℕ) (c : H.Coloring (Fin t)) (V : Type) [Fintype V] (C : SimpleGraph V)
    (hV : Fintype.card W + (k - 2) * (t - 1) ≤ Fintype.card V) :
    (SimpleGraph.pathGraph k).IsContained C ∨ H.IsContained Cᶜ := by
  sorry

/-! N21 cor6_path_ramsey [join, believed provable] deps: N20 -/
theorem cor6_path_ramsey (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] (H : SimpleGraph W)
    (V : Type) [Fintype V] (C : SimpleGraph V)
    (hV : (k - 1) * (Fintype.card W - 1) + 1 ≤ Fintype.card V) :
    (SimpleGraph.pathGraph k).IsContained C ∨ H.IsContained Cᶜ := by
  sorry

/-! N22 jayawardene_C4 [leaf, believed likely_false] deps:  -/
theorem jayawardene_C4 {W : Type} [Fintype W] (H : SimpleGraph W) (hc : H.Connected) (m : ℕ)
    (hm : H.edgeSet.ncard = m) (hm2 : 2 ≤ m) (V : Type) [Fintype V] (C : SimpleGraph V)
    (hV : 2 * m + 1 ≤ Fintype.card V) :
    (SimpleGraph.cycleGraph 4).IsContained C ∨ H.IsContained Cᶜ := by
  sorry

/-! N23 jayawardene_C5 [leaf, believed likely_false] deps:  -/
theorem jayawardene_C5 {W : Type} [Fintype W] (H : SimpleGraph W) (hc : H.Connected)
    (hW : 4 ≤ Fintype.card W) (m : ℕ) (hm : H.edgeSet.ncard = m) (V : Type) [Fintype V]
    (C : SimpleGraph V) (hV : 2 * m + 2 ≤ Fintype.card V) :
    (SimpleGraph.cycleGraph 5).IsContained C ∨ H.IsContained Cᶜ := by
  sorry

/-! N24 jayawardene_C6 [leaf, believed likely_false] deps:  -/
theorem jayawardene_C6 {W : Type} [Fintype W] (H : SimpleGraph W) (hc : H.Connected)
    (hW : 6 ≤ Fintype.card W) (m : ℕ) (hm : H.edgeSet.ncard = m) (V : Type) [Fintype V]
    (C : SimpleGraph V) (hV : 2 * m + 2 ≤ Fintype.card V) :
    (SimpleGraph.cycleGraph 6).IsContained C ∨ H.IsContained Cᶜ := by
  sorry

/-! N25 ramsey_C5_K3 [leaf, believed unsure] deps: N12 -/
theorem ramsey_C5_K3 (V : Type) [Fintype V] (C : SimpleGraph V) (hV : 9 ≤ Fintype.card V) :
    (SimpleGraph.cycleGraph 5).IsContained C ∨ (⊤ : SimpleGraph (Fin 3)).IsContained Cᶜ := by
  sorry

/-! N26 ramsey_C6_K3 [leaf, believed unsure] deps: N12 -/
theorem ramsey_C6_K3 (V : Type) [Fintype V] (C : SimpleGraph V) (hV : 11 ≤ Fintype.card V) :
    (SimpleGraph.cycleGraph 6).IsContained C ∨ (⊤ : SimpleGraph (Fin 3)).IsContained Cᶜ := by
  sorry

/-! N27 ramsey_C6_K4 [leaf, believed likely_false] deps: N12 -/
theorem ramsey_C6_K4 (V : Type) [Fintype V] (C : SimpleGraph V) (hV : 16 ≤ Fintype.card V) :
    (SimpleGraph.cycleGraph 6).IsContained C ∨ (⊤ : SimpleGraph (Fin 4)).IsContained Cᶜ := by
  sorry

/-! N28 ramsey_C6_K5 [leaf, believed likely_false] deps: N12 -/
theorem ramsey_C6_K5 (V : Type) [Fintype V] (C : SimpleGraph V) (hV : 21 ≤ Fintype.card V) :
    (SimpleGraph.cycleGraph 6).IsContained C ∨ (⊤ : SimpleGraph (Fin 5)).IsContained Cᶜ := by
  sorry

/-! N29 lemma4_small_cycles [join, believed provable] deps: N22 N23 N24 N25 N26 N27 N28 N03 N08 -/
theorem lemma4_small_cycles (k : ℕ) (hk : k = 4 ∨ k = 5 ∨ k = 6) {W : Type} [Fintype W]
    (H : SimpleGraph W) (hc : H.Connected) (m : ℕ) (hm : H.edgeSet.ncard = m) (hm2 : 2 ≤ m)
    (V : Type) [Fintype V] (C : SimpleGraph V) (hV : (k - 1) * m + 1 ≤ Fintype.card V) :
    (SimpleGraph.cycleGraph k).IsContained C ∨ H.IsContained Cᶜ := by
  sorry

/-! N30 claim8 [join, believed provable] deps: N12 -/
theorem claim8 (k : ℕ) (hk : 7 ≤ k) {V : Type} (C : SimpleGraph V) (v : V) (w u : ℕ → V)
    (hw : Set.InjOn w (Set.Iic k)) (hwadj : ∀ i, i < k → C.Adj (w i) (w (i + 1)))
    (hvu : ∀ i, i ≤ k → C.Adj v (u i)) (huw : ∀ i, i ≤ k → C.Adj (u i) (w i))
    (huw' : ∀ i j, i ≤ k → j ≤ k → u i ≠ w j) (hvw : ∀ j, j ≤ k → v ≠ w j)
    (hfree : ¬ (SimpleGraph.cycleGraph k).IsContained C) :
    ∀ i, i ≤ 4 → u i = u (k - 4 + i) := by
  sorry

/-! N31 claim9 [leaf, believed provable] deps: N30 N12 -/
theorem claim9 (k : ℕ) (hk : 7 ≤ k) {V : Type} (C : SimpleGraph V) (v : V) (w u : ℕ → V)
    (hw : Set.InjOn w (Set.Iic k)) (hwadj : ∀ i, i < k → C.Adj (w i) (w (i + 1)))
    (hvu : ∀ i, i ≤ k → C.Adj v (u i)) (huw : ∀ i, i ≤ k → C.Adj (u i) (w i))
    (huw' : ∀ i j, i ≤ k → j ≤ k → u i ≠ w j) (hvw : ∀ j, j ≤ k → v ≠ w j)
    (hfree : ¬ (SimpleGraph.cycleGraph k).IsContained C) :
    ∀ i, i ≤ 2 → u i ≠ u (i + 2) := by
  sorry

/-! N32 lemma7 [leaf, believed provable] deps: N30 N31 N12 -/
theorem lemma7 (k : ℕ) (hk : 7 ≤ k) {V : Type} (C : SimpleGraph V) (v : V) (w u : ℕ → V)
    (hw : Set.InjOn w (Set.Iic k)) (hwadj : ∀ i, i < k → C.Adj (w i) (w (i + 1)))
    (hvu : ∀ i, i ≤ k → C.Adj v (u i)) (huw : ∀ i, i ≤ k → C.Adj (u i) (w i))
    (huw' : ∀ i j, i ≤ k → j ≤ k → u i ≠ w j) (hvw : ∀ j, j ≤ k → v ≠ w j) :
    (SimpleGraph.cycleGraph k).IsContained C := by
  sorry

/-! N33 lemma7_bridge [leaf, believed provable] deps: N32 -/
theorem lemma7_bridge (k : ℕ) (hk : 7 ≤ k) {V : Type} (C : SimpleGraph V) (v : V) (U Gam : Set V)
    (hU : ∀ x ∈ U, C.Adj v x) (hGam : ∀ y ∈ Gam, ∃ x ∈ U, C.Adj x y) (hdisj : Disjoint U Gam)
    (hvG : v ∉ Gam) (hP : (SimpleGraph.pathGraph (k + 1)).IsContained (C.induce Gam)) :
    (SimpleGraph.cycleGraph k).IsContained C := by
  sorry

/-! N34 exists_critical_vertex_set [leaf, believed provable] deps:  -/
theorem exists_critical_vertex_set {W : Type} [Fintype W] (H : SimpleGraph W) (s : ℕ)
    (h : ¬ H.Colorable s) :
    ∃ X : Finset W, ¬ (H.induce (X : Set W)).Colorable s ∧
      ∀ x ∈ X, s ≤ (H.neighborSet x ∩ (X : Set W)).ncard := by
  sorry

/-! N35 prop10 [leaf, believed provable] deps: N34 N06 -/
theorem prop10 {W : Type} [Fintype W] (H : SimpleGraph W) (hδ : ∀ v, 2 ≤ (H.neighborSet v).ncard)
    (t : ℕ) (ht : ¬ H.Colorable (t - 1)) :
    2 * Fintype.card W + t * (t - 3) ≤ 2 * H.edgeSet.ncard := by
  sorry

/-! N36 exists_chromatic [leaf, believed provable] deps:  -/
theorem exists_chromatic {W : Type} [Fintype W] (H : SimpleGraph W) (hm : 1 ≤ H.edgeSet.ncard) :
    ∃ t, 2 ≤ t ∧ H.Colorable t ∧ ¬ H.Colorable (t - 1) := by
  sorry

/-! N37 choose_ineq [leaf, believed provable] deps:  -/
theorem choose_ineq (n s : ℕ) (hs : 2 ≤ s) (hsn : 2 * s + 1 ≤ n) :
    4 * (n - 2).choose (s - 2) < n.choose s := by
  sorry

/-! N38 sum_induced_edges_powersetCard [leaf, believed provable] deps:  -/
theorem sum_induced_edges_powersetCard {W : Type} [Fintype W] (H : SimpleGraph W) (s : ℕ)
    (hs : 2 ≤ s) :
    ∑ T ∈ Finset.univ.powersetCard s, (H.induce (T : Set W)).edgeSet.ncard =
      H.edgeSet.ncard * (Fintype.card W - 2).choose (s - 2) := by
  sorry

/-! N39 exists_sparse_half [leaf, believed provable] deps: N37 N38 -/
theorem exists_sparse_half {W : Type} [Fintype W] (H : SimpleGraph W)
    (hn : 3 ≤ Fintype.card W) (hm : 1 ≤ H.edgeSet.ncard) :
    ∃ T : Finset W, T.card = (Fintype.card W + 1) / 2 - 1 ∧
      4 * (H.induce (T : Set W)).edgeSet.ncard < H.edgeSet.ncard := by
  sorry

/-! N40 ramsey_with_isolated [join, believed provable] deps: N04 N05 -/
theorem ramsey_with_isolated (k : ℕ) (hk : 3 ≤ k) (m : ℕ)
    (ih : ∀ m' < m, ∀ (W' : Type) [Fintype W'] (H' : SimpleGraph W'), (∀ v, ∃ w, H'.Adj v w) →
      H'.edgeSet.ncard = m' → ∀ (V' : Type) [Fintype V'] (C' : SimpleGraph V'),
      (k - 1) * m' + 1 ≤ Fintype.card V' →
      (SimpleGraph.cycleGraph k).IsContained C' ∨ H'.IsContained C'ᶜ)
    {W : Type} [Fintype W] (H : SimpleGraph W) (e : ℕ) (he : H.edgeSet.ncard = e) (hem : e < m)
    (V : Type) [Fintype V] (C : SimpleGraph V) (hV1 : (k - 1) * e + 1 ≤ Fintype.card V)
    (hV2 : Fintype.card W ≤ Fintype.card V) :
    (SimpleGraph.cycleGraph k).IsContained C ∨ H.IsContained Cᶜ := by
  sorry

/-! N41 glue_components [leaf, believed provable] deps:  -/
theorem glue_components {W V : Type} [Fintype W] [Fintype V] (H : SimpleGraph W) (A : Set W)
    (hA : ∀ x y, H.Adj x y → (x ∈ A ↔ y ∈ A)) (C : SimpleGraph V)
    (f : SimpleGraph.Copy (H.induce A) Cᶜ)
    (h2 : (H.induce Aᶜ).IsContained (C.induce (Set.range ⇑f)ᶜ)ᶜ) : H.IsContained Cᶜ := by
  sorry

/-! N42 split_of_not_connected [leaf, believed provable] deps:  -/
theorem split_of_not_connected {W : Type} [Fintype W] [Nonempty W] (H : SimpleGraph W)
    (hc : ¬ H.Connected) :
    ∃ A : Set W, A.Nonempty ∧ Aᶜ.Nonempty ∧ ∀ x y, H.Adj x y → (x ∈ A ↔ y ∈ A) := by
  sorry

/-! N43 edge_split_of_closed [leaf, believed provable] deps:  -/
theorem edge_split_of_closed {W : Type} [Fintype W] (H : SimpleGraph W) (A : Set W)
    (hA : ∀ x y, H.Adj x y → (x ∈ A ↔ y ∈ A)) :
    (H.induce A).edgeSet.ncard + (H.induce Aᶜ).edgeSet.ncard = H.edgeSet.ncard := by
  sorry

/-! N44 induce_no_isolated_of_closed [leaf, believed provable] deps:  -/
theorem induce_no_isolated_of_closed {W : Type} (H : SimpleGraph W) (h0 : ∀ v, ∃ w, H.Adj v w)
    (A : Set W) (hA : ∀ x y, H.Adj x y → (x ∈ A ↔ y ∈ A)) :
    ∀ v : A, ∃ w, (H.induce A).Adj v w := by
  sorry

/-! N45 step_disconnected [leaf, believed provable] deps: N04 N07 N41 N42 N43 N44 -/
theorem step_disconnected (k : ℕ) (hk : 3 ≤ k) (m : ℕ)
    (ih : ∀ m' < m, ∀ (W' : Type) [Fintype W'] (H' : SimpleGraph W'), (∀ v, ∃ w, H'.Adj v w) →
      H'.edgeSet.ncard = m' → ∀ (V' : Type) [Fintype V'] (C' : SimpleGraph V'),
      (k - 1) * m' + 1 ≤ Fintype.card V' →
      (SimpleGraph.cycleGraph k).IsContained C' ∨ H'.IsContained C'ᶜ)
    {W : Type} [Fintype W] (H : SimpleGraph W) (h0 : ∀ v, ∃ w, H.Adj v w)
    (hm : H.edgeSet.ncard = m) (hc : ¬ H.Connected) (hne : Nonempty W)
    (V : Type) [Fintype V] (C : SimpleGraph V) (hV : (k - 1) * m + 1 ≤ Fintype.card V) :
    (SimpleGraph.cycleGraph k).IsContained C ∨ H.IsContained Cᶜ := by
  sorry

/-! N46 extend_by_vertex [leaf, believed provable] deps:  -/
theorem extend_by_vertex {W V : Type} (H : SimpleGraph W) (u : W) (D : SimpleGraph V)
    (f : SimpleGraph.Copy (H.induce ({u}ᶜ : Set W)) D) (x : V) (hx : x ∉ Set.range ⇑f)
    (hadj : ∀ w : ({u}ᶜ : Set W), H.Adj u w → D.Adj x (f w)) : H.IsContained D := by
  sorry

/-! N47 delete_vertex_edges [leaf, believed provable] deps:  -/
theorem delete_vertex_edges {W : Type} [Fintype W] (H : SimpleGraph W) (u : W) :
    (H.induce ({u}ᶜ : Set W)).edgeSet.ncard + (H.neighborSet u).ncard = H.edgeSet.ncard := by
  sorry

/-! N48 delete_min_vertex_no_isolated [leaf, believed provable] deps:  -/
theorem delete_min_vertex_no_isolated {W : Type} [Fintype W] (H : SimpleGraph W)
    (hc : H.Connected) (hm : 2 ≤ H.edgeSet.ncard) (u : W)
    (hu : ∀ w, (H.neighborSet u).ncard ≤ (H.neighborSet w).ncard) :
    ∀ v : ({u}ᶜ : Set W), ∃ w, (H.induce ({u}ᶜ : Set W)).Adj v w := by
  sorry

/-! N49 red_star_pigeonhole [leaf, believed provable] deps:  -/
theorem red_star_pigeonhole {V : Type} (C : SimpleGraph V) (T X : Finset V) (hT : T.Nonempty)
    (hX : ∀ x ∈ X, ∃ t ∈ T, C.Adj t x) :
    ∃ v ∈ T, ∃ S : Finset V, S ⊆ X ∧ (∀ s ∈ S, C.Adj v s) ∧ X.card ≤ T.card * S.card := by
  sorry

/-! N50 exists_red_star [leaf, believed provable] deps: N46 N47 N48 N49 -/
theorem exists_red_star (k : ℕ) (hk : 3 ≤ k) (m : ℕ)
    (ih : ∀ m' < m, ∀ (W' : Type) [Fintype W'] (H' : SimpleGraph W'), (∀ v, ∃ w, H'.Adj v w) →
      H'.edgeSet.ncard = m' → ∀ (V' : Type) [Fintype V'] (C' : SimpleGraph V'),
      (k - 1) * m' + 1 ≤ Fintype.card V' →
      (SimpleGraph.cycleGraph k).IsContained C' ∨ H'.IsContained C'ᶜ)
    {W : Type} [Fintype W] (H : SimpleGraph W) (hc : H.Connected) (hm : H.edgeSet.ncard = m)
    (hm2 : 2 ≤ m) (u : W) (hu : ∀ w, (H.neighborSet u).ncard ≤ (H.neighborSet w).ncard)
    (V : Type) [Fintype V] (C : SimpleGraph V) (hV : (k - 1) * m + 1 ≤ Fintype.card V)
    (hcyc : ¬ (SimpleGraph.cycleGraph k).IsContained C) (hH : ¬ H.IsContained Cᶜ) :
    ∃ v : V, ∃ S : Finset V, v ∉ S ∧ (∀ s ∈ S, C.Adj v s) ∧
      (k - 1) * m + 2 ≤ (H.neighborSet u).ncard * S.card + Fintype.card W := by
  sorry

/-! N51 step_min_degree_one [leaf, believed provable] deps: N21 N13 N05 N08 -/
theorem step_min_degree_one (k : ℕ) (hk : 3 ≤ k) {W : Type} [Fintype W] (H : SimpleGraph W)
    (hc : H.Connected) (m : ℕ) (hm : H.edgeSet.ncard = m) {V : Type} (C : SimpleGraph V) (v : V)
    (S : Finset V) (hvS : v ∉ S) (hS : ∀ s ∈ S, C.Adj v s)
    (hsize : (k - 1) * m + 2 ≤ 1 * S.card + Fintype.card W) :
    (SimpleGraph.cycleGraph k).IsContained C ∨ H.IsContained Cᶜ := by
  sorry

/-! N52 S_size_bound [leaf, believed provable] deps:  -/
theorem S_size_bound (k n m d s : ℕ) (hk : 3 ≤ k) (hd : 2 ≤ d) (hnd : n * d ≤ 2 * m)
    (hs : (k - 1) * m + 2 ≤ d * s + n) : (k - 2) * (n / 2) + 1 ≤ s := by
  sorry

/-! N53 blue_clique_in_S [leaf, believed provable] deps: N21 -/
theorem blue_clique_in_S (k q : ℕ) (hk : 3 ≤ k) {V : Type} (C : SimpleGraph V) (S : Finset V)
    (hS : (k - 2) * q + 1 ≤ S.card) :
    (SimpleGraph.pathGraph (k - 1)).IsContained (C.induce (S : Set V)) ∨
      ∃ U : Finset V, U ⊆ S ∧ U.card = q + 1 ∧ ∀ x ∈ U, ∀ y ∈ U, x ≠ y → Cᶜ.Adj x y := by
  sorry

/-! N54 gamma_bound [leaf, believed provable] deps: N33 N20 N05 -/
theorem gamma_bound (k : ℕ) (hk : 7 ≤ k) {W : Type} [Fintype W] (H : SimpleGraph W) (t : ℕ)
    (c : H.Coloring (Fin t)) {V : Type} (C : SimpleGraph V) (v : V) (U Gam : Finset V)
    (hU : ∀ x ∈ U, C.Adj v x) (hGam : ∀ y ∈ Gam, ∃ x ∈ U, C.Adj x y) (hdisj : Disjoint U Gam)
    (hvG : v ∉ Gam) (hfree : ¬ (SimpleGraph.cycleGraph k).IsContained C)
    (hH : ¬ H.IsContained Cᶜ) :
    Gam.card + 1 ≤ Fintype.card W + (k - 1) * (t - 1) := by
  sorry

/-! N55 glue_clique_sparse [leaf, believed provable] deps:  -/
theorem glue_clique_sparse {W V : Type} [Fintype W] (H : SimpleGraph W) (T : Finset W)
    (C : SimpleGraph V) (U1 U2 : Finset V) (hdisj : Disjoint U1 U2)
    (hcard : Fintype.card W - T.card ≤ U1.card)
    (hclique : ∀ x ∈ U1, ∀ y ∈ U1, x ≠ y → Cᶜ.Adj x y)
    (hcross : ∀ x ∈ U1, ∀ y ∈ U2, Cᶜ.Adj x y)
    (h2 : (H.induce (T : Set W)).IsContained (C.induce (U2 : Set V))ᶜ) : H.IsContained Cᶜ := by
  sorry

/-! N56 final_arith [leaf, believed provable] deps:  -/
theorem final_arith (k n m t g u2 e2 h2 : ℕ) (hk : 7 ≤ k) (hn : 4 ≤ n) (hmn : n ≤ m) (ht : 2 ≤ t)
    (hprop : 2 * n + t * (t - 3) ≤ 2 * m)
    (htot : (k - 1) * m + 1 ≤ 1 + (n / 2 + 1) + g + u2)
    (hg : g + 1 ≤ n + (k - 1) * (t - 1)) (hu2 : u2 ≤ (k - 1) * e2 ∨ u2 < h2)
    (he2 : 4 * e2 < m) (hh2 : 2 * h2 ≤ n) : False := by
  sorry

/-! N57 step_large_deg_two [join, believed provable] deps: N04 N05 N06 N13 N15 N35 N36 N39 N40 N53 N54 N55 N56 -/
theorem step_large_deg_two (k : ℕ) (hk : 7 ≤ k) (m : ℕ)
    (ih : ∀ m' < m, ∀ (W' : Type) [Fintype W'] (H' : SimpleGraph W'), (∀ v, ∃ w, H'.Adj v w) →
      H'.edgeSet.ncard = m' → ∀ (V' : Type) [Fintype V'] (C' : SimpleGraph V'),
      (k - 1) * m' + 1 ≤ Fintype.card V' →
      (SimpleGraph.cycleGraph k).IsContained C' ∨ H'.IsContained C'ᶜ)
    {W : Type} [Fintype W] (H : SimpleGraph W) (hc : H.Connected) (hm : H.edgeSet.ncard = m)
    (hδ : ∀ w, 2 ≤ (H.neighborSet w).ncard) (V : Type) [Fintype V] (C : SimpleGraph V)
    (hV : (k - 1) * m + 1 ≤ Fintype.card V) (v : V) (S : Finset V) (hvS : v ∉ S)
    (hS : ∀ s ∈ S, C.Adj v s) (hsize : (k - 2) * (Fintype.card W / 2) + 1 ≤ S.card) :
    (SimpleGraph.cycleGraph k).IsContained C ∨ H.IsContained Cᶜ := by
  sorry

/-! N58 step_connected_large [join, believed provable] deps: N06 N50 N51 N52 N57 -/
theorem step_connected_large (k : ℕ) (hk : 7 ≤ k) (m : ℕ)
    (ih : ∀ m' < m, ∀ (W' : Type) [Fintype W'] (H' : SimpleGraph W'), (∀ v, ∃ w, H'.Adj v w) →
      H'.edgeSet.ncard = m' → ∀ (V' : Type) [Fintype V'] (C' : SimpleGraph V'),
      (k - 1) * m' + 1 ≤ Fintype.card V' →
      (SimpleGraph.cycleGraph k).IsContained C' ∨ H'.IsContained C'ᶜ)
    {W : Type} [Fintype W] (H : SimpleGraph W) (hc : H.Connected) (hm : H.edgeSet.ncard = m)
    (hm2 : 2 ≤ m) (V : Type) [Fintype V] (C : SimpleGraph V)
    (hV : (k - 1) * m + 1 ≤ Fintype.card V) :
    (SimpleGraph.cycleGraph k).IsContained C ∨ H.IsContained Cᶜ := by
  sorry

/-! N59 main_property [join, believed provable] deps: N09 N11 N14 N29 N45 N58 N08 -/
theorem main_property (k : ℕ) (hk : 3 ≤ k) (m : ℕ) :
    ∀ (W : Type) [Fintype W] (H : SimpleGraph W), (∀ v, ∃ w, H.Adj v w) →
      H.edgeSet.ncard = m → ∀ (V : Type) [Fintype V] (C : SimpleGraph V),
      (k - 1) * m + 1 ≤ Fintype.card V →
      (SimpleGraph.cycleGraph k).IsContained C ∨ H.IsContained Cᶜ := by
  sorry

/-! ## Root -/

/-- **Cambie–Freschi (2026), Theorem 3.** For every `k ≥ 3` and every graph `H` with `m` edges and no isolated
vertices, `R(C_k, H) ≤ (k - 1) * m + 1`. -/
theorem cambie_freschi (k : ℕ) (hk : 3 ≤ k) (m : ℕ) (W : Type) [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (h0 : ∀ v, 0 < H.degree v) (hm : H.edgeSet.ncard = m) :
    SimpleGraph.graphRamsey (SimpleGraph.cycleGraph k) H ≤ (k - 1) * m + 1 := by
  sorry

end Erdos569
