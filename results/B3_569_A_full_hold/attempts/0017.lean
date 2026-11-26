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
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 3 := ⟨k - 3, by omega⟩
  intro v
  refine ⟨v + 1, ?_⟩
  rw [SimpleGraph.cycleGraph_adj']
  right
  simp
/-! N02 cycleGraph_edgeSet_ncard [leaf, believed provable] deps:  -/
theorem cycleGraph_edgeSet_ncard (k : ℕ) (hk : 3 ≤ k) :
    (SimpleGraph.cycleGraph k).edgeSet.ncard = k := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 3 := ⟨k - 3, by omega⟩
  have h := SimpleGraph.sum_degrees_eq_twice_card_edges (SimpleGraph.cycleGraph (n + 3))
  simp only [SimpleGraph.cycleGraph_degree_three_le, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at h
  rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  omega
/-! N03 isContained_top_of_card_le [join, believed provable] deps:  -/
theorem isContained_top_of_card_le {W V : Type} [Fintype W] [Fintype V] (H : SimpleGraph W)
    (h : Fintype.card W ≤ Fintype.card V) : H.IsContained (⊤ : SimpleGraph V) := by
  exact SimpleGraph.isContained_top_iff.mpr (Function.Embedding.nonempty_of_card_le h)
/-! N04 isContained_of_induce [join, believed provable] deps:  -/
theorem isContained_of_induce {W V : Type} {H : SimpleGraph W} {C : SimpleGraph V} (s : Set V)
    (h : H.IsContained (C.induce s)) : H.IsContained C := by
  exact h.trans ⟨SimpleGraph.Copy.induce C s⟩
/-! N05 isContained_compl_of_compl_induce [join, believed provable] deps:  -/
theorem isContained_compl_of_compl_induce {W V : Type} {H : SimpleGraph W} {C : SimpleGraph V}
    (s : Set V) (h : H.IsContained (C.induce s)ᶜ) : H.IsContained Cᶜ := by
  refine h.trans ⟨⟨⟨Subtype.val, fun {a b} hab => ?_⟩, Subtype.val_injective⟩⟩
  rw [SimpleGraph.compl_adj] at hab ⊢
  exact ⟨fun h' => hab.1 (Subtype.ext h'), hab.2⟩
/-! N06 degree_sum_ncard [join, believed provable] deps:  -/
theorem degree_sum_ncard {W : Type} [Fintype W] (H : SimpleGraph W) :
    ∑ v, (H.neighborSet v).ncard = 2 * H.edgeSet.ncard := by
  classical
  simp_rw [Set.ncard_eq_toFinset_card', Set.toFinset_card, SimpleGraph.card_neighborSet_eq_degree,
    ← SimpleGraph.edgeFinset_card]
  exact SimpleGraph.sum_degrees_eq_twice_card_edges H
/-! N07 card_le_two_mul_ncard [leaf, believed provable] deps: N06 -/
theorem card_le_two_mul_ncard {W : Type} [Fintype W] (H : SimpleGraph W)
    (h0 : ∀ v, ∃ w, H.Adj v w) : Fintype.card W ≤ 2 * H.edgeSet.ncard := by
  rw [← degree_sum_ncard H, ← Finset.card_univ, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro v _
  obtain ⟨w, hw⟩ := h0 v
  exact Nat.one_le_iff_ne_zero.mpr ((Set.ncard_pos (Set.toFinite _)).mpr ⟨w, hw⟩).ne'
/-! N08 connected_card_le_ncard_add_one [join, believed provable] deps:  -/
theorem connected_card_le_ncard_add_one {W : Type} [Fintype W] (H : SimpleGraph W)
    (hc : H.Connected) : Fintype.card W ≤ H.edgeSet.ncard + 1 := by
  have h := hc.card_vert_le_card_edgeSet_add_one
  rwa [Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at h
/-! N09 ramsey_zero_edges [leaf, believed provable] deps:  -/
theorem ramsey_zero_edges {W : Type} [Fintype W] (H : SimpleGraph W) (h0 : ∀ v, ∃ w, H.Adj v w)
    (hm : H.edgeSet.ncard = 0) {V : Type} (C : SimpleGraph V) : H.IsContained Cᶜ := by
  have : IsEmpty W := by
    refine ⟨fun v => ?_⟩
    obtain ⟨w, hw⟩ := h0 v
    have hmem : s(v, w) ∈ H.edgeSet := by rw [SimpleGraph.mem_edgeSet]; exact hw
    rw [Set.ncard_eq_zero] at hm
    rw [hm] at hmem
    exact hmem
  exact SimpleGraph.IsContained.of_isEmpty
/-! N10 one_edge_isContained_of_adj [leaf, believed provable] deps:  -/
theorem one_edge_isContained_of_adj {W V : Type} [Fintype W] (H : SimpleGraph W)
    (h0 : ∀ v, ∃ w, H.Adj v w) (hm : H.edgeSet.ncard = 1) (D : SimpleGraph V) {x y : V}
    (hxy : D.Adj x y) : H.IsContained D := by
  classical
  obtain ⟨e, he⟩ := Set.ncard_eq_one.mp hm
  induction e using Sym2.ind with
  | h a b =>
  have hab : H.Adj a b := by
    have : s(a, b) ∈ H.edgeSet := by rw [he]; rfl
    exact this
  have hmem : ∀ v w, H.Adj v w → (v = a ∧ w = b) ∨ (v = b ∧ w = a) := by
    intro v w hvw
    have : s(v, w) ∈ H.edgeSet := hvw
    rw [he, Set.mem_singleton_iff, Sym2.eq_iff] at this
    exact this
  have hall : ∀ v, v = a ∨ v = b := by
    intro v
    obtain ⟨w, hw⟩ := h0 v
    rcases hmem v w hw with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact Or.inl h1
    · exact Or.inr h1
  have hne : x ≠ y := hxy.ne
  have hba : b ≠ a := hab.ne.symm
  refine ⟨⟨⟨fun v => if v = a then x else y, ?_⟩, ?_⟩⟩
  · intro v w hvw
    rcases hmem v w hvw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [if_pos rfl, if_neg hba]
      exact hxy
    · simp only [if_pos rfl, if_neg hba]
      exact hxy.symm
  · intro v w hvw
    have hvw' : (if v = a then x else y) = (if w = a then x else y) := hvw
    rcases hall v with rfl | rfl <;> rcases hall w with rfl | rfl
    · rfl
    · rw [if_pos rfl, if_neg hba] at hvw'; exact absurd hvw' hne
    · rw [if_neg hba, if_pos rfl] at hvw'; exact absurd hvw'.symm hne
    · rfl
/-! N11 ramsey_one_edge [leaf, believed provable] deps: N03 N10 -/
theorem ramsey_one_edge (k : ℕ) (hk : 3 ≤ k) {W : Type} [Fintype W] (H : SimpleGraph W)
    (h0 : ∀ v, ∃ w, H.Adj v w) (hm : H.edgeSet.ncard = 1) (V : Type) [Fintype V]
    (C : SimpleGraph V) (hV : (k - 1) * 1 + 1 ≤ Fintype.card V) :
    (SimpleGraph.cycleGraph k).IsContained C ∨ H.IsContained Cᶜ := by
  by_cases hex : ∃ x y, Cᶜ.Adj x y
  · obtain ⟨x, y, hxy⟩ := hex
    exact Or.inr (one_edge_isContained_of_adj H h0 hm Cᶜ hxy)
  · left
    push_neg at hex
    have htop : (⊤ : SimpleGraph V) ≤ C := by
      intro x y hxy
      by_contra hc
      exact hex x y ((SimpleGraph.compl_adj C x y).mpr ⟨hxy.ne, hc⟩)
    have h1 : (SimpleGraph.cycleGraph k).IsContained (⊤ : SimpleGraph V) :=
      isContained_top_of_card_le _ (by simp only [Fintype.card_fin]; omega)
    exact h1.mono_right htop
/-! N12 cycle_of_closed_seq [join, believed provable] deps:  -/
theorem cycle_of_closed_seq {V : Type} (C : SimpleGraph V) (k : ℕ) (hk : 3 ≤ k) (f : ℕ → V)
    (hinj : Set.InjOn f (Set.Iio k)) (hadj : ∀ i, i + 1 < k → C.Adj (f i) (f (i + 1)))
    (hclose : C.Adj (f (k - 1)) (f 0)) : (SimpleGraph.cycleGraph k).IsContained C := by
  have key : ∀ i j : Fin k, (j - i).val = 1 → C.Adj (f i) (f j) := by
    intro i j h
    rcases Nat.lt_or_ge j i with hij | hij
    · rw [Fin.coe_sub_iff_lt.mpr (Fin.lt_def.mpr hij)] at h
      have hi : (i : ℕ) = k - 1 := by omega
      have hj : (j : ℕ) = 0 := by omega
      rw [hi, hj]; exact hclose
    · rw [Fin.coe_sub_iff_le.mpr (Fin.le_def.mpr hij)] at h
      have : (j : ℕ) = i + 1 := by omega
      rw [this]; exact hadj i (by omega)
  refine ⟨⟨⟨fun i => f i, fun {u v} huv => ?_⟩, fun u v huv => ?_⟩⟩
  · rcases SimpleGraph.cycleGraph_adj'.mp huv with h | h
    · exact (key v u h).symm
    · exact key u v h
  · exact Fin.ext (hinj (Set.mem_Iio.mpr u.isLt) (Set.mem_Iio.mpr v.isLt) huv)
/-! N13 cycle_of_path_in_nbhd [join, believed provable] deps: N12 -/
theorem cycle_of_path_in_nbhd {V : Type} (C : SimpleGraph V) (k : ℕ) (hk : 3 ≤ k) (v : V)
    (S : Set V) (hS : ∀ s ∈ S, C.Adj v s) (hv : v ∉ S)
    (hP : (SimpleGraph.pathGraph (k - 1)).IsContained (C.induce S)) :
    (SimpleGraph.cycleGraph k).IsContained C := by
  obtain ⟨g⟩ := hP
  let f : ℕ → V := fun i => if h : 0 < i ∧ i < k then (g ⟨i - 1, by omega⟩ : V) else v
  have hf0 : f 0 = v := by simp [f]
  have hfpos : ∀ i, 0 < i → i < k → ∀ (h : i - 1 < k - 1), f i = (g ⟨i - 1, h⟩ : V) := by
    intro i hi hik h
    simp only [f]
    rw [dif_pos ⟨hi, hik⟩]
  have hmemS : ∀ i, 0 < i → i < k → f i ∈ S := by
    intro i hi hik
    rw [hfpos i hi hik (by omega)]
    exact (g _).2
  refine cycle_of_closed_seq C k hk f ?_ ?_ ?_
  · intro i hi j hj hij
    simp only [Set.mem_Iio] at hi hj
    rcases Nat.eq_zero_or_pos i with rfl | hi0 <;> rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rfl
    · have : f j ∈ S := hmemS j hj0 hj
      rw [← hij, hf0] at this
      exact absurd this hv
    · have : f i ∈ S := hmemS i hi0 hi
      rw [hij, hf0] at this
      exact absurd this hv
    · rw [hfpos i hi0 hi (by omega), hfpos j hj0 hj (by omega)] at hij
      have := g.injective (Subtype.val_injective hij)
      simp only [Fin.mk.injEq] at this
      omega
  · intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [hf0, hfpos 1 one_pos (by omega) (by omega)]
      exact hS _ (g _).2
    · rw [hfpos i hi0 (by omega) (by omega), hfpos (i + 1) (by omega) hi (by omega)]
      have : (SimpleGraph.pathGraph (k - 1)).Adj ⟨i - 1, by omega⟩ ⟨i + 1 - 1, by omega⟩ := by
        rw [SimpleGraph.pathGraph_adj]; left; simp only; omega
      exact g.toHom.map_adj this
  · rw [hf0, hfpos (k - 1) (by omega) (by omega) (by omega)]
    exact (hS _ (g _).2).symm
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
  have h2 := goddard_kleitman_sidorenko (SimpleGraph.cycleGraph k) (cycleGraph_no_isolated k hk) k
    (cycleGraph_edgeSet_ncard k hk) V Cᶜ hV
  rcases h2 with h | h
  · right
    have h3 : H.IsContained (⊤ : SimpleGraph (Fin 3)) :=
      isContained_top_of_card_le H (by simp [hW])
    rw [SimpleGraph.cycleGraph_three_eq_top] at h
    exact h3.trans h
  · left; rwa [compl_compl] at h
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
  classical
  by_cases ha : 1 ≤ a
  swap
  · right
    exact ⟨∅, X, Finset.empty_subset _, le_rfl, by omega, by omega, by simp⟩
  by_cases hb : 1 ≤ b
  swap
  · right
    exact ⟨X, ∅, le_rfl, Finset.empty_subset _, by omega, by omega, by simp⟩
  have hcard : a + b + k - 2 ≤ Fintype.card (X : Set V) := by simpa using hX
  rcases haggkvist k a b hk ha hb (X : Set V) (C.induce (X : Set V)) hcard with h | h
  · exact Or.inl (isContained_of_induce _ h)
  · right
    obtain ⟨g⟩ := h
    have hinjP : Function.Injective (fun i : Fin a => (g (Sum.inl i) : V)) := by
      intro i j h
      exact Sum.inl_injective (g.injective (Subtype.val_injective h))
    have hinjQ : Function.Injective (fun j : Fin b => (g (Sum.inr j) : V)) := by
      intro i j h
      exact Sum.inr_injective (g.injective (Subtype.val_injective h))
    refine ⟨Finset.univ.image (fun i : Fin a => (g (Sum.inl i) : V)),
      Finset.univ.image (fun j : Fin b => (g (Sum.inr j) : V)), ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨i, _, rfl⟩ := hx
      exact (g (Sum.inl i)).2
    · intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨i, _, rfl⟩ := hx
      exact (g (Sum.inr i)).2
    · rw [Finset.card_image_of_injective _ hinjP, Finset.card_univ, Fintype.card_fin]
    · rw [Finset.card_image_of_injective _ hinjQ, Finset.card_univ, Fintype.card_fin]
    · intro x hx y hy
      rw [Finset.mem_image] at hx hy
      obtain ⟨i, _, rfl⟩ := hx
      obtain ⟨j, _, rfl⟩ := hy
      have hadj : (completeBipartiteGraph (Fin a) (Fin b)).Adj (Sum.inl i) (Sum.inr j) :=
        Or.inl ⟨rfl, rfl⟩
      have := g.toHom.map_adj hadj
      rw [SimpleGraph.compl_adj] at this ⊢
      exact ⟨fun h => this.1 (Subtype.ext h), this.2⟩
/-! N18 multipartite_parts [leaf, believed provable] deps: N17 -/
theorem multipartite_parts (k : ℕ) (hk : 2 ≤ k) (t : ℕ) (n : Fin t → ℕ) {V : Type} [Fintype V]
    (C : SimpleGraph V) (X : Finset V) (hX : (k - 2) * (t - 1) + ∑ i, n i ≤ X.card) :
    (SimpleGraph.pathGraph k).IsContained C ∨
      ∃ P : Fin t → Finset V, (∀ i, P i ⊆ X) ∧ (∀ i, n i ≤ (P i).card) ∧
        ∀ i j, i ≠ j → ∀ x ∈ P i, ∀ y ∈ P j, Cᶜ.Adj x y := by
  classical
  induction t generalizing X with
  | zero =>
    right
    exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ t ih =>
    rw [Fin.sum_univ_succ] at hX
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · right
      refine ⟨fun _ => X, fun _ => le_rfl, fun i => ?_,
        fun i j hij => absurd (Fin.ext (by have := i.isLt; have := j.isLt; omega)) hij⟩
      have hi : i = 0 := Fin.ext (by have := i.isLt; simp only [Fin.val_zero]; omega)
      subst hi
      simpa using hX
    · have hb : n 0 + ((k - 2) * (t - 1) + ∑ i : Fin t, n i.succ) + k - 2 ≤ X.card := by
        have : (k - 2) * (t + 1 - 1) = (k - 2) * (t - 1) + (k - 2) := by
          obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
          simp only [Nat.add_sub_cancel]
          ring
        omega
      rcases haggkvist_parts k (n 0) ((k - 2) * (t - 1) + ∑ i : Fin t, n i.succ) hk C X hb with
        h | ⟨P, Q, hPX, hQX, hPcard, hQcard, hPQ⟩
      · exact Or.inl h
      · rcases ih (fun i => n i.succ) Q hQcard with h | ⟨P', hP'Q, hP'card, hP'cross⟩
        · exact Or.inl h
        · right
          refine ⟨Fin.cons P P', ?_, ?_, ?_⟩
          · intro i
            rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
            · simp only [Fin.cons_zero]; exact hPX
            · simp only [Fin.cons_succ]; exact (hP'Q i').trans hQX
          · intro i
            rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
            · simp only [Fin.cons_zero]; exact hPcard
            · simp only [Fin.cons_succ]; exact hP'card i'
          · intro i j hij x hx y hy
            rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩ <;>
              rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
            · exact absurd rfl hij
            · simp only [Fin.cons_zero] at hx
              simp only [Fin.cons_succ] at hy
              exact hPQ x hx y (hP'Q j' hy)
            · simp only [Fin.cons_succ] at hx
              simp only [Fin.cons_zero] at hy
              exact (hPQ y hy x (hP'Q i' hx)).symm
            · simp only [Fin.cons_succ] at hx hy
              exact hP'cross i' j' (fun h => hij (by rw [h])) x hx y hy
/-! N19 embed_colored_into_parts [leaf, believed provable] deps:  -/
theorem embed_colored_into_parts {W V : Type} [Fintype W] (H : SimpleGraph W) (t : ℕ)
    (c : H.Coloring (Fin t)) (D : SimpleGraph V) (P : Fin t → Finset V)
    (hP : ∀ i, (Finset.univ.filter (fun w => c w = i)).card ≤ (P i).card)
    (hcross : ∀ i j, i ≠ j → ∀ x ∈ P i, ∀ y ∈ P j, D.Adj x y) : H.IsContained D := by
  classical
  have hemb : ∀ i : Fin t, Nonempty ({w // c w = i} ↪ P i) := by
    intro i
    apply Function.Embedding.nonempty_of_card_le
    simpa [Fintype.card_subtype] using hP i
  let e : ∀ i, {w // c w = i} ↪ P i := fun i => (hemb i).some
  let φ : W → V := fun w => (e (c w) ⟨w, rfl⟩ : V)
  have hφ : ∀ w, φ w ∈ P (c w) := fun w => (e (c w) ⟨w, rfl⟩).2
  have key : ∀ (w : W) (j : Fin t) (h : c w = j), (e j ⟨w, h⟩ : V) = φ w := by
    intro w j h
    subst h
    rfl
  refine ⟨⟨⟨φ, fun {a b} hab => ?_⟩, fun a b hab => ?_⟩⟩
  · exact hcross _ _ (c.valid hab) _ (hφ a) _ (hφ b)
  · have hab' : φ a = φ b := hab
    by_cases hc : c a = c b
    · have h1 := key b (c a) hc.symm
      have h2 : (e (c a) ⟨a, rfl⟩ : V) = φ a := rfl
      have h3 : (e (c a) ⟨a, rfl⟩ : V) = (e (c a) ⟨b, hc.symm⟩ : V) := by rw [h1, h2]; exact hab'
      have h4 := (e (c a)).injective (Subtype.val_injective h3)
      exact congrArg Subtype.val h4
    · have := hcross _ _ hc _ (hφ a) _ (hφ b)
      exact absurd hab' this.ne
/-! N20 lemma5_path_coloring [join, believed provable] deps: N18 N19 -/
theorem lemma5_path_coloring (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] (H : SimpleGraph W)
    (t : ℕ) (c : H.Coloring (Fin t)) (V : Type) [Fintype V] (C : SimpleGraph V)
    (hV : Fintype.card W + (k - 2) * (t - 1) ≤ Fintype.card V) :
    (SimpleGraph.pathGraph k).IsContained C ∨ H.IsContained Cᶜ := by
  classical
  have hsum : ∑ i : Fin t, (Finset.univ.filter (fun w => c w = i)).card = Fintype.card W := by
    rw [← Finset.card_univ]
    exact (Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ) (f := c)
      (fun x _ => Finset.mem_univ _)).symm
  rcases multipartite_parts k hk t (fun i => (Finset.univ.filter (fun w => c w = i)).card) C
    Finset.univ (by rw [hsum, Finset.card_univ]; omega) with h | h
  · exact Or.inl h
  · obtain ⟨P, _, hP, hcross⟩ := h
    exact Or.inr (embed_colored_into_parts H t c Cᶜ P hP hcross)
/-! N21 cor6_path_ramsey [join, believed provable] deps: N20 -/
theorem cor6_path_ramsey (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] (H : SimpleGraph W)
    (V : Type) [Fintype V] (C : SimpleGraph V)
    (hV : (k - 1) * (Fintype.card W - 1) + 1 ≤ Fintype.card V) :
    (SimpleGraph.pathGraph k).IsContained C ∨ H.IsContained Cᶜ := by
  rcases isEmpty_or_nonempty W with hW | hW
  · exact Or.inr SimpleGraph.IsContained.of_isEmpty
  · have hpos : 1 ≤ Fintype.card W := Fintype.card_pos
    obtain ⟨c⟩ := H.colorable_of_fintype
    apply lemma5_path_coloring k hk H (Fintype.card W) c V C
    have : Fintype.card W + (k - 2) * (Fintype.card W - 1) = (k - 1) * (Fintype.card W - 1) + 1 := by
      obtain ⟨n, hn⟩ : ∃ n, Fintype.card W = n + 1 := ⟨Fintype.card W - 1, by omega⟩
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
      rw [hn, Nat.add_sub_cancel, Nat.add_sub_cancel, show k' + 2 - 1 = k' + 1 by omega]
      ring
    omega
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
  classical
  have hn := connected_card_le_ncard_add_one H hc
  rw [hm] at hn
  have hclique : ∀ r, Fintype.card W ≤ r → (⊤ : SimpleGraph (Fin r)).IsContained Cᶜ →
      H.IsContained Cᶜ :=
    fun r hr h => (isContained_top_of_card_le H (by simpa using hr)).trans h
  rcases hk with rfl | rfl | rfl
  · exact jayawardene_C4 H hc m hm hm2 V C (by omega)
  · rcases Nat.lt_or_ge (Fintype.card W) 4 with h4 | h4
    · rcases ramsey_C5_K3 V C (by omega) with h | h
      · exact Or.inl h
      · exact Or.inr (hclique 3 (by omega) h)
    · exact jayawardene_C5 H hc h4 m hm V C (by omega)
  · rcases Nat.lt_or_ge (Fintype.card W) 6 with h6 | h6
    · rcases Nat.lt_or_ge (Fintype.card W) 4 with h4 | h4
      · rcases ramsey_C6_K3 V C (by omega) with h | h
        · exact Or.inl h
        · exact Or.inr (hclique 3 (by omega) h)
      · rcases Nat.lt_or_ge (Fintype.card W) 5 with h5 | h5
        · rcases ramsey_C6_K4 V C (by omega) with h | h
          · exact Or.inl h
          · exact Or.inr (hclique 4 (by omega) h)
        · rcases ramsey_C6_K5 V C (by omega) with h | h
          · exact Or.inl h
          · exact Or.inr (hclique 5 (by omega) h)
    · exact jayawardene_C6 H hc h6 m hm V C (by omega)
/-! N30 claim8 [join, believed provable] deps: N12 -/
theorem claim8 (k : ℕ) (hk : 7 ≤ k) {V : Type} (C : SimpleGraph V) (v : V) (w u : ℕ → V)
    (hw : Set.InjOn w (Set.Iic k)) (hwadj : ∀ i, i < k → C.Adj (w i) (w (i + 1)))
    (hvu : ∀ i, i ≤ k → C.Adj v (u i)) (huw : ∀ i, i ≤ k → C.Adj (u i) (w i))
    (huw' : ∀ i j, i ≤ k → j ≤ k → u i ≠ w j) (hvw : ∀ j, j ≤ k → v ≠ w j)
    (hfree : ¬ (SimpleGraph.cycleGraph k).IsContained C) :
    ∀ i, i ≤ 4 → u i = u (k - 4 + i) := by
  intro i hi
  by_contra hne
  set j := k - 4 + i with hj
  have hjk : j ≤ k := by omega
  have hik : i ≤ k := by omega
  let f : ℕ → V := fun n => if n = 0 then v else if n = 1 then u i else
    if n ≤ k - 2 then w (i + (n - 2)) else u j
  have hf0 : f 0 = v := by simp [f]
  have hf1 : f 1 = u i := by simp [f]
  have hfw : ∀ n, 2 ≤ n ∧ n ≤ k - 2 → f n = w (i + (n - 2)) := by
    intro n hn
    simp only [f]
    rw [if_neg (by omega), if_neg (by omega), if_pos hn.2]
  have hfk : f (k - 1) = u j := by
    simp only [f]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have hcases : ∀ n, n < k → n = 0 ∨ n = 1 ∨ (2 ≤ n ∧ n ≤ k - 2) ∨ n = k - 1 := by
    intro n hn; omega
  have hvu' : ∀ l, l ≤ k → v ≠ u l := fun l hl => (hvu l hl).ne
  have hwmem : ∀ n, 2 ≤ n ∧ n ≤ k - 2 → i + (n - 2) ∈ Set.Iic k := fun n hn => Set.mem_Iic.mpr (by omega)
  apply hfree
  refine cycle_of_closed_seq C k (by omega) f ?_ ?_ ?_
  · intro a ha b hb hab
    simp only [Set.mem_Iio] at ha hb
    rcases hcases a ha with rfl | rfl | hamid | rfl <;> rcases hcases b hb with rfl | rfl | hbmid | rfl
    · rfl
    · rw [hf0, hf1] at hab; exact absurd hab (hvu' i hik)
    · rw [hf0, hfw b hbmid] at hab; exact absurd hab (hvw _ (hwmem b hbmid))
    · rw [hf0, hfk] at hab; exact absurd hab (hvu' j hjk)
    · rw [hf1, hf0] at hab; exact absurd hab.symm (hvu' i hik)
    · rfl
    · rw [hf1, hfw b hbmid] at hab; exact absurd hab (huw' i _ hik (hwmem b hbmid))
    · rw [hf1, hfk] at hab; exact absurd hab hne
    · rw [hfw a hamid, hf0] at hab; exact absurd hab.symm (hvw _ (hwmem a hamid))
    · rw [hfw a hamid, hf1] at hab; exact absurd hab.symm (huw' i _ hik (hwmem a hamid))
    · rw [hfw a hamid, hfw b hbmid] at hab
      have := hw (hwmem a hamid) (hwmem b hbmid) hab
      omega
    · rw [hfw a hamid, hfk] at hab; exact absurd hab.symm (huw' j _ hjk (hwmem a hamid))
    · rw [hfk, hf0] at hab; exact absurd hab.symm (hvu' j hjk)
    · rw [hfk, hf1] at hab; exact absurd hab.symm hne
    · rw [hfk, hfw b hbmid] at hab; exact absurd hab (huw' j _ hjk (hwmem b hbmid))
    · rfl
  · intro a ha
    rcases hcases a (by omega) with rfl | rfl | hamid | rfl
    · rw [hf0, hf1]; exact hvu i hik
    · rw [hf1, hfw 2 ⟨le_rfl, by omega⟩]
      simp only [Nat.sub_self, add_zero]
      exact huw i hik
    · rcases Nat.lt_or_ge (a + 1) (k - 1) with ha1 | ha1
      · rw [hfw a hamid, hfw (a + 1) ⟨by omega, by omega⟩]
        have : i + (a + 1 - 2) = i + (a - 2) + 1 := by omega
        rw [this]
        exact hwadj _ (by omega)
      · have ha' : a + 1 = k - 1 := by omega
        rw [hfw a hamid, ha', hfk]
        have : i + (a - 2) = j := by omega
        rw [this]
        exact (huw j hjk).symm
    · omega
  · rw [hfk, hf0]
    exact (hvu j hjk).symm
/-! N31 claim9 [leaf, believed provable] deps: N30 N12 -/
theorem claim9 (k : ℕ) (hk : 7 ≤ k) {V : Type} (C : SimpleGraph V) (v : V) (w u : ℕ → V)
    (hw : Set.InjOn w (Set.Iic k)) (hwadj : ∀ i, i < k → C.Adj (w i) (w (i + 1)))
    (hvu : ∀ i, i ≤ k → C.Adj v (u i)) (huw : ∀ i, i ≤ k → C.Adj (u i) (w i))
    (huw' : ∀ i j, i ≤ k → j ≤ k → u i ≠ w j) (hvw : ∀ j, j ≤ k → v ≠ w j)
    (hfree : ¬ (SimpleGraph.cycleGraph k).IsContained C) :
    ∀ i, i ≤ 2 → u i ≠ u (i + 2) := by
  intro i hi
  intro heq
  have h8 := claim8 k hk C v w u hw hwadj hvu huw huw' hvw hfree (i + 2) (by omega)
  -- u (i+2) = u (k - 4 + (i + 2)) = u (i + k - 2)
  have hik : i + k - 2 ≤ k := by omega
  let f : ℕ → V := fun n => if n = 0 then u i else w (i + (n - 1))
  have hf0 : f 0 = u i := by simp [f]
  have hfw : ∀ n, 1 ≤ n → f n = w (i + (n - 1)) := by
    intro n hn
    simp only [f]
    rw [if_neg (by omega)]
  have hwmem : ∀ n, 1 ≤ n → n < k → i + (n - 1) ∈ Set.Iic k := fun n hn hnk => Set.mem_Iic.mpr (by omega)
  apply hfree
  refine cycle_of_closed_seq C k (by omega) f ?_ ?_ ?_
  · intro a ha b hb hab
    simp only [Set.mem_Iio] at ha hb
    rcases Nat.eq_zero_or_pos a with rfl | ha0 <;> rcases Nat.eq_zero_or_pos b with rfl | hb0
    · rfl
    · rw [hf0, hfw b hb0] at hab; exact absurd hab (huw' i _ (by omega) (hwmem b hb0 hb))
    · rw [hfw a ha0, hf0] at hab; exact absurd hab.symm (huw' i _ (by omega) (hwmem a ha0 ha))
    · rw [hfw a ha0, hfw b hb0] at hab
      have := hw (hwmem a ha0 ha) (hwmem b hb0 hb) hab
      omega
  · intro a ha
    rcases Nat.eq_zero_or_pos a with rfl | ha0
    · rw [hf0, hfw 1 le_rfl]
      simp only [Nat.sub_self, add_zero]
      exact huw i (by omega)
    · rw [hfw a ha0, hfw (a + 1) (by omega)]
      have : i + (a + 1 - 1) = i + (a - 1) + 1 := by omega
      rw [this]
      exact hwadj _ (by omega)
  · rw [hfw (k - 1) (by omega), hf0]
    have : i + (k - 1 - 1) = k - 4 + (i + 2) := by omega
    rw [this, heq, h8]
    exact (huw _ (by omega)).symm
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
  classical
  obtain ⟨g⟩ := hP
  let w : ℕ → V := fun i => if h : i < k + 1 then (g ⟨i, h⟩ : V) else v
  have hw : ∀ i (h : i < k + 1), w i = (g ⟨i, h⟩ : V) := fun i h => by simp only [w, dif_pos h]
  have hwG : ∀ i, i ≤ k → w i ∈ Gam := fun i hi => by
    rw [hw i (by omega)]
    exact (g _).2
  have hex : ∀ i, ∃ x, i ≤ k → x ∈ U ∧ C.Adj x (w i) := by
    intro i
    by_cases hi : i ≤ k
    · obtain ⟨x, hxU, hx⟩ := hGam (w i) (hwG i hi)
      exact ⟨x, fun _ => ⟨hxU, hx⟩⟩
    · exact ⟨v, fun h => absurd h hi⟩
  choose u hu using hex
  apply lemma7 k hk C v w u
  · intro a ha b hb hab
    simp only [Set.mem_Iic] at ha hb
    rw [hw a (by omega), hw b (by omega)] at hab
    have := g.injective (Subtype.val_injective hab)
    simp only [Fin.mk.injEq] at this
    exact this
  · intro i hi
    rw [hw i (by omega), hw (i + 1) (by omega)]
    have : (SimpleGraph.pathGraph (k + 1)).Adj ⟨i, by omega⟩ ⟨i + 1, by omega⟩ := by
      rw [SimpleGraph.pathGraph_adj]
      left
      rfl
    exact g.toHom.map_adj this
  · intro i hi
    exact hU _ (hu i hi).1
  · intro i hi
    exact (hu i hi).2
  · intro i j hi hj heq
    exact Set.disjoint_left.mp hdisj (hu i hi).1 (heq ▸ hwG j hj)
  · intro j hj heq
    exact hvG (heq ▸ hwG j hj)
/-! N34 exists_critical_vertex_set [leaf, believed provable] deps:  -/
theorem exists_critical_vertex_set {W : Type} [Fintype W] (H : SimpleGraph W) (s : ℕ)
    (h : ¬ H.Colorable s) :
    ∃ X : Finset W, ¬ (H.induce (X : Set W)).Colorable s ∧
      ∀ x ∈ X, s ≤ (H.neighborSet x ∩ (X : Set W)).ncard := by
  classical
  let P : Finset W → Prop := fun X => ¬ (H.induce (X : Set W)).Colorable s
  have huniv : P Finset.univ := by
    intro hcol
    apply h
    obtain ⟨c⟩ := hcol
    exact ⟨SimpleGraph.Coloring.mk (fun w => c ⟨w, Finset.mem_univ w⟩) (fun hvw => c.valid hvw)⟩
  obtain ⟨X, hXP, hXmin⟩ := Finset.exists_min_image (Finset.univ.filter P) Finset.card
    ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, huniv⟩⟩
  have hXP' : P X := (Finset.mem_filter.mp hXP).2
  refine ⟨X, hXP', ?_⟩
  intro x hx
  by_contra hlt
  push_neg at hlt
  have hcol : (H.induce ((X.erase x : Finset W) : Set W)).Colorable s := by
    by_contra hnot
    have hmem : X.erase x ∈ Finset.univ.filter P := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnot⟩
    have h1 := hXmin _ hmem
    have h2 := Finset.card_erase_lt_of_mem hx
    omega
  obtain ⟨c⟩ := hcol
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  let c0 : W → Fin (s' + 1) := fun y => if hy : y ∈ X.erase x then c ⟨y, hy⟩ else 0
  let N : Finset W := X.filter (fun y => H.Adj x y)
  have hNcard : N.card < s' + 1 := by
    have : N.card = (H.neighborSet x ∩ (X : Set W)).ncard := by
      rw [Set.ncard_eq_toFinset_card']
      congr 1
      ext y
      simp only [N, Finset.mem_filter, Set.mem_toFinset, Set.mem_inter_iff,
        SimpleGraph.mem_neighborSet, Finset.mem_coe]
      exact and_comm
    omega
  have hused : (N.image c0).card < (Finset.univ : Finset (Fin (s' + 1))).card := by
    calc (N.image c0).card ≤ N.card := Finset.card_image_le
      _ < s' + 1 := hNcard
      _ = _ := by rw [Finset.card_univ, Fintype.card_fin]
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card hused
  let c1 : W → Fin (s' + 1) := fun y => if y = x then i else c0 y
  apply hXP'
  refine ⟨SimpleGraph.Coloring.mk (fun y => c1 y.1) ?_⟩
  intro a b hab
  have hab' : H.Adj a.1 b.1 := hab
  simp only [c1]
  by_cases ha : a.1 = x <;> by_cases hb : b.1 = x
  · exact absurd (ha.trans hb.symm) hab'.ne
  · rw [if_pos ha, if_neg hb]
    intro heq
    apply hi
    rw [Finset.mem_image]
    exact ⟨b.1, Finset.mem_filter.mpr ⟨b.2, ha ▸ hab'⟩, heq.symm⟩
  · rw [if_neg ha, if_pos hb]
    intro heq
    apply hi
    rw [Finset.mem_image]
    exact ⟨a.1, Finset.mem_filter.mpr ⟨a.2, hb ▸ hab'.symm⟩, heq⟩
  · rw [if_neg ha, if_neg hb]
    have ha' : a.1 ∈ X.erase x := Finset.mem_erase.mpr ⟨ha, a.2⟩
    have hb' : b.1 ∈ X.erase x := Finset.mem_erase.mpr ⟨hb, b.2⟩
    simp only [c0, dif_pos ha', dif_pos hb']
    exact c.valid (show (H.induce _).Adj ⟨a.1, ha'⟩ ⟨b.1, hb'⟩ from hab')
/-! N35 prop10 [leaf, believed provable] deps: N34 N06 -/
theorem prop10 {W : Type} [Fintype W] (H : SimpleGraph W) (hδ : ∀ v, 2 ≤ (H.neighborSet v).ncard)
    (t : ℕ) (ht : ¬ H.Colorable (t - 1)) :
    2 * Fintype.card W + t * (t - 3) ≤ 2 * H.edgeSet.ncard := by
  classical
  rcases Nat.lt_or_ge t 3 with ht3 | ht3
  · have h0 : t - 3 = 0 := by omega
    rw [h0, mul_zero, add_zero]
    have h1 : ∑ _v : W, 2 ≤ ∑ v, (H.neighborSet v).ncard := Finset.sum_le_sum (fun v _ => hδ v)
    rw [degree_sum_ncard H, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h1
    omega
  obtain ⟨X, hXcol, hXdeg⟩ := exists_critical_vertex_set H (t - 1) ht
  have hsum := degree_sum_ncard H
  have hXcard : t ≤ X.card := by
    by_contra h
    push_neg at h
    apply hXcol
    have := (H.induce (X : Set W)).colorable_of_fintype
    simp only [Finset.coe_sort_coe, Fintype.card_coe] at this
    exact this.mono (by omega)
  have h1 : ∑ v ∈ X, (t - 1) ≤ ∑ v ∈ X, (H.neighborSet v).ncard :=
    Finset.sum_le_sum (fun v hv => (hXdeg v hv).trans (Set.ncard_le_ncard Set.inter_subset_left))
  have h2 : ∑ v ∈ Xᶜ, 2 ≤ ∑ v ∈ Xᶜ, (H.neighborSet v).ncard :=
    Finset.sum_le_sum (fun v _ => hδ v)
  rw [← Finset.sum_add_sum_compl X] at hsum
  rw [Finset.sum_const, smul_eq_mul] at h1 h2
  rw [Finset.card_compl] at h2
  have hXle : X.card ≤ Fintype.card W := Finset.card_le_univ X
  have hsub := Nat.sub_add_cancel hXle
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 3 := ⟨t - 3, by omega⟩
  rw [show t' + 3 - 1 = t' + 2 by omega] at h1
  rw [show t' + 3 - 3 = t' by omega]
  have h3 : (t' + 3) * t' ≤ X.card * t' := Nat.mul_le_mul_right t' hXcard
  nlinarith
/-! N36 exists_chromatic [leaf, believed provable] deps:  -/
theorem exists_chromatic {W : Type} [Fintype W] (H : SimpleGraph W) (hm : 1 ≤ H.edgeSet.ncard) :
    ∃ t, 2 ≤ t ∧ H.Colorable t ∧ ¬ H.Colorable (t - 1) := by
  classical
  have hex : ∃ n, H.Colorable n := ⟨_, H.colorable_of_fintype⟩
  obtain ⟨e, he⟩ := (Set.ncard_pos (Set.toFinite _)).mp hm
  induction e using Sym2.ind with
  | h a b =>
  have hab : H.Adj a b := he
  have h2 : 2 ≤ Nat.find hex := by
    by_contra hlt
    push_neg at hlt
    obtain ⟨c⟩ := Nat.find_spec hex
    have hn : Nat.find hex = 0 ∨ Nat.find hex = 1 := by omega
    rcases hn with hn | hn
    · rw [hn] at c
      exact (c a).elim0
    · rw [hn] at c
      exact c.valid hab (Subsingleton.elim _ _)
  exact ⟨Nat.find hex, h2, Nat.find_spec hex, Nat.find_min hex (by omega)⟩
/-! N37 choose_ineq [leaf, believed provable] deps:  -/
theorem choose_ineq (n s : ℕ) (hs : 2 ≤ s) (hsn : 2 * s + 1 ≤ n) :
    4 * (n - 2).choose (s - 2) < n.choose s := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 2 := ⟨s - 2, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h1 := Nat.add_one_mul_choose_eq (n' + 1) (s' + 1)
  have h2 := Nat.add_one_mul_choose_eq n' s'
  have hpos : 0 < n'.choose s' := Nat.choose_pos (by omega)
  have hn : 2 * s' + 3 ≤ n' := by omega
  have hc : (n' + 2).choose (s' + 2) * ((s' + 2) * (s' + 1)) = (n' + 2) * (n' + 1) * n'.choose s' := by
    calc (n' + 2).choose (s' + 2) * ((s' + 2) * (s' + 1))
        = ((n' + 2).choose (s' + 2) * (s' + 2)) * (s' + 1) := by ring
      _ = ((n' + 2) * (n' + 1).choose (s' + 1)) * (s' + 1) := by rw [← h1]
      _ = (n' + 2) * ((n' + 1).choose (s' + 1) * (s' + 1)) := by ring
      _ = (n' + 2) * ((n' + 1) * n'.choose s') := by rw [← h2]
      _ = (n' + 2) * (n' + 1) * n'.choose s' := by ring
  by_contra hcon
  push_neg at hcon
  have h3 : (n' + 2).choose (s' + 2) * ((s' + 2) * (s' + 1)) ≤ 4 * n'.choose s' * ((s' + 2) * (s' + 1)) :=
    Nat.mul_le_mul_right _ hcon
  rw [hc] at h3
  have h4 : (n' + 2) * (n' + 1) ≤ 4 * ((s' + 2) * (s' + 1)) := by
    have h5 : (n' + 2) * (n' + 1) * n'.choose s' ≤ 4 * ((s' + 2) * (s' + 1)) * n'.choose s' := by
      calc (n' + 2) * (n' + 1) * n'.choose s' ≤ 4 * n'.choose s' * ((s' + 2) * (s' + 1)) := h3
        _ = 4 * ((s' + 2) * (s' + 1)) * n'.choose s' := by ring
    exact Nat.le_of_mul_le_mul_right h5 hpos
  have h6 : (2 * s' + 5) * (2 * s' + 4) ≤ (n' + 2) * (n' + 1) := Nat.mul_le_mul (by omega) (by omega)
  nlinarith
/-! N38 sum_induced_edges_powersetCard [leaf, believed provable] deps:  -/
theorem sum_induced_edges_powersetCard {W : Type} [Fintype W] (H : SimpleGraph W) (s : ℕ)
    (hs : 2 ≤ s) :
    ∑ T ∈ (Finset.univ : Finset W).powersetCard s, (H.induce (T : Set W)).edgeSet.ncard =
      H.edgeSet.ncard * (Fintype.card W - 2).choose (s - 2) := by
  classical
  have hT : ∀ T : Finset W, (H.induce (T : Set W)).edgeSet.ncard =
      (H.edgeFinset.filter (fun e => ∀ x ∈ e, x ∈ T)).card := by
    intro T
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
    have hmap' : (H.induce (T : Set W)).edgeFinset.card =
        (H.edgeFinset ∩ (T : Set W).toFinset.sym2).card := by
      have hmap := congrArg Finset.card
        (SimpleGraph.map_edgeFinset_induce (G := H) (s := (T : Set W)))
      rw [Finset.card_map] at hmap
      convert hmap
    refine hmap'.trans ?_
    congr 1
    ext e
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_sym2_iff, Set.mem_toFinset,
      Finset.mem_coe]
  simp_rw [hT, Finset.card_filter]
  rw [Finset.sum_comm]
  rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset, Finset.card_eq_sum_ones, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e he
  rw [one_mul]
  simp only [Finset.sum_boole, Nat.cast_id]
  have h2 : e.toFinset.card = 2 := Sym2.card_toFinset_of_not_isDiag e
    (SimpleGraph.not_isDiag_of_mem_edgeSet H (SimpleGraph.mem_edgeFinset.mp he))
  have hc := Finset.card_filter_powersetCard_subset e.toFinset Finset.univ s (Finset.subset_univ _)
    (by omega)
  rw [Finset.card_univ, h2] at hc
  rw [← hc]
  congr 1
  apply Finset.filter_congr
  intro T _
  constructor
  · intro h x hx
    exact h x (Sym2.mem_toFinset.mp hx)
  · intro h x hx
    exact h (Sym2.mem_toFinset.mpr hx)
/-! N39 exists_sparse_half [leaf, believed provable] deps: N37 N38 -/
theorem exists_sparse_half {W : Type} [Fintype W] (H : SimpleGraph W)
    (hn : 3 ≤ Fintype.card W) (hm : 1 ≤ H.edgeSet.ncard) :
    ∃ T : Finset W, T.card = (Fintype.card W + 1) / 2 - 1 ∧
      4 * (H.induce (T : Set W)).edgeSet.ncard < H.edgeSet.ncard := by
  classical
  have hsn : (Fintype.card W + 1) / 2 - 1 ≤ Fintype.card W := by omega
  rcases Nat.lt_or_ge ((Fintype.card W + 1) / 2 - 1) 2 with hs2 | hs2
  · obtain ⟨T, -, hT⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset W)) hsn
    refine ⟨T, hT, ?_⟩
    have hempty : (H.induce (T : Set W)).edgeSet = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro e he
      induction e using Sym2.ind with
      | h a b =>
      have hab : (H.induce (T : Set W)).Adj a b := he
      have hne : (a : W) ≠ b := fun h => hab.ne (Subtype.ext h)
      have hsub : ({(a : W), (b : W)} : Finset W) ⊆ T := by
        intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact a.2
        · exact b.2
      have := Finset.card_le_card hsub
      rw [Finset.card_pair hne] at this
      omega
    rw [hempty, Set.ncard_empty]
    omega
  · have hsn' : 2 * ((Fintype.card W + 1) / 2 - 1) + 1 ≤ Fintype.card W := by omega
    have hchoose := choose_ineq (Fintype.card W) _ hs2 hsn'
    have hsum := sum_induced_edges_powersetCard H _ hs2
    have hlt : ∑ T ∈ (Finset.univ : Finset W).powersetCard ((Fintype.card W + 1) / 2 - 1),
        4 * (H.induce (T : Set W)).edgeSet.ncard <
        ∑ T ∈ (Finset.univ : Finset W).powersetCard ((Fintype.card W + 1) / 2 - 1), H.edgeSet.ncard := by
      rw [← Finset.mul_sum, hsum, Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
        smul_eq_mul]
      calc 4 * (H.edgeSet.ncard * (Fintype.card W - 2).choose ((Fintype.card W + 1) / 2 - 1 - 2))
          = H.edgeSet.ncard * (4 * (Fintype.card W - 2).choose ((Fintype.card W + 1) / 2 - 1 - 2)) := by
            ring
        _ < H.edgeSet.ncard * (Fintype.card W).choose ((Fintype.card W + 1) / 2 - 1) :=
            Nat.mul_lt_mul_of_pos_left hchoose hm
        _ = (Fintype.card W).choose ((Fintype.card W + 1) / 2 - 1) * H.edgeSet.ncard := mul_comm _ _
    obtain ⟨T, hT, hlt'⟩ := Finset.exists_lt_of_sum_lt hlt
    exact ⟨T, (Finset.mem_powersetCard.mp hT).2, hlt'⟩
-- helper (the content of N41, placed here because N40 uses it; N41 below is proved from it)
theorem glue_components_aux {W V : Type} [Fintype W] [Fintype V] (H : SimpleGraph W) (A : Set W)
    (hA : ∀ x y, H.Adj x y → (x ∈ A ↔ y ∈ A)) (C : SimpleGraph V)
    (f : SimpleGraph.Copy (H.induce A) Cᶜ)
    (h2 : (H.induce Aᶜ).IsContained (C.induce (Set.range ⇑f)ᶜ)ᶜ) : H.IsContained Cᶜ := by
  classical
  obtain ⟨g⟩ := h2
  let φ : W → V := fun w => if h : w ∈ A then f ⟨w, h⟩ else (g ⟨w, h⟩ : V)
  have hφA : ∀ w (h : w ∈ A), φ w = f ⟨w, h⟩ := fun w h => by simp only [φ, dif_pos h]
  have hφA' : ∀ w (h : w ∉ A), φ w = (g ⟨w, h⟩ : V) := fun w h => by simp only [φ, dif_neg h]
  have hgnot : ∀ w (h : w ∉ A), (g ⟨w, h⟩ : V) ∉ Set.range ⇑f := fun w h => (g ⟨w, h⟩).2
  refine ⟨⟨⟨φ, fun {a b} hab => ?_⟩, fun a b hab => ?_⟩⟩
  · by_cases ha : a ∈ A
    · have hb : b ∈ A := (hA a b hab).mp ha
      rw [hφA a ha, hφA b hb]
      exact f.toHom.map_adj (show (H.induce A).Adj ⟨a, ha⟩ ⟨b, hb⟩ from hab)
    · have hb : b ∉ A := fun hb => ha ((hA a b hab).mpr hb)
      rw [hφA' a ha, hφA' b hb]
      have := g.toHom.map_adj (show (H.induce Aᶜ).Adj ⟨a, ha⟩ ⟨b, hb⟩ from hab)
      rw [SimpleGraph.compl_adj] at this ⊢
      exact ⟨fun h => this.1 (Subtype.ext h), this.2⟩
  · have hab' : φ a = φ b := hab
    clear hab
    by_cases ha : a ∈ A <;> by_cases hb : b ∈ A
    · rw [hφA a ha, hφA b hb] at hab'
      exact congrArg Subtype.val (f.injective hab')
    · rw [hφA a ha, hφA' b hb] at hab'
      exact absurd ⟨⟨a, ha⟩, hab'⟩ (hgnot b hb)
    · rw [hφA' a ha, hφA b hb] at hab'
      exact absurd ⟨⟨b, hb⟩, hab'.symm⟩ (hgnot a ha)
    · rw [hφA' a ha, hφA' b hb] at hab'
      exact congrArg Subtype.val (g.injective (Subtype.val_injective hab'))
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
  classical
  set A := H.support with hAdef
  have hA : ∀ x y, H.Adj x y → (x ∈ A ↔ y ∈ A) := fun x y hxy =>
    ⟨fun _ => (SimpleGraph.mem_support H).mpr ⟨x, hxy.symm⟩, fun _ => (SimpleGraph.mem_support H).mpr ⟨y, hxy⟩⟩
  have h0A : ∀ v : A, ∃ w, (H.induce A).Adj v w := by
    intro v
    obtain ⟨w, hw⟩ := (SimpleGraph.mem_support H).mp v.2
    exact ⟨⟨w, (hA _ _ hw).mp v.2⟩, hw⟩
  have heA : (H.induce A).edgeSet.ncard = e := by
    rw [← he, ← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset, ← SimpleGraph.coe_edgeFinset,
      Set.ncard_coe_finset]
    exact SimpleGraph.card_edgeFinset_induce_support
  rcases ih e hem A (H.induce A) h0A heA V C hV1 with h | h
  · exact Or.inl h
  · obtain ⟨f⟩ := h
    right
    apply glue_components_aux H A hA C f
    have hbot : H.induce Aᶜ ≤ ⊥ := by
      intro x y hxy
      exact absurd ((SimpleGraph.mem_support H).mpr ⟨y.val, hxy⟩) x.2
    refine SimpleGraph.IsContained.mono_left hbot ?_
    have hrange : Fintype.card (Set.range ⇑f) = Fintype.card A :=
      Set.card_range_of_injective f.injective
    have hcompl : Fintype.card ↥(Set.range ⇑f)ᶜ = Fintype.card V - Fintype.card (Set.range ⇑f) :=
      Fintype.card_compl_set _
    have hcomplA : Fintype.card ↥Aᶜ = Fintype.card W - Fintype.card A := Fintype.card_compl_set _
    rw [SimpleGraph.bot_isContained_iff_card_le, hcomplA, hcompl, hrange]
    omega
/-! N41 glue_components [leaf, believed provable] deps:  -/
theorem glue_components {W V : Type} [Fintype W] [Fintype V] (H : SimpleGraph W) (A : Set W)
    (hA : ∀ x y, H.Adj x y → (x ∈ A ↔ y ∈ A)) (C : SimpleGraph V)
    (f : SimpleGraph.Copy (H.induce A) Cᶜ)
    (h2 : (H.induce Aᶜ).IsContained (C.induce (Set.range ⇑f)ᶜ)ᶜ) : H.IsContained Cᶜ := by
  exact glue_components_aux H A hA C f h2

/-! N42 split_of_not_connected [leaf, believed provable] deps:  -/
theorem split_of_not_connected {W : Type} [Fintype W] [Nonempty W] (H : SimpleGraph W)
    (hc : ¬ H.Connected) :
    ∃ A : Set W, A.Nonempty ∧ Aᶜ.Nonempty ∧ ∀ x y, H.Adj x y → (x ∈ A ↔ y ∈ A) := by
  obtain ⟨v⟩ := ‹Nonempty W›
  refine ⟨{w | H.Reachable v w}, ⟨v, SimpleGraph.Reachable.refl v⟩, ?_, ?_⟩
  · by_contra hA
    rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at hA
    apply hc
    refine ⟨fun x y => ?_⟩
    have hx : H.Reachable v x := Set.eq_univ_iff_forall.mp hA x
    have hy : H.Reachable v y := Set.eq_univ_iff_forall.mp hA y
    exact hx.symm.trans hy
  · intro x y hxy
    exact ⟨fun hx => hx.trans hxy.reachable, fun hy => hy.trans hxy.symm.reachable⟩
/-! N43 edge_split_of_closed [leaf, believed provable] deps:  -/
theorem edge_split_of_closed {W : Type} [Fintype W] (H : SimpleGraph W) (A : Set W)
    (hA : ∀ x y, H.Adj x y → (x ∈ A ↔ y ∈ A)) :
    (H.induce A).edgeSet.ncard + (H.induce Aᶜ).edgeSet.ncard = H.edgeSet.ncard := by
  classical
  have hinj1 : Function.Injective (Sym2.map (Subtype.val : A → W)) :=
    Sym2.map.injective Subtype.val_injective
  have hinj2 : Function.Injective (Sym2.map (Subtype.val : ↥Aᶜ → W)) :=
    Sym2.map.injective Subtype.val_injective
  have hunion : H.edgeSet = Sym2.map Subtype.val '' (H.induce A).edgeSet ∪
      Sym2.map Subtype.val '' (H.induce Aᶜ).edgeSet := by
    ext e
    induction e using Sym2.ind with
    | h x y =>
    simp only [SimpleGraph.mem_edgeSet, Set.mem_union, Set.mem_image]
    constructor
    · intro hxy
      by_cases hx : x ∈ A
      · left
        exact ⟨s(⟨x, hx⟩, ⟨y, (hA x y hxy).mp hx⟩), hxy, rfl⟩
      · right
        exact ⟨s(⟨x, hx⟩, ⟨y, fun hy => hx ((hA x y hxy).mpr hy)⟩), hxy, rfl⟩
    · rintro (⟨e', he', hee'⟩ | ⟨e', he', hee'⟩)
      · induction e' using Sym2.ind with
        | h a b =>
        rw [Sym2.map_mk, Sym2.eq_iff] at hee'
        rcases hee' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact he'
        · exact he'.symm
      · induction e' using Sym2.ind with
        | h a b =>
        rw [Sym2.map_mk, Sym2.eq_iff] at hee'
        rcases hee' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact he'
        · exact he'.symm
  have hdisj : Disjoint (Sym2.map Subtype.val '' (H.induce A).edgeSet)
      (Sym2.map Subtype.val '' (H.induce Aᶜ).edgeSet) := by
    rw [Set.disjoint_left]
    rintro e ⟨e1, _, rfl⟩ ⟨e2, _, h12⟩
    induction e1 using Sym2.ind with
    | h a b =>
    induction e2 using Sym2.ind with
    | h c d =>
    rw [Sym2.map_mk, Sym2.map_mk, Sym2.eq_iff] at h12
    rcases h12 with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact c.2 (h1 ▸ a.2)
    · exact c.2 (h1 ▸ b.2)
  rw [hunion, Set.ncard_union_eq hdisj, Set.ncard_image_of_injective _ hinj1,
    Set.ncard_image_of_injective _ hinj2]
/-! N44 induce_no_isolated_of_closed [leaf, believed provable] deps:  -/
theorem induce_no_isolated_of_closed {W : Type} (H : SimpleGraph W) (h0 : ∀ v, ∃ w, H.Adj v w)
    (A : Set W) (hA : ∀ x y, H.Adj x y → (x ∈ A ↔ y ∈ A)) :
    ∀ v : A, ∃ w, (H.induce A).Adj v w := by
  intro v
  obtain ⟨w, hw⟩ := h0 v.val
  exact ⟨⟨w, (hA _ _ hw).mp v.2⟩, hw⟩
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
  classical
  obtain ⟨A, hAne, hAcne, hA⟩ := split_of_not_connected H hc
  have h0A := induce_no_isolated_of_closed H h0 A hA
  have hAc : ∀ x y, H.Adj x y → (x ∈ Aᶜ ↔ y ∈ Aᶜ) := fun x y hxy => by
    simp only [Set.mem_compl_iff]
    exact not_congr (hA x y hxy)
  have h0Ac := induce_no_isolated_of_closed H h0 Aᶜ hAc
  have hsplit := edge_split_of_closed H A hA
  set m1 := (H.induce A).edgeSet.ncard with hm1
  set m2 := (H.induce Aᶜ).edgeSet.ncard with hm2
  have hcardA : Fintype.card A ≤ 2 * m1 := card_le_two_mul_ncard _ h0A
  have hcardAc : Fintype.card ↥Aᶜ ≤ 2 * m2 := card_le_two_mul_ncard _ h0Ac
  have hApos : 1 ≤ Fintype.card A := Fintype.card_pos_iff.mpr hAne.to_subtype
  have hAcpos : 1 ≤ Fintype.card ↥Aᶜ := Fintype.card_pos_iff.mpr hAcne.to_subtype
  have hm1lt : m1 < m := by omega
  have hm2lt : m2 < m := by omega
  rcases ih m1 hm1lt A (H.induce A) h0A rfl V C
    (by have := Nat.mul_le_mul_left (k - 1) hm1lt.le; omega) with h | h
  · exact Or.inl h
  · obtain ⟨f⟩ := h
    have hrange : Fintype.card (Set.range ⇑f) = Fintype.card A :=
      Set.card_range_of_injective f.injective
    have hcompl : Fintype.card ↥(Set.range ⇑f)ᶜ = Fintype.card V - Fintype.card (Set.range ⇑f) :=
      Fintype.card_compl_set _
    have hk1 : 2 ≤ k - 1 := by omega
    have hV' : (k - 1) * m2 + 1 ≤ Fintype.card ↥(Set.range ⇑f)ᶜ := by
      rw [hcompl, hrange]
      have h1 : (k - 1) * m = (k - 1) * m1 + (k - 1) * m2 := by rw [← hm, ← hsplit]; ring
      have h2 : 2 * m1 ≤ (k - 1) * m1 := Nat.mul_le_mul_right m1 hk1
      omega
    rcases ih m2 hm2lt ↥Aᶜ (H.induce Aᶜ) h0Ac rfl ↥(Set.range ⇑f)ᶜ (C.induce (Set.range ⇑f)ᶜ) hV'
      with h2 | h2
    · exact Or.inl (isContained_of_induce _ h2)
    · exact Or.inr (glue_components H A hA C f h2)
/-! N46 extend_by_vertex [leaf, believed provable] deps:  -/
theorem extend_by_vertex {W V : Type} (H : SimpleGraph W) (u : W) (D : SimpleGraph V)
    (f : SimpleGraph.Copy (H.induce ({u}ᶜ : Set W)) D) (x : V) (hx : x ∉ Set.range ⇑f)
    (hadj : ∀ w : ({u}ᶜ : Set W), H.Adj u w → D.Adj x (f w)) : H.IsContained D := by
  classical
  let φ : W → V := fun w => if h : w = u then x else f ⟨w, Set.mem_compl_singleton_iff.mpr h⟩
  have hφu : φ u = x := by simp only [φ, dif_pos rfl]
  have hφ : ∀ w (h : w ≠ u), φ w = f ⟨w, Set.mem_compl_singleton_iff.mpr h⟩ :=
    fun w h => by simp only [φ, dif_neg h]
  refine ⟨⟨⟨φ, fun {a b} hab => ?_⟩, fun a b hab => ?_⟩⟩
  · by_cases ha : a = u
    · have hb : b ≠ u := fun hb => hab.ne (ha.trans hb.symm)
      rw [ha, hφu, hφ b hb]
      exact hadj ⟨b, Set.mem_compl_singleton_iff.mpr hb⟩ (ha ▸ hab)
    · by_cases hb : b = u
      · rw [hb, hφu, hφ a ha]
        exact (hadj ⟨a, Set.mem_compl_singleton_iff.mpr ha⟩ (hb ▸ hab.symm)).symm
      · rw [hφ a ha, hφ b hb]
        exact f.toHom.map_adj (show (H.induce _).Adj ⟨a, Set.mem_compl_singleton_iff.mpr ha⟩
          ⟨b, Set.mem_compl_singleton_iff.mpr hb⟩ from hab)
  · have hab' : φ a = φ b := hab
    clear hab
    by_cases ha : a = u <;> by_cases hb : b = u
    · exact ha.trans hb.symm
    · rw [ha, hφu, hφ b hb] at hab'
      exact absurd ⟨⟨b, Set.mem_compl_singleton_iff.mpr hb⟩, hab'.symm⟩ hx
    · rw [hb, hφu, hφ a ha] at hab'
      exact absurd ⟨⟨a, Set.mem_compl_singleton_iff.mpr ha⟩, hab'⟩ hx
    · rw [hφ a ha, hφ b hb] at hab'
      exact congrArg Subtype.val (f.injective hab')
/-! N47 delete_vertex_edges [leaf, believed provable] deps:  -/
theorem delete_vertex_edges {W : Type} [Fintype W] (H : SimpleGraph W) (u : W) :
    (H.induce ({u}ᶜ : Set W)).edgeSet.ncard + (H.neighborSet u).ncard = H.edgeSet.ncard := by
  classical
  have h1 := SimpleGraph.card_edgeFinset_induce_compl_singleton H u
  have h2 := SimpleGraph.card_edgeFinset_deleteIncidenceSet H u
  have h3 : H.degree u ≤ H.edgeFinset.card := SimpleGraph.degree_le_card_edgeFinset H u
  rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset, ← SimpleGraph.coe_edgeFinset,
    Set.ncard_coe_finset, Set.ncard_eq_toFinset_card', Set.toFinset_card,
    SimpleGraph.card_neighborSet_eq_degree]
  omega
/-! N48 delete_min_vertex_no_isolated [leaf, believed provable] deps:  -/
theorem delete_min_vertex_no_isolated {W : Type} [Fintype W] (H : SimpleGraph W)
    (hc : H.Connected) (hm : 2 ≤ H.edgeSet.ncard) (u : W)
    (hu : ∀ w, (H.neighborSet u).ncard ≤ (H.neighborSet w).ncard) :
    ∀ v : ({u}ᶜ : Set W), ∃ w, (H.induce ({u}ᶜ : Set W)).Adj v w := by
  classical
  intro v
  have hvu : (v : W) ≠ u := Set.mem_compl_singleton_iff.mp v.2
  by_contra hcon
  push_neg at hcon
  -- every neighbor of v is u
  have hNv : ∀ w, H.Adj v w → w = u := by
    intro w hw
    by_contra hwu
    exact hcon ⟨w, Set.mem_compl_singleton_iff.mpr hwu⟩ hw
  obtain ⟨w0, hw0⟩ := (hc.preconnected v u).nonempty_neighborSet_left hvu
  have hw0u : w0 = u := hNv w0 hw0
  have hvu' : H.Adj v u := hw0u ▸ hw0
  have hNvle : (H.neighborSet v).ncard ≤ 1 := by
    have hsub : H.neighborSet v ⊆ {u} := fun w hw => hNv w hw
    calc (H.neighborSet v).ncard ≤ ({u} : Set W).ncard := Set.ncard_le_ncard hsub
      _ = 1 := Set.ncard_singleton u
  have hNule : (H.neighborSet u).ncard ≤ 1 := (hu v).trans hNvle
  have hNu : ∀ w, H.Adj u w → w = v :=
    fun w hw => (Set.ncard_le_one_iff (Set.toFinite _)).mp hNule hw hvu'.symm
  -- {u, v} is closed under walks
  have hclosed : ∀ (a x : W) (p : H.Walk a x), (a = u ∨ a = v) → (x = u ∨ x = v) := by
    intro a x p
    induction p with
    | nil => exact id
    | cons h p ih =>
      intro ha
      apply ih
      rcases ha with rfl | rfl
      · exact Or.inr (hNu _ h)
      · exact Or.inl (hNv _ h)
  have hall : ∀ x : W, x = u ∨ x = v := by
    intro x
    obtain ⟨p⟩ := hc.preconnected u x
    exact hclosed u x p (Or.inl rfl)
  -- then all edges equal s(u, v)
  have hsub : H.edgeSet ⊆ {s(u, (v : W))} := by
    intro e he
    induction e using Sym2.ind with
    | h a b =>
    have hab : H.Adj a b := he
    rw [Set.mem_singleton_iff, Sym2.eq_iff]
    rcases hall a with rfl | rfl <;> rcases hall b with rfl | rfl
    · exact absurd hab (H.irrefl)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact absurd hab (H.irrefl)
  have := Set.ncard_le_ncard hsub
  rw [Set.ncard_singleton] at this
  omega
/-! N49 red_star_pigeonhole [leaf, believed provable] deps:  -/
theorem red_star_pigeonhole {V : Type} (C : SimpleGraph V) (T X : Finset V) (hT : T.Nonempty)
    (hX : ∀ x ∈ X, ∃ t ∈ T, C.Adj t x) :
    ∃ v ∈ T, ∃ S : Finset V, S ⊆ X ∧ (∀ s ∈ S, C.Adj v s) ∧ X.card ≤ T.card * S.card := by
  classical
  obtain ⟨t0, ht0⟩ := hT
  let g : V → V := fun x => if h : x ∈ X then Classical.choose (hX x h) else t0
  have hg : ∀ x ∈ X, g x ∈ T ∧ C.Adj (g x) x := by
    intro x hx
    simp only [g, dif_pos hx]
    exact Classical.choose_spec (hX x hx)
  have hsum : X.card = ∑ t ∈ T, (X.filter (fun x => g x = t)).card :=
    Finset.card_eq_sum_card_fiberwise (fun x hx => (hg x hx).1)
  have hex : ∃ t ∈ T, X.card ≤ T.card * (X.filter (fun x => g x = t)).card := by
    apply Finset.exists_le_of_sum_le ⟨t0, ht0⟩
    rw [← Finset.mul_sum, ← hsum, Finset.sum_const, smul_eq_mul]
  obtain ⟨v, hv, hcard⟩ := hex
  refine ⟨v, hv, X.filter (fun x => g x = v), Finset.filter_subset _ _, ?_, hcard⟩
  intro s hs
  rw [Finset.mem_filter] at hs
  rw [← hs.2]
  exact (hg s hs.1).2
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
  classical
  have hne : Nonempty W := hc.nonempty
  have hdel := delete_vertex_edges H u
  rw [hm] at hdel
  have hd1 : 1 ≤ (H.neighborSet u).ncard := by
    obtain ⟨e, he⟩ := (Set.ncard_pos (Set.toFinite _)).mp (by omega : 0 < H.edgeSet.ncard)
    induction e using Sym2.ind with
    | h a b =>
    have hab : H.Adj a b := he
    have hex : (H.neighborSet u).Nonempty := by
      by_cases hua : u = a
      · exact ⟨b, hua ▸ hab⟩
      · exact (hc.preconnected u a).nonempty_neighborSet_left hua
    exact Nat.one_le_iff_ne_zero.mpr ((Set.ncard_pos (Set.toFinite _)).mpr hex).ne'
  have h0' := delete_min_vertex_no_isolated H hc (by omega) u hu
  have hm' : (H.induce ({u}ᶜ : Set W)).edgeSet.ncard < m := by omega
  rcases ih _ hm' _ (H.induce ({u}ᶜ : Set W)) h0' rfl V C
    (by have := Nat.mul_le_mul_left (k - 1) hm'.le; omega) with h | h
  · exact absurd h hcyc
  obtain ⟨f⟩ := h
  let g : H.neighborSet u → V := fun w => f ⟨w.1, Set.mem_compl_singleton_iff.mpr w.2.ne.symm⟩
  set T : Finset V := Finset.univ.image g with hT
  set X : Finset V := Finset.univ.filter (fun x => x ∉ Set.range ⇑f) with hX
  have hTcard : T.card ≤ (H.neighborSet u).ncard := by
    calc T.card ≤ (Finset.univ : Finset (H.neighborSet u)).card := Finset.card_image_le
      _ = Fintype.card (H.neighborSet u) := Finset.card_univ
      _ = (H.neighborSet u).ncard := by rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
  have hTne : T.Nonempty := by
    obtain ⟨w, hw⟩ := (Set.ncard_pos (Set.toFinite _)).mp (by omega : 0 < (H.neighborSet u).ncard)
    exact ⟨g ⟨w, hw⟩, Finset.mem_image_of_mem g (Finset.mem_univ _)⟩
  have hXadj : ∀ x ∈ X, ∃ t ∈ T, C.Adj t x := by
    intro x hx
    have hx' : x ∉ Set.range ⇑f := (Finset.mem_filter.mp hx).2
    by_contra hcon
    push_neg at hcon
    apply hH
    apply extend_by_vertex H u Cᶜ f x hx'
    intro w hw
    rw [SimpleGraph.compl_adj]
    refine ⟨fun h => hx' ⟨w, h.symm⟩, fun h => ?_⟩
    have hfw : f w ∈ T := by
      have : g ⟨w.1, hw⟩ = f w := rfl
      rw [← this]
      exact Finset.mem_image_of_mem g (Finset.mem_univ _)
    exact hcon (f w) hfw h.symm
  obtain ⟨v, hvT, S, hSX, hSadj, hcard⟩ := red_star_pigeonhole C T X hTne hXadj
  refine ⟨v, S, ?_, hSadj, ?_⟩
  · intro hvS
    have hvX := hSX hvS
    have hv' : v ∉ Set.range ⇑f := (Finset.mem_filter.mp hvX).2
    rw [Finset.mem_image] at hvT
    obtain ⟨w, _, rfl⟩ := hvT
    exact hv' ⟨_, rfl⟩
  · have hXcard : X.card = Fintype.card V - (Fintype.card W - 1) := by
      have h1 : X.card = Fintype.card {x : V // ¬ x ∈ Set.range ⇑f} := (Fintype.card_subtype _).symm
      have h2 : Fintype.card {x : V // ¬ x ∈ Set.range ⇑f} =
          Fintype.card V - Fintype.card {x : V // x ∈ Set.range ⇑f} := Fintype.card_subtype_compl _
      have h3 : Fintype.card {x : V // x ∈ Set.range ⇑f} = Fintype.card ({u}ᶜ : Set W) :=
        Set.card_range_of_injective f.injective
      have h4 : Fintype.card ({u}ᶜ : Set W) = Fintype.card W - Fintype.card ({u} : Set W) :=
        Fintype.card_compl_set _
      rw [h1, h2, h3, h4, Set.card_singleton]
    have h5 : T.card * S.card ≤ (H.neighborSet u).ncard * S.card := Nat.mul_le_mul_right _ hTcard
    have h6 : 1 ≤ Fintype.card W := Fintype.card_pos
    omega
/-! N51 step_min_degree_one [leaf, believed provable] deps: N21 N13 N05 N08 -/
theorem step_min_degree_one (k : ℕ) (hk : 3 ≤ k) {W : Type} [Fintype W] (H : SimpleGraph W)
    (hc : H.Connected) (m : ℕ) (hm : H.edgeSet.ncard = m) {V : Type} (C : SimpleGraph V) (v : V)
    (S : Finset V) (hvS : v ∉ S) (hS : ∀ s ∈ S, C.Adj v s)
    (hsize : (k - 1) * m + 2 ≤ 1 * S.card + Fintype.card W) :
    (SimpleGraph.cycleGraph k).IsContained C ∨ H.IsContained Cᶜ := by
  classical
  have hn := connected_card_le_ncard_add_one H hc
  rw [hm] at hn
  have hcard : (k - 1 - 1) * (Fintype.card W - 1) + 1 ≤ Fintype.card (S : Set V) := by
    simp only [Finset.coe_sort_coe, Fintype.card_coe]
    have h1 : (k - 1 - 1) * (Fintype.card W - 1) ≤ (k - 2) * m := Nat.mul_le_mul (by omega) (by omega)
    have h2 : (k - 1) * m = (k - 2) * m + m := by
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 3 := ⟨k - 3, by omega⟩
      rw [show k' + 3 - 1 = k' + 2 by omega, show k' + 3 - 2 = k' + 1 by omega]
      ring
    omega
  rcases cor6_path_ramsey (k - 1) (by omega) H (S : Set V) (C.induce (S : Set V)) hcard with h | h
  · exact Or.inl (cycle_of_path_in_nbhd C k hk v (S : Set V) hS hvS h)
  · exact Or.inr (isContained_compl_of_compl_induce _ h)
/-! N52 S_size_bound [leaf, believed provable] deps:  -/
theorem S_size_bound (k n m d s : ℕ) (hk : 3 ≤ k) (hd : 2 ≤ d) (hnd : n * d ≤ 2 * m)
    (hs : (k - 1) * m + 2 ≤ d * s + n) : (k - 2) * (n / 2) + 1 ≤ s := by
  by_contra hcon
  push_neg at hcon
  have h1 : s ≤ (k - 2) * (n / 2) := by omega
  have h2 : d * (n / 2) ≤ m := by
    have := Nat.mul_le_mul_left d (Nat.div_mul_le_self n 2)
    nlinarith
  have h3 : d * s ≤ (k - 2) * m := by
    calc d * s ≤ d * ((k - 2) * (n / 2)) := Nat.mul_le_mul_left d h1
      _ = (k - 2) * (d * (n / 2)) := by ring
      _ ≤ (k - 2) * m := Nat.mul_le_mul_left _ h2
  have h4 : n ≤ m := by
    have := Nat.mul_le_mul_left n hd
    nlinarith
  have h5 : (k - 1) * m = (k - 2) * m + m := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 3 := ⟨k - 3, by omega⟩
    rw [show k' + 3 - 1 = k' + 2 by omega, show k' + 3 - 2 = k' + 1 by omega]
    ring
  omega
/-! N53 blue_clique_in_S [leaf, believed provable] deps: N21 -/
theorem blue_clique_in_S (k q : ℕ) (hk : 3 ≤ k) {V : Type} (C : SimpleGraph V) (S : Finset V)
    (hS : (k - 2) * q + 1 ≤ S.card) :
    (SimpleGraph.pathGraph (k - 1)).IsContained (C.induce (S : Set V)) ∨
      ∃ U : Finset V, U ⊆ S ∧ U.card = q + 1 ∧ ∀ x ∈ U, ∀ y ∈ U, x ≠ y → Cᶜ.Adj x y := by
  classical
  have hk' : 2 ≤ k - 1 := by omega
  have hcard : (k - 1 - 1) * (Fintype.card (Fin (q + 1)) - 1) + 1 ≤ Fintype.card (S : Set V) := by
    simp only [Fintype.card_fin, Nat.add_sub_cancel, Finset.coe_sort_coe, Fintype.card_coe]
    rw [show k - 1 - 1 = k - 2 by omega]
    exact hS
  rcases cor6_path_ramsey (k - 1) hk' (⊤ : SimpleGraph (Fin (q + 1))) (S : Set V)
    (C.induce (S : Set V)) hcard with h | h
  · exact Or.inl h
  · right
    obtain ⟨g⟩ := h
    have hinj : Function.Injective (fun i : Fin (q + 1) => (g i : V)) :=
      fun i j h => g.injective (Subtype.val_injective h)
    refine ⟨Finset.univ.image (fun i => (g i : V)), ?_, ?_, ?_⟩
    · intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨i, _, rfl⟩ := hx
      exact (g i).2
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    · intro x hx y hy hxy
      rw [Finset.mem_image] at hx hy
      obtain ⟨i, _, rfl⟩ := hx
      obtain ⟨j, _, rfl⟩ := hy
      have hij : i ≠ j := fun h => hxy (by rw [h])
      have := g.toHom.map_adj ((SimpleGraph.top_adj i j).mpr hij)
      rw [SimpleGraph.compl_adj] at this ⊢
      exact ⟨fun h => this.1 (Subtype.ext h), this.2⟩
/-! N54 gamma_bound [leaf, believed provable] deps: N33 N20 N05 -/
theorem gamma_bound (k : ℕ) (hk : 7 ≤ k) {W : Type} [Fintype W] (H : SimpleGraph W) (t : ℕ)
    (c : H.Coloring (Fin t)) {V : Type} (C : SimpleGraph V) (v : V) (U Gam : Finset V)
    (hU : ∀ x ∈ U, C.Adj v x) (hGam : ∀ y ∈ Gam, ∃ x ∈ U, C.Adj x y) (hdisj : Disjoint U Gam)
    (hvG : v ∉ Gam) (hfree : ¬ (SimpleGraph.cycleGraph k).IsContained C)
    (hH : ¬ H.IsContained Cᶜ) :
    Gam.card + 1 ≤ Fintype.card W + (k - 1) * (t - 1) := by
  classical
  by_contra hcon
  push_neg at hcon
  have hcard : Fintype.card W + (k + 1 - 2) * (t - 1) ≤ Fintype.card (Gam : Set V) := by
    simp only [Finset.coe_sort_coe, Fintype.card_coe]
    rw [show k + 1 - 2 = k - 1 by omega]
    omega
  rcases lemma5_path_coloring (k + 1) (by omega) H t c (Gam : Set V) (C.induce (Gam : Set V)) hcard
    with h | h
  · exact hfree (lemma7_bridge k hk C v (U : Set V) (Gam : Set V) hU hGam
      (Finset.disjoint_coe.mpr hdisj) hvG h)
  · exact hH (isContained_compl_of_compl_induce _ h)
/-! N55 glue_clique_sparse [leaf, believed provable] deps:  -/
theorem glue_clique_sparse {W V : Type} [Fintype W] (H : SimpleGraph W) (T : Finset W)
    (C : SimpleGraph V) (U1 U2 : Finset V) (hdisj : Disjoint U1 U2)
    (hcard : Fintype.card W - T.card ≤ U1.card)
    (hclique : ∀ x ∈ U1, ∀ y ∈ U1, x ≠ y → Cᶜ.Adj x y)
    (hcross : ∀ x ∈ U1, ∀ y ∈ U2, Cᶜ.Adj x y)
    (h2 : (H.induce (T : Set W)).IsContained (C.induce (U2 : Set V))ᶜ) : H.IsContained Cᶜ := by
  classical
  obtain ⟨g⟩ := h2
  have hemb : Nonempty ({w // w ∉ T} ↪ U1) := by
    apply Function.Embedding.nonempty_of_card_le
    rw [Fintype.card_coe]
    refine le_trans (le_of_eq ?_) hcard
    rw [Fintype.card_subtype_compl, Fintype.card_coe]
  let e := hemb.some
  let φ : W → V := fun w => if h : w ∈ T then (g ⟨w, h⟩ : V) else (e ⟨w, h⟩ : V)
  have hφT : ∀ w (h : w ∈ T), φ w = (g ⟨w, h⟩ : V) := fun w h => by simp only [φ, dif_pos h]
  have hφT' : ∀ w (h : w ∉ T), φ w = (e ⟨w, h⟩ : V) := fun w h => by simp only [φ, dif_neg h]
  have hgU2 : ∀ w (h : w ∈ T), (g ⟨w, h⟩ : V) ∈ U2 := fun w h => (g ⟨w, h⟩).2
  have heU1 : ∀ w (h : w ∉ T), (e ⟨w, h⟩ : V) ∈ U1 := fun w h => (e ⟨w, h⟩).2
  refine ⟨⟨⟨φ, fun {a b} hab => ?_⟩, fun a b hab => ?_⟩⟩
  · by_cases ha : a ∈ T <;> by_cases hb : b ∈ T
    · rw [hφT a ha, hφT b hb]
      have := g.toHom.map_adj (show (H.induce (T : Set W)).Adj ⟨a, ha⟩ ⟨b, hb⟩ from hab)
      rw [SimpleGraph.compl_adj] at this ⊢
      exact ⟨fun h => this.1 (Subtype.ext h), this.2⟩
    · rw [hφT a ha, hφT' b hb]
      exact (hcross _ (heU1 b hb) _ (hgU2 a ha)).symm
    · rw [hφT' a ha, hφT b hb]
      exact hcross _ (heU1 a ha) _ (hgU2 b hb)
    · rw [hφT' a ha, hφT' b hb]
      apply hclique _ (heU1 a ha) _ (heU1 b hb)
      intro h
      exact hab.ne (congrArg Subtype.val (e.injective (Subtype.val_injective h)))
  · have hab' : φ a = φ b := hab
    clear hab
    by_cases ha : a ∈ T <;> by_cases hb : b ∈ T
    · rw [hφT a ha, hφT b hb] at hab'
      exact congrArg Subtype.val (g.injective (Subtype.val_injective hab'))
    · rw [hφT a ha, hφT' b hb] at hab'
      have h1 : (e ⟨b, hb⟩ : V) ∈ U2 := by rw [← hab']; exact hgU2 a ha
      exact absurd h1 (Finset.disjoint_left.mp hdisj (heU1 b hb))
    · rw [hφT' a ha, hφT b hb] at hab'
      have h1 : (e ⟨a, ha⟩ : V) ∈ U2 := by rw [hab']; exact hgU2 b hb
      exact absurd h1 (Finset.disjoint_left.mp hdisj (heU1 a ha))
    · rw [hφT' a ha, hφT' b hb] at hab'
      exact congrArg Subtype.val (e.injective (Subtype.val_injective hab'))
/-! N56 final_arith [leaf, believed provable] deps:  -/
theorem final_arith (k n m t g u2 e2 h2 : ℕ) (hk : 7 ≤ k) (hn : 4 ≤ n) (hmn : n ≤ m) (ht : 2 ≤ t)
    (hprop : 2 * n + t * (t - 3) ≤ 2 * m)
    (htot : (k - 1) * m + 1 ≤ 1 + (n / 2 + 1) + g + u2)
    (hg : g + 1 ≤ n + (k - 1) * (t - 1)) (hu2 : u2 ≤ (k - 1) * e2 ∨ u2 < h2)
    (he2 : 4 * e2 < m) (hh2 : 2 * h2 ≤ n) : False := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 7 := ⟨k - 7, by omega⟩
  obtain ⟨q, hq⟩ : ∃ q, q = n / 2 := ⟨_, rfl⟩
  have hq1 : 2 * q ≤ n := by omega
  have hq2 : n ≤ 2 * q + 1 := by omega
  rw [← hq] at htot
  rw [show k' + 7 - 1 = k' + 6 by omega] at htot hg hu2
  have hA : (k' + 6) * (4 * e2 + 1) ≤ (k' + 6) * m := Nat.mul_le_mul_left _ (by omega)
  by_cases ht3 : t ≤ 3
  · have h0 : t - 3 = 0 := by omega
    have h1 : t - 1 ≤ 2 := by omega
    rw [h0, mul_zero, add_zero] at hprop
    have hg' : g + 1 ≤ n + (k' + 6) * 2 :=
      hg.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ h1) _)
    have hD : k' * 7 ≤ k' * (3 * m) := Nat.mul_le_mul_left _ (by omega)
    have hE : k' * 2 ≤ k' * m := Nat.mul_le_mul_left _ (by omega)
    rcases hu2 with hu2 | hu2
    · nlinarith
    · nlinarith
  · obtain ⟨t'', rfl⟩ : ∃ t'', t = t'' + 4 := ⟨t - 4, by omega⟩
    rw [show t'' + 4 - 3 = t'' + 1 by omega] at hprop
    rw [show t'' + 4 - 1 = t'' + 3 by omega] at hg
    have ht : 4 * t'' + 11 ≤ 3 * m := by nlinarith
    have hB : k' * (4 * t'' + 11) ≤ k' * (3 * m) := Nat.mul_le_mul_left _ ht
    have ht2 : t'' + 3 ≤ m := by nlinarith
    have hC : k' * (t'' + 3) ≤ k' * m := Nat.mul_le_mul_left _ ht2
    rcases hu2 with hu2 | hu2
    · nlinarith
    · nlinarith
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
  classical
  have hk3 : 3 ≤ k := by omega
  by_contra hcon
  have hcyc : ¬ (SimpleGraph.cycleGraph k).IsContained C := fun h => hcon (Or.inl h)
  have hH : ¬ H.IsContained Cᶜ := fun h => hcon (Or.inr h)
  have hnm : Fintype.card W ≤ m := by
    have h1 : ∑ _w : W, 2 ≤ ∑ w, (H.neighborSet w).ncard := Finset.sum_le_sum (fun w _ => hδ w)
    rw [degree_sum_ncard H, hm, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h1
    omega
  have hne : Nonempty W := hc.nonempty
  have hn3 : 3 ≤ Fintype.card W := by
    obtain ⟨w⟩ := hne
    have h2 := hδ w
    have hss : H.neighborSet w ⊂ Set.univ := by
      rw [Set.ssubset_univ_iff]
      intro h
      have : w ∈ H.neighborSet w := h ▸ Set.mem_univ w
      exact H.irrefl this
    have := Set.ncard_lt_ncard hss (Set.toFinite _)
    rw [Set.ncard_univ, Nat.card_eq_fintype_card] at this
    omega
  rcases Nat.lt_or_ge (Fintype.card W) 4 with hn4 | hn4
  · have h3 : Fintype.card W = 3 := by omega
    have hV' : 2 * k + 1 ≤ Fintype.card V := by
      have := Nat.mul_le_mul_left (k - 1) (show 3 ≤ m by omega)
      omega
    exact hcon (step_triangle k hk3 H h3 V C hV')
  · have hm1 : 1 ≤ H.edgeSet.ncard := by omega
    obtain ⟨t, ht2, ⟨c⟩, hnot⟩ := exists_chromatic H hm1
    have hprop := prop10 H hδ t hnot
    rw [hm] at hprop
    rcases blue_clique_in_S k (Fintype.card W / 2) hk3 C S hsize with hpath | ⟨U1, hU1S, hU1card, hU1clique⟩
    · exact hcyc (cycle_of_path_in_nbhd C k hk3 v (S : Set V) hS hvS hpath)
    set Gam := (Finset.univ.filter (fun y => y ∉ U1 ∧ y ≠ v ∧ ∃ x ∈ U1, C.Adj x y)) with hGam
    set U2 := (Finset.univ.filter (fun y => y ∉ U1 ∧ y ≠ v ∧ ∀ x ∈ U1, ¬ C.Adj x y)) with hU2
    have hU1v : ∀ x ∈ U1, C.Adj v x := fun x hx => hS x (hU1S hx)
    have hGamprop : ∀ y ∈ Gam, ∃ x ∈ U1, C.Adj x y := fun y hy => (Finset.mem_filter.mp hy).2.2.2
    have hdisjG : Disjoint U1 Gam := by
      rw [Finset.disjoint_left]
      intro x hx hxG
      exact (Finset.mem_filter.mp hxG).2.1 hx
    have hvG : v ∉ Gam := fun h => (Finset.mem_filter.mp h).2.2.1 rfl
    have hg := gamma_bound k hk H t c C v U1 Gam hU1v hGamprop hdisjG hvG hcyc hH
    have hcover : ∀ y : V, y ∈ ({v} ∪ U1 ∪ Gam ∪ U2 : Finset V) := by
      intro y
      by_cases hy1 : y = v
      · simp [hy1]
      by_cases hy2 : y ∈ U1
      · simp [hy2]
      by_cases hy3 : ∃ x ∈ U1, C.Adj x y
      · have : y ∈ Gam := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy2, hy1, hy3⟩
        simp [this]
      · push_neg at hy3
        have : y ∈ U2 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy2, hy1, hy3⟩
        simp [this]
    have htot : Fintype.card V ≤ 1 + U1.card + Gam.card + U2.card := by
      have h4 := Finset.card_le_card (fun y _ => hcover y : (Finset.univ : Finset V) ⊆ _)
      have h1 := Finset.card_union_le ({v} ∪ U1 ∪ Gam) U2
      have h2 := Finset.card_union_le ({v} ∪ U1) Gam
      have h3 := Finset.card_union_le ({v} : Finset V) U1
      rw [Finset.card_univ] at h4
      rw [Finset.card_singleton] at h3
      omega
    obtain ⟨T, hTcard, hTsparse⟩ := exists_sparse_half H hn3 hm1
    rw [hm] at hTsparse
    have hdisjU : Disjoint U1 U2 := by
      rw [Finset.disjoint_left]
      intro x hx hxU
      exact (Finset.mem_filter.mp hxU).2.1 hx
    have hcross : ∀ x ∈ U1, ∀ y ∈ U2, Cᶜ.Adj x y := by
      intro x hx y hy
      have hy' := Finset.mem_filter.mp hy
      rw [SimpleGraph.compl_adj]
      exact ⟨fun h => hy'.2.1 (h ▸ hx), hy'.2.2.2 x hx⟩
    have hu2 : U2.card ≤ (k - 1) * (H.induce (T : Set W)).edgeSet.ncard ∨ U2.card < T.card := by
      by_contra hcon2
      push_neg at hcon2
      obtain ⟨h1, h2⟩ := hcon2
      have hV1 : (k - 1) * (H.induce (T : Set W)).edgeSet.ncard + 1 ≤ Fintype.card (U2 : Set V) := by
        simp only [Finset.coe_sort_coe, Fintype.card_coe]
        omega
      have hV2 : Fintype.card (T : Set W) ≤ Fintype.card (U2 : Set V) := by
        simp only [Finset.coe_sort_coe, Fintype.card_coe]
        exact h2
      rcases ramsey_with_isolated k hk3 m ih (H.induce (T : Set W)) _ rfl (by omega) (U2 : Set V)
        (C.induce (U2 : Set V)) hV1 hV2 with h | h
      · exact hcyc (isContained_of_induce _ h)
      · exact hH (glue_clique_sparse H T C U1 U2 hdisjU (by omega) hU1clique hcross h)
    exact final_arith k (Fintype.card W) m t Gam.card U2.card (H.induce (T : Set W)).edgeSet.ncard
      T.card hk hn4 hnm ht2 hprop (by omega) hg hu2 hTsparse (by omega)
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
  classical
  have hk3 : 3 ≤ k := by omega
  have hne : Nonempty W := hc.nonempty
  have h0 : ∀ v, ∃ w, H.Adj v w := by
    intro v
    obtain ⟨e, he⟩ := (Set.ncard_pos (Set.toFinite _)).mp (by omega : 0 < H.edgeSet.ncard)
    induction e using Sym2.ind with
    | h a b =>
    have hab : H.Adj a b := he
    by_cases hva : v = a
    · exact ⟨b, hva ▸ hab⟩
    · obtain ⟨x, hx⟩ := (hc.preconnected v a).nonempty_neighborSet_left hva
      exact ⟨x, hx⟩
  obtain ⟨u, _, hu⟩ := Finset.exists_min_image Finset.univ (fun w => (H.neighborSet w).ncard)
    Finset.univ_nonempty
  have hu' : ∀ w, (H.neighborSet u).ncard ≤ (H.neighborSet w).ncard :=
    fun w => hu w (Finset.mem_univ w)
  by_contra hcon
  have hcyc : ¬ (SimpleGraph.cycleGraph k).IsContained C := fun h => hcon (Or.inl h)
  have hH : ¬ H.IsContained Cᶜ := fun h => hcon (Or.inr h)
  obtain ⟨v, S, hvS, hS, hsize⟩ := exists_red_star k hk3 m ih H hc hm hm2 u hu' V C hV hcyc hH
  have hd1 : 1 ≤ (H.neighborSet u).ncard := by
    obtain ⟨w, hw⟩ := h0 u
    exact Nat.one_le_iff_ne_zero.mpr ((Set.ncard_pos (Set.toFinite _)).mpr ⟨w, hw⟩).ne'
  rcases Nat.lt_or_ge (H.neighborSet u).ncard 2 with hd2 | hd2
  · have hd1' : (H.neighborSet u).ncard = 1 := by omega
    rw [hd1'] at hsize
    rcases step_min_degree_one k hk3 H hc m hm C v S hvS hS hsize with h | h
    · exact hcyc h
    · exact hH h
  · have hnd : Fintype.card W * (H.neighborSet u).ncard ≤ 2 * m := by
      calc Fintype.card W * (H.neighborSet u).ncard = ∑ _w : W, (H.neighborSet u).ncard := by
            rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
        _ ≤ ∑ w, (H.neighborSet w).ncard := Finset.sum_le_sum (fun w _ => hu' w)
        _ = 2 * H.edgeSet.ncard := degree_sum_ncard H
        _ = 2 * m := by rw [hm]
    have hS' := S_size_bound k (Fintype.card W) m (H.neighborSet u).ncard S.card hk3 hd2 hnd hsize
    rcases step_large_deg_two k hk m ih H hc hm (fun w => hd2.trans (hu' w)) V C hV v S hvS hS hS'
      with h | h
    · exact hcyc h
    · exact hH h
/-! N59 main_property [join, believed provable] deps: N09 N11 N14 N29 N45 N58 N08 -/
theorem main_property (k : ℕ) (hk : 3 ≤ k) (m : ℕ) :
    ∀ (W : Type) [Fintype W] (H : SimpleGraph W), (∀ v, ∃ w, H.Adj v w) →
      H.edgeSet.ncard = m → ∀ (V : Type) [Fintype V] (C : SimpleGraph V),
      (k - 1) * m + 1 ≤ Fintype.card V →
      (SimpleGraph.cycleGraph k).IsContained C ∨ H.IsContained Cᶜ := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro W _ H h0 hm V _ C hV
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · interval_cases m
    · exact Or.inr (ramsey_zero_edges H h0 hm C)
    · exact ramsey_one_edge k hk H h0 hm V C hV
  · rcases isEmpty_or_nonempty W with hW | hW
    · exact Or.inr SimpleGraph.IsContained.of_isEmpty
    · by_cases hc : H.Connected
      · rcases Nat.lt_or_ge k 7 with hk7 | hk7
        · rcases Nat.lt_or_ge k 4 with hk4 | hk4
          · have hk3 : k = 3 := by omega
            subst hk3
            exact goddard_kleitman_sidorenko H h0 m hm V C (by omega)
          · exact lemma4_small_cycles k (by omega) H hc m hm hm2 V C hV
        · exact step_connected_large k hk7 m ih H hc hm hm2 V C hV
      · exact step_disconnected k hk m ih H h0 hm hc hW V C hV
/-! ## Root -/

/-- **Cambie–Freschi (2026), Theorem 3.** For every `k ≥ 3` and every graph `H` with `m` edges and no isolated
vertices, `R(C_k, H) ≤ (k - 1) * m + 1`. -/
theorem cambie_freschi (k : ℕ) (hk : 3 ≤ k) (m : ℕ) (W : Type) [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (h0 : ∀ v, 0 < H.degree v) (hm : H.edgeSet.ncard = m) :
    SimpleGraph.graphRamsey (SimpleGraph.cycleGraph k) H ≤ (k - 1) * m + 1 := by
  apply Nat.sInf_le
  rw [Set.mem_setOf_eq]
  intro C
  apply main_property k hk m W H ?_ hm (Fin ((k - 1) * m + 1)) C (by simp)
  intro v
  exact (SimpleGraph.degree_pos_iff_exists_adj H v).mp (h0 v)
end Erdos569
