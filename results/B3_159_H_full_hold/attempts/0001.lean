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

/-! ## Helper lemmas (searcher's additions) -/

/-- Which ordered pairs of `Fin 4` are adjacent in the 4-cycle. -/
theorem cycleGraph_four_adj_cases (i j : Fin 4) (h : (SimpleGraph.cycleGraph 4).Adj i j) :
    (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨
    (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨ (i = 3 ∧ j = 0) ∨ (i = 0 ∧ j = 3) := by
  revert i j
  decide

/-- A 4-cycle `u a v b` in `G` (with `u ≠ v`, `a ≠ b`) gives a copy of `cycleGraph 4` in `G`. -/
def c4Copy {V : Type*} (G : SimpleGraph V) {u a v b : V}
    (hua : G.Adj u a) (hva : G.Adj v a) (hub : G.Adj u b) (hvb : G.Adj v b)
    (huv : u ≠ v) (hab : a ≠ b) : SimpleGraph.Copy (SimpleGraph.cycleGraph 4) G where
  toHom := ⟨![u, a, v, b], fun {i j} hij => by
    rcases cycleGraph_four_adj_cases i j hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hua
    · exact hua.symm
    · exact hva.symm
    · exact hva
    · exact hvb
    · exact hvb.symm
    · exact hub.symm
    · exact hub⟩
  injective' := by
    intro i j h
    have h4 : ∀ k : Fin 4, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by decide
    have hau : a ≠ u := hua.ne.symm
    have hav : a ≠ v := hva.ne.symm
    have hbu : b ≠ u := hub.ne.symm
    have hbv : b ≠ v := hvb.ne.symm
    rcases h4 i with rfl | rfl | rfl | rfl <;> rcases h4 j with rfl | rfl | rfl | rfl <;>
      first
      | rfl
      | exact absurd h (by
          first
          | exact hua.ne | exact hau | exact huv | exact huv.symm | exact hub.ne | exact hbu
          | exact hav | exact hva.ne | exact hab | exact hab.symm | exact hvb.ne | exact hbv)

/-- An independent set in a graph with no independent `n`-set has fewer than `n` vertices. -/
theorem card_lt_of_indepSetFree {V : Type*} (G : SimpleGraph V) {n : ℕ} (hα : G.IndepSetFree n)
    {t : Finset V} (ht : G.IsIndepSet (t : Set V)) : t.card < n := by
  by_contra h
  push_neg at h
  obtain ⟨u, hut, hcard⟩ := Finset.exists_subset_card_eq h
  exact hα u ⟨ht.mono (Finset.coe_subset.2 hut), hcard⟩

/-- A graph with no independent `n`-set forces `0 < n` (the empty set is `0`-independent). -/
theorem indepSetFree_pos {V : Type*} (G : SimpleGraph V) {n : ℕ} (hα : G.IndepSetFree n) :
    0 < n := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · exfalso
    apply hα (∅ : Finset V)
    refine ⟨?_, rfl⟩
    rw [Finset.coe_empty]
    exact Set.pairwise_empty _
  · exact h

/-! ## Blueprint nodes -/

-- N01
theorem graphRamsey_le_of_forall {α β : Type*} [Fintype α] [Fintype β]
    (G : SimpleGraph α) (H : SimpleGraph β) (N : ℕ)
    (h : ∀ C : SimpleGraph (Fin N), G.IsContained C ∨ H.IsContained Cᶜ) :
    SimpleGraph.graphRamsey G H ≤ N := by
  unfold SimpleGraph.graphRamsey
  exact Nat.sInf_le h

-- N02
theorem complete_isContained_compl_iff {V : Type*} (C : SimpleGraph V) (n : ℕ) :
    (SimpleGraph.completeGraph (Fin n)).IsContained Cᶜ ↔ ¬ C.IndepSetFree n := by
  rw [← SimpleGraph.not_cliqueFree_iff_top_isContained, SimpleGraph.cliqueFree_compl]

-- N03
theorem c4_free_common_nbrs {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ¬ (SimpleGraph.cycleGraph 4).IsContained G) {u v : V} (huv : u ≠ v) :
    (G.neighborFinset u ∩ G.neighborFinset v).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  by_contra hab
  simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at ha hb
  exact hG ⟨c4Copy G ha.1 ha.2 hb.1 hb.2 huv hab⟩

-- N04
theorem c4_free_nbhd_local_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ¬ (SimpleGraph.cycleGraph 4).IsContained G) (v w : V) (hw : G.Adj v w) :
    ((G.neighborFinset v).filter (G.Adj w)).card ≤ 1 := by
  refine le_trans (Finset.card_le_card ?_) (c4_free_common_nbrs G hG hw.ne)
  intro x hx
  simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset, Finset.mem_inter] at hx ⊢
  exact hx

-- N05
theorem greedy_indep_local {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) (D : ℕ)
    (hD : ∀ v ∈ s, (s.filter (G.Adj v)).card ≤ D) :
    ∃ t ⊆ s, G.IsIndepSet (t : Set V) ∧ s.card ≤ (D + 1) * t.card := by
  induction s using Finset.strongInduction with
  | H s ih =>
    rcases s.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
    · refine ⟨∅, Finset.Subset.refl _, ?_, by simp⟩
      rw [Finset.coe_empty]
      exact Set.pairwise_empty _
    · set s' := s.filter (fun x => ¬ (x = v ∨ G.Adj v x)) with hs'
      have hs'sub : s' ⊆ s := Finset.filter_subset _ _
      have hvs' : v ∉ s' := by simp [hs']
      have hss' : s' ⊂ s := Finset.ssubset_iff_subset_ne.2 ⟨hs'sub, fun h => hvs' (h ▸ hv)⟩
      obtain ⟨t', ht's', ht'ind, ht'card⟩ := ih s' hss' (fun x hx =>
        le_trans (Finset.card_le_card (Finset.filter_subset_filter _ hs'sub)) (hD x (hs'sub hx)))
      have hvt' : v ∉ t' := fun h => hvs' (ht's' h)
      refine ⟨insert v t', Finset.insert_subset hv (ht's'.trans hs'sub), ?_, ?_⟩
      · rw [Finset.coe_insert]
        refine Set.pairwise_insert.2 ⟨ht'ind, fun b hb _ => ?_⟩
        have hb' : b ∈ s' := ht's' hb
        simp only [hs', Finset.mem_filter, not_or] at hb'
        exact ⟨hb'.2.2, fun h => hb'.2.2 h.symm⟩
      · rw [Finset.card_insert_of_notMem hvt']
        have h1 : (s.filter (fun x => x = v ∨ G.Adj v x)).card + s'.card = s.card :=
          Finset.card_filter_add_card_filter_not _
        have h2 : (s.filter (fun x => x = v ∨ G.Adj v x)).card ≤ D + 1 := by
          calc (s.filter (fun x => x = v ∨ G.Adj v x)).card
              ≤ (insert v (s.filter (G.Adj v))).card := by
                apply Finset.card_le_card
                intro x hx
                simp only [Finset.mem_filter, Finset.mem_insert] at hx ⊢
                rcases hx.2 with h | h
                · exact Or.inl h
                · exact Or.inr ⟨hx.1, h⟩
            _ ≤ (s.filter (G.Adj v)).card + 1 := Finset.card_insert_le _ _
            _ ≤ D + 1 := by have := hD v hv; omega
        calc s.card = (s.filter (fun x => x = v ∨ G.Adj v x)).card + s'.card := h1.symm
          _ ≤ (D + 1) + (D + 1) * t'.card := Nat.add_le_add h2 ht'card
          _ = (D + 1) * (t'.card + 1) := by ring

-- N06
theorem degree_lt_of_c4_free_indepSetFree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ¬ (SimpleGraph.cycleGraph 4).IsContained G) {n : ℕ} (hα : G.IndepSetFree n) (v : V) :
    G.degree v < 2 * n := by
  obtain ⟨t, -, htind, htcard⟩ := greedy_indep_local G (G.neighborFinset v) 1
    (fun w hw => c4_free_nbhd_local_degree G hG v w (by rwa [SimpleGraph.mem_neighborFinset] at hw))
  have := card_lt_of_indepSetFree G hα htind
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  omega

-- N07
theorem card_le_quadratic_of_c4_free {N n : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (hG : ¬ (SimpleGraph.cycleGraph 4).IsContained G) (hα : G.IndepSetFree n) :
    N ≤ 2 * n * n := by
  have hn := indepSetFree_pos G hα
  obtain ⟨t, -, htind, htcard⟩ := greedy_indep_local G Finset.univ (2 * n - 1) (fun v _ => by
    have h1 := degree_lt_of_c4_free_indepSetFree G hG hα v
    have h2 : Finset.univ.filter (G.Adj v) = G.neighborFinset v := by
      ext w
      simp
    rw [h2, SimpleGraph.card_neighborFinset_eq_degree]
    omega)
  have ht := card_lt_of_indepSetFree G hα htind
  rw [Finset.card_univ, Fintype.card_fin] at htcard
  have h2 : 2 * n - 1 + 1 = 2 * n := by omega
  rw [h2] at htcard
  calc N ≤ 2 * n * t.card := htcard
    _ ≤ 2 * n * n := Nat.mul_le_mul_left _ ht.le

-- N08
theorem graphRamsey_le_of_c4_free_bound (n N : ℕ)
    (h : ∀ G : SimpleGraph (Fin N), ¬ (SimpleGraph.cycleGraph 4).IsContained G → ¬ G.IndepSetFree n) :
    SimpleGraph.graphRamsey (SimpleGraph.cycleGraph 4) (SimpleGraph.completeGraph (Fin n)) ≤ N := by
  apply graphRamsey_le_of_forall
  intro C
  rw [complete_isContained_compl_iff]
  exact or_iff_not_imp_left.2 (h C)

-- N09
theorem graphRamsey_c4_le_quadratic (n : ℕ) :
    SimpleGraph.graphRamsey (SimpleGraph.cycleGraph 4) (SimpleGraph.completeGraph (Fin n)) ≤ 2 * n * n + 1 := by
  apply graphRamsey_le_of_c4_free_bound
  intro G hG hα
  classical
  have := card_le_quadratic_of_c4_free G hG hα
  omega

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
