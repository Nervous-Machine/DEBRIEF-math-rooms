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
  push Not at h
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

/-! ### Helpers for the counting rooms -/

/-- The neighbours of `v` among all vertices are exactly its neighbour finset. -/
theorem filter_univ_adj_eq {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) : Finset.univ.filter (G.Adj v) = G.neighborFinset v := by
  ext w
  simp

/-- The number of neighbours of `v` inside any finset is at most the degree of `v`. -/
theorem card_filter_adj_le_degree {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Finset V) (v : V) : (s.filter (G.Adj v)).card ≤ G.degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← filter_univ_adj_eq]
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))

-- N10
theorem turan_weak {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ t : Finset V, G.IsIndepSet (t : Set V) ∧
      Fintype.card V ^ 2 ≤ 2 * (4 * G.edgeFinset.card + Fintype.card V) * t.card := by
  rcases Nat.eq_zero_or_pos (Fintype.card V) with hn0 | hnpos
  · refine ⟨∅, ?_, ?_⟩
    · rw [Finset.coe_empty]
      exact Set.pairwise_empty _
    · rw [hn0]
      simp
  obtain ⟨D, hDdef⟩ : ∃ D, 4 * G.edgeFinset.card / Fintype.card V = D := ⟨_, rfl⟩
  have hC : D * Fintype.card V ≤ 4 * G.edgeFinset.card := by
    rw [← hDdef]
    exact Nat.div_mul_le_self _ _
  have h4m : 4 * G.edgeFinset.card < (D + 1) * Fintype.card V := by
    have h1 := Nat.div_add_mod (4 * G.edgeFinset.card) (Fintype.card V)
    rw [hDdef] at h1
    have h2 : 4 * G.edgeFinset.card % Fintype.card V < Fintype.card V := Nat.mod_lt _ hnpos
    calc 4 * G.edgeFinset.card = Fintype.card V * D + 4 * G.edgeFinset.card % Fintype.card V :=
          h1.symm
      _ < Fintype.card V * D + Fintype.card V := Nat.add_lt_add_left h2 _
      _ = (D + 1) * Fintype.card V := by ring
  -- the low-degree vertices
  have hsb : (Finset.univ.filter (fun v => G.degree v ≤ D)).card
      + (Finset.univ.filter (fun v => ¬ G.degree v ≤ D)).card = Fintype.card V := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ]
  have hbsum : (D + 1) * (Finset.univ.filter (fun v => ¬ G.degree v ≤ D)).card
      ≤ 2 * G.edgeFinset.card := by
    calc (D + 1) * (Finset.univ.filter (fun v => ¬ G.degree v ≤ D)).card
        = (Finset.univ.filter (fun v => ¬ G.degree v ≤ D)).card • (D + 1) := by
          rw [smul_eq_mul, mul_comm]
      _ ≤ ∑ v ∈ Finset.univ.filter (fun v => ¬ G.degree v ≤ D), G.degree v :=
          Finset.card_nsmul_le_sum _ _ _ (fun v hv => by
            simp only [Finset.mem_filter] at hv
            omega)
      _ ≤ ∑ v, G.degree v :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
      _ = 2 * G.edgeFinset.card := SimpleGraph.sum_degrees_eq_twice_card_edges G
  have hb2 : 2 * (Finset.univ.filter (fun v => ¬ G.degree v ≤ D)).card < Fintype.card V := by
    have h1 : (D + 1) * (2 * (Finset.univ.filter (fun v => ¬ G.degree v ≤ D)).card)
        < (D + 1) * Fintype.card V := by
      calc (D + 1) * (2 * (Finset.univ.filter (fun v => ¬ G.degree v ≤ D)).card)
          = 2 * ((D + 1) * (Finset.univ.filter (fun v => ¬ G.degree v ≤ D)).card) := by ring
        _ ≤ 2 * (2 * G.edgeFinset.card) := Nat.mul_le_mul_left 2 hbsum
        _ = 4 * G.edgeFinset.card := by ring
        _ < (D + 1) * Fintype.card V := h4m
    exact Nat.lt_of_mul_lt_mul_left h1
  have hA : Fintype.card V ≤ 2 * (Finset.univ.filter (fun v => G.degree v ≤ D)).card := by omega
  obtain ⟨t, -, htind, htcard⟩ := greedy_indep_local G (Finset.univ.filter (fun v => G.degree v ≤ D))
    D (fun v hv => by
      simp only [Finset.mem_filter] at hv
      exact (card_filter_adj_le_degree G _ v).trans hv.2)
  refine ⟨t, htind, ?_⟩
  calc Fintype.card V ^ 2 = Fintype.card V * Fintype.card V := sq _
    _ ≤ (2 * (Finset.univ.filter (fun v => G.degree v ≤ D)).card) * Fintype.card V :=
        Nat.mul_le_mul_right _ hA
    _ ≤ (2 * ((D + 1) * t.card)) * Fintype.card V :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 htcard)
    _ = 2 * t.card * (D * Fintype.card V + Fintype.card V) := by ring
    _ ≤ 2 * t.card * (4 * G.edgeFinset.card + Fintype.card V) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add_right hC _)
    _ = 2 * (4 * G.edgeFinset.card + Fintype.card V) * t.card := by ring

/-- Removing one vertex `v` from `s` loses at most `2 * deg_s(v)` from the internal degree sum. -/
theorem sum_filter_adj_erase_le {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (s : Finset V) {v : V} (hv : v ∈ s) :
    ∑ u ∈ s, (s.filter (G.Adj u)).card
      ≤ ∑ u ∈ s.erase v, ((s.erase v).filter (G.Adj u)).card + 2 * (s.filter (G.Adj v)).card := by
  have h1 : ∑ u ∈ s, (s.filter (G.Adj u)).card
      = (s.filter (G.Adj v)).card + ∑ u ∈ s.erase v, (s.filter (G.Adj u)).card :=
    (Finset.add_sum_erase s _ hv).symm
  have h2 : ∀ u ∈ s.erase v, (s.filter (G.Adj u)).card
      ≤ ((s.erase v).filter (G.Adj u)).card + (if G.Adj u v then 1 else 0) := by
    intro u _
    rw [Finset.filter_erase]
    by_cases huv : G.Adj u v
    · have hmem : v ∈ s.filter (G.Adj u) := Finset.mem_filter.2 ⟨hv, huv⟩
      rw [Finset.card_erase_of_mem hmem, if_pos huv]
      have : 0 < (s.filter (G.Adj u)).card := Finset.card_pos.2 ⟨v, hmem⟩
      omega
    · have hmem : v ∉ s.filter (G.Adj u) := fun h => huv (Finset.mem_filter.1 h).2
      rw [Finset.erase_eq_of_notMem hmem, if_neg huv, add_zero]
  have h3 : ∑ u ∈ s.erase v, (if G.Adj u v then 1 else 0) ≤ (s.filter (G.Adj v)).card := by
    rw [← Finset.card_filter]
    apply Finset.card_le_card
    intro u hu
    simp only [Finset.mem_filter, Finset.mem_erase] at hu ⊢
    exact ⟨hu.1.2, hu.2.symm⟩
  calc ∑ u ∈ s, (s.filter (G.Adj u)).card
      = (s.filter (G.Adj v)).card + ∑ u ∈ s.erase v, (s.filter (G.Adj u)).card := h1
    _ ≤ (s.filter (G.Adj v)).card
        + ∑ u ∈ s.erase v, (((s.erase v).filter (G.Adj u)).card + (if G.Adj u v then 1 else 0)) :=
        Nat.add_le_add_left (Finset.sum_le_sum h2) _
    _ = (s.filter (G.Adj v)).card + (∑ u ∈ s.erase v, ((s.erase v).filter (G.Adj u)).card
        + ∑ u ∈ s.erase v, (if G.Adj u v then 1 else 0)) := by rw [Finset.sum_add_distrib]
    _ ≤ (s.filter (G.Adj v)).card + (∑ u ∈ s.erase v, ((s.erase v).filter (G.Adj u)).card
        + (s.filter (G.Adj v)).card) := Nat.add_le_add_left (Nat.add_le_add_left h3 _) _
    _ = ∑ u ∈ s.erase v, ((s.erase v).filter (G.Adj u)).card + 2 * (s.filter (G.Adj v)).card := by
        ring

/-- A finset whose internal degree sum is at least `2 d` times its size contains a nonempty
subset of minimum internal degree at least `d`. -/
theorem dense_core_aux {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (d : ℕ) (s : Finset V) (hs : s.Nonempty)
    (hσ : 2 * d * s.card ≤ ∑ v ∈ s, (s.filter (G.Adj v)).card) :
    ∃ s' : Finset V, s' ⊆ s ∧ s'.Nonempty ∧ ∀ v ∈ s', d ≤ (s'.filter (G.Adj v)).card := by
  induction s using Finset.strongInduction with
  | H s ih =>
    by_cases hall : ∀ v ∈ s, d ≤ (s.filter (G.Adj v)).card
    · exact ⟨s, Finset.Subset.refl _, hs, hall⟩
    · push Not at hall
      obtain ⟨v, hv, hvd⟩ := hall
      have hss' : s.erase v ⊂ s := Finset.erase_ssubset hv
      have hcard : s.card = (s.erase v).card + 1 := by
        rw [Finset.card_erase_of_mem hv]
        have : 0 < s.card := Finset.card_pos.2 ⟨v, hv⟩
        omega
      have hsum := sum_filter_adj_erase_le G s hv
      have hσ' : 2 * d * (s.erase v).card < ∑ u ∈ s.erase v, ((s.erase v).filter (G.Adj u)).card := by
        have e1 : 2 * d * s.card = 2 * d * (s.erase v).card + 2 * d := by rw [hcard]; ring
        linarith
      have hne : (s.erase v).Nonempty := by
        by_contra hemp
        rw [Finset.not_nonempty_iff_eq_empty] at hemp
        rw [hemp, Finset.sum_empty] at hσ'
        exact absurd hσ' (Nat.not_lt_zero _)
      obtain ⟨s'', hs''sub, hs''ne, hs''min⟩ := ih (s.erase v) hss' hne hσ'.le
      exact ⟨s'', hs''sub.trans (Finset.erase_subset _ _), hs''ne, hs''min⟩

-- N11
theorem exists_dense_core {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
    (hd : d * Fintype.card V ≤ G.edgeFinset.card) :
    ∃ s : Finset V, s.Nonempty ∧ ∀ v ∈ s, d ≤ (s.filter (G.Adj v)).card := by
  obtain ⟨s, -, hne, hmin⟩ := dense_core_aux G d Finset.univ Finset.univ_nonempty (by
    have h1 : ∑ v ∈ Finset.univ, (Finset.univ.filter (G.Adj v)).card = 2 * G.edgeFinset.card := by
      rw [← SimpleGraph.sum_degrees_eq_twice_card_edges G]
      apply Finset.sum_congr rfl
      intro v _
      rw [filter_univ_adj_eq, SimpleGraph.card_neighborFinset_eq_degree]
    rw [h1, Finset.card_univ]
    calc 2 * d * Fintype.card V = 2 * (d * Fintype.card V) := by ring
      _ ≤ 2 * G.edgeFinset.card := Nat.mul_le_mul_left 2 hd)
  exact ⟨s, hne, hmin⟩

-- N12
theorem moore_bound_c4_free {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ¬ (SimpleGraph.cycleGraph 4).IsContained G) (s : Finset V) (d : ℕ) (hs : s.Nonempty)
    (hmin : ∀ v ∈ s, d ≤ (s.filter (G.Adj v)).card) :
    d * d ≤ 2 * s.card := by
  obtain ⟨v, hv⟩ := hs
  have hAd : d ≤ (s.filter (G.Adj v)).card := hmin v hv
  have hAs : s.filter (G.Adj v) ⊆ s := Finset.filter_subset _ _
  have hdisj : ((s.filter (G.Adj v) : Finset V) : Set V).PairwiseDisjoint
      (fun a => (s.filter (G.Adj a)).erase v) := by
    intro a ha b hb hab
    refine Finset.disjoint_left.2 ?_
    intro x hxa hxb
    simp only [Finset.mem_erase, Finset.mem_filter] at hxa hxb
    have ha' : G.Adj v a := (Finset.mem_filter.1 (Finset.mem_coe.1 ha)).2
    have hb' : G.Adj v b := (Finset.mem_filter.1 (Finset.mem_coe.1 hb)).2
    have hcard := c4_free_common_nbrs G hG hab
    rw [Finset.card_le_one] at hcard
    apply hxa.1
    apply hcard x _ v _
    · rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset]
      exact ⟨hxa.2.2, hxb.2.2⟩
    · rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset]
      exact ⟨ha'.symm, hb'.symm⟩
  have hunion : ((s.filter (G.Adj v)).biUnion (fun a => (s.filter (G.Adj a)).erase v)).card
      ≤ s.card :=
    Finset.card_le_card (Finset.biUnion_subset.2 (fun a _ =>
      (Finset.erase_subset _ _).trans (Finset.filter_subset _ _)))
  rw [Finset.card_biUnion hdisj] at hunion
  have hlow : (s.filter (G.Adj v)).card • (d - 1)
      ≤ ∑ a ∈ s.filter (G.Adj v), ((s.filter (G.Adj a)).erase v).card :=
    Finset.card_nsmul_le_sum _ _ _ (fun a ha => by
      have h1 := hmin a (hAs ha)
      have h2 : (s.filter (G.Adj a)).card - 1 ≤ ((s.filter (G.Adj a)).erase v).card :=
        Finset.pred_card_le_card_erase
      omega)
  rw [smul_eq_mul] at hlow
  have hAs' : (s.filter (G.Adj v)).card ≤ s.card := Finset.card_le_card hAs
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · have h3 : d * (d - 1) ≤ (s.filter (G.Adj v)).card * (d - 1) := Nat.mul_le_mul_right _ hAd
    have h4 : d * d = d * (d - 1) + d := by
      have : d - 1 + 1 = d := Nat.sub_add_cancel hd
      calc d * d = d * (d - 1 + 1) := by rw [this]
        _ = d * (d - 1) + d := by ring
    omega

/-! ### Helpers for the open core N13 -/

/-- In a `C₄`-free graph, the neighbourhood of `v` inside `s` induces a matching, so it contains
an independent set of at least half its size. -/
theorem nbhd_half_indep {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ¬ (SimpleGraph.cycleGraph 4).IsContained G) (s : Finset V) (v : V) :
    ∃ t ⊆ s.filter (G.Adj v), G.IsIndepSet (t : Set V) ∧ (s.filter (G.Adj v)).card ≤ 2 * t.card := by
  obtain ⟨t, hts, hind, hcard⟩ := greedy_indep_local G (s.filter (G.Adj v)) 1 (fun w hw => by
    have hw' : G.Adj v w := (Finset.mem_filter.1 hw).2
    refine le_trans (Finset.card_le_card ?_) (c4_free_nbhd_local_degree G hG v w hw')
    intro x hx
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hx ⊢
    exact ⟨hx.1.2, hx.2⟩)
  exact ⟨t, hts, hind, by omega⟩

/-- The empty set is independent and meets the N13 bound (`0 ^ p = 0` for `p > 0`). -/
theorem empty_case_N13 {V : Type*} (G : SimpleGraph V) (K p : ℝ) (hp : 0 < p) :
    ∃ t ⊆ (∅ : Finset V), G.IsIndepSet (t : Set V) ∧
      K * ((∅ : Finset V).card : ℝ) ^ p ≤ (t.card : ℝ) := by
  refine ⟨∅, Finset.Subset.refl _, ?_, ?_⟩
  · rw [Finset.coe_empty]
    exact Set.pairwise_empty _
  · simp only [Finset.card_empty, Nat.cast_zero]
    rw [Real.zero_rpow hp.ne']
    simp

/-- Every finite set `s` in a `C₄`-free graph carries an independent set `t` with
`|s| ≤ (2|t|+1)|t|`, i.e. of size about `√|s|`: either the vertex of maximum internal degree has a
large neighbourhood (which induces a matching), or all internal degrees are small (greedy). -/
theorem exists_indep_sqrt {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ¬ (SimpleGraph.cycleGraph 4).IsContained G) (s : Finset V) :
    ∃ t ⊆ s, G.IsIndepSet (t : Set V) ∧ s.card ≤ (2 * t.card + 1) * t.card := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · refine ⟨∅, Finset.Subset.refl _, ?_, by simp⟩
    rw [Finset.coe_empty]
    exact Set.pairwise_empty _
  obtain ⟨v, hv, hvmax⟩ := s.exists_max_image (fun u => (s.filter (G.Adj u)).card) hne
  obtain ⟨t₁, ht₁s, hind₁, hcard₁⟩ := nbhd_half_indep G hG s v
  obtain ⟨t₂, ht₂s, hind₂, hcard₂⟩ := greedy_indep_local G s _ (fun u hu => hvmax u hu)
  rcases le_or_gt t₁.card t₂.card with h | h
  · refine ⟨t₂, ht₂s, hind₂, ?_⟩
    calc s.card ≤ ((s.filter (G.Adj v)).card + 1) * t₂.card := hcard₂
      _ ≤ (2 * t₂.card + 1) * t₂.card := Nat.mul_le_mul_right _ (by omega)
  · refine ⟨t₁, ht₁s.trans (Finset.filter_subset _ _), hind₁, ?_⟩
    calc s.card ≤ ((s.filter (G.Adj v)).card + 1) * t₂.card := hcard₂
      _ ≤ (2 * t₁.card + 1) * t₁.card := Nat.mul_le_mul (by omega) h.le

/-- Deleting a vertex of minimum internal degree together with its neighbourhood: by the Moore
bound N12 that neighbourhood has at most `M + 1` vertices once `2|s| ≤ (M+1)²`, and `C₄`-freeness is
inherited, so repeating yields an independent set `t` with `|s| ≤ (M+2)|t|`. -/
theorem exists_indep_moore {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ¬ (SimpleGraph.cycleGraph 4).IsContained G) (M : ℕ) (s : Finset V)
    (hs : 2 * s.card ≤ (M + 1) * (M + 1)) :
    ∃ t ⊆ s, G.IsIndepSet (t : Set V) ∧ s.card ≤ (M + 2) * t.card := by
  induction s using Finset.strongInduction with
  | H s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hne
    · refine ⟨∅, Finset.Subset.refl _, ?_, by simp⟩
      rw [Finset.coe_empty]
      exact Set.pairwise_empty _
    · obtain ⟨v, hv, hvmin⟩ := s.exists_min_image (fun u => (s.filter (G.Adj u)).card) hne
      have hmoore := moore_bound_c4_free G hG s _ hne (fun u hu => hvmin u hu)
      have hdM : (s.filter (G.Adj v)).card ≤ M + 1 := by
        by_contra h
        push Not at h
        have : (M + 2) * (M + 2) ≤ (s.filter (G.Adj v)).card * (s.filter (G.Adj v)).card :=
          Nat.mul_le_mul h h
        nlinarith
      set s' := s.filter (fun x => ¬ (x = v ∨ G.Adj v x)) with hs'
      have hs'sub : s' ⊆ s := Finset.filter_subset _ _
      have hvs' : v ∉ s' := by simp [hs']
      have hss' : s' ⊂ s := Finset.ssubset_iff_subset_ne.2 ⟨hs'sub, fun h => hvs' (h ▸ hv)⟩
      have hs'card : 2 * s'.card ≤ (M + 1) * (M + 1) :=
        le_trans (Nat.mul_le_mul_left 2 (Finset.card_le_card hs'sub)) hs
      obtain ⟨t', ht's', ht'ind, ht'card⟩ := ih s' hss' hs'card
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
        have h2 : (s.filter (fun x => x = v ∨ G.Adj v x)).card ≤ M + 2 := by
          calc (s.filter (fun x => x = v ∨ G.Adj v x)).card
              ≤ (insert v (s.filter (G.Adj v))).card := by
                apply Finset.card_le_card
                intro x hx
                simp only [Finset.mem_filter, Finset.mem_insert] at hx ⊢
                rcases hx.2 with h | h
                · exact Or.inl h
                · exact Or.inr ⟨hx.1, h⟩
            _ ≤ (s.filter (G.Adj v)).card + 1 := Finset.card_insert_le _ _
            _ ≤ M + 2 := by omega
        calc s.card = (s.filter (fun x => x = v ∨ G.Adj v x)).card + s'.card := h1.symm
          _ ≤ (M + 2) + (M + 2) * t'.card := Nat.add_le_add h2 ht'card
          _ = (M + 2) * (t'.card + 1) := by ring

/-- Two-vertex route. In a `C₄`-free graph, for distinct `u v`, the pruned union
`(N_s(u) \ {v}) ∪ (N_s(v) \ {u})` has internal maximum degree at most `2` (every vertex has at most
one common neighbour with `u` and one with `v`), so it carries an independent set `t` with
`deg_s(u) + deg_s(v) ≤ 3|t| + 3`. -/
theorem two_nbhd_union {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ¬ (SimpleGraph.cycleGraph 4).IsContained G) (s : Finset V) {u v : V} (huv : u ≠ v) :
    ∃ t ⊆ s, G.IsIndepSet (t : Set V) ∧
      (s.filter (G.Adj u)).card + (s.filter (G.Adj v)).card ≤ 3 * t.card + 3 := by
  have hdeg : ∀ x ∈ (s.filter (G.Adj u)).erase v ∪ (s.filter (G.Adj v)).erase u,
      (((s.filter (G.Adj u)).erase v ∪ (s.filter (G.Adj v)).erase u).filter (G.Adj x)).card ≤ 2 := by
    intro x hx
    have hxu : x ≠ u := by
      rintro rfl
      rcases Finset.mem_union.1 hx with h | h
      · exact (Finset.mem_filter.1 (Finset.mem_of_mem_erase h)).2.ne rfl
      · exact (Finset.ne_of_mem_erase h) rfl
    have hxv : x ≠ v := by
      rintro rfl
      rcases Finset.mem_union.1 hx with h | h
      · exact (Finset.ne_of_mem_erase h) rfl
      · exact (Finset.mem_filter.1 (Finset.mem_of_mem_erase h)).2.ne rfl
    rw [Finset.filter_union]
    refine (Finset.card_union_le _ _).trans ?_
    have ha : (((s.filter (G.Adj u)).erase v).filter (G.Adj x)).card ≤ 1 := by
      refine le_trans (Finset.card_le_card ?_) (c4_free_common_nbrs G hG hxu)
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_inter,
        SimpleGraph.mem_neighborFinset] at hy ⊢
      exact ⟨hy.2, hy.1.2.2⟩
    have hb : (((s.filter (G.Adj v)).erase u).filter (G.Adj x)).card ≤ 1 := by
      refine le_trans (Finset.card_le_card ?_) (c4_free_common_nbrs G hG hxv)
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_inter,
        SimpleGraph.mem_neighborFinset] at hy ⊢
      exact ⟨hy.2, hy.1.2.2⟩
    omega
  obtain ⟨t, hts, hind, hcard⟩ := greedy_indep_local G _ 2 hdeg
  refine ⟨t, hts.trans ?_, hind, ?_⟩
  · intro y hy
    rcases Finset.mem_union.1 hy with h | h
    · exact (Finset.mem_filter.1 (Finset.mem_of_mem_erase h)).1
    · exact (Finset.mem_filter.1 (Finset.mem_of_mem_erase h)).1
  · have hinter : ((s.filter (G.Adj u)).erase v ∩ (s.filter (G.Adj v)).erase u).card ≤ 1 := by
      refine le_trans (Finset.card_le_card ?_) (c4_free_common_nbrs G hG huv)
      intro y hy
      simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_filter,
        SimpleGraph.mem_neighborFinset] at hy ⊢
      exact ⟨hy.1.2.2, hy.2.2.2⟩
    have hA : (s.filter (G.Adj u)).card - 1 ≤ ((s.filter (G.Adj u)).erase v).card :=
      Finset.pred_card_le_card_erase
    have hB : (s.filter (G.Adj v)).card - 1 ≤ ((s.filter (G.Adj v)).erase u).card :=
      Finset.pred_card_le_card_erase
    have hU := Finset.card_union_add_card_inter ((s.filter (G.Adj u)).erase v)
      ((s.filter (G.Adj v)).erase u)
    omega

-- N13 (open core). Attempt 11: the larger of the `√|s|` set and the two-vertex set.
theorem core_near_extremal :
    ∃ δ η : ℝ, 0 < δ ∧ δ ≤ 1 / 8 ∧ 4 * δ ≤ η ∧ ∀ κ : ℝ, 0 < κ → ∃ K : ℝ, 0 < K ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V),
        ¬ (SimpleGraph.cycleGraph 4).IsContained G →
        (∀ v ∈ s, κ * (s.card : ℝ) ^ ((1 : ℝ) / 2 - δ) ≤ ((s.filter (G.Adj v)).card : ℝ)) →
        ∃ t ⊆ s, G.IsIndepSet (t : Set V) ∧ K * (s.card : ℝ) ^ ((1 : ℝ) / 2 + η) ≤ (t.card : ℝ) := by
  refine ⟨1 / 100, 1 / 25, by norm_num, by norm_num, by norm_num, ?_⟩
  intro κ hκ
  refine ⟨min (κ / 8) (1 / 4), lt_min (by positivity) (by norm_num), ?_⟩
  intro V _ _ G _ s hG hmin
  rcases s.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
  · exact empty_case_N13 G _ _ (by norm_num)
  have hs1' : (1 : ℝ) ≤ s.card := by exact_mod_cast Finset.card_pos.2 ⟨v, hv⟩
  have hX0 : 0 ≤ (s.card : ℝ) ^ ((1 : ℝ) / 2 + 1 / 25) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hK1 : min (κ / 8) (1 / 4 : ℝ) ≤ κ / 8 := min_le_left _ _
  have hK2 : min (κ / 8) (1 / 4 : ℝ) ≤ 1 / 4 := min_le_right _ _
  have hK0 : 0 ≤ min (κ / 8) (1 / 4 : ℝ) := le_min (by positivity) (by norm_num)
  by_cases hs1 : s = {v}
  · exfalso
    have h := hmin v hv
    subst hs1
    have h0 : (({v} : Finset V).filter (G.Adj v)).card = 0 := by
      simp [Finset.filter_singleton]
    rw [h0, Finset.card_singleton, Nat.cast_one, Real.one_rpow, mul_one, Nat.cast_zero] at h
    linarith
  obtain ⟨u, hu, huv⟩ : ∃ u ∈ s, u ≠ v := by
    by_contra h
    push Not at h
    exact hs1 (Finset.eq_singleton_iff_unique_mem.2 ⟨hv, h⟩)
  obtain ⟨t₁, hts₁, hind₁, hcard₁⟩ := exists_indep_sqrt G hG s
  obtain ⟨t₂, hts₂, hind₂, hcard₂⟩ := two_nbhd_union G hG s huv
  have h1 := hmin u hu
  have h2 := hmin v hv
  have h3 : ((s.filter (G.Adj u)).card : ℝ) + (s.filter (G.Adj v)).card ≤ 3 * t₂.card + 3 := by
    exact_mod_cast hcard₂
  have h4 : (s.card : ℝ) ≤ (2 * t₁.card + 1) * t₁.card := by exact_mod_cast hcard₁
  have ht₁0 : (0 : ℝ) ≤ t₁.card := Nat.cast_nonneg _
  have hroot : ((s.card : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 = s.card := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num
  have hr0 : 0 ≤ (s.card : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hr1 : 1 ≤ (s.card : ℝ) ^ ((1 : ℝ) / 2) := Real.one_le_rpow hs1' (by norm_num)
  have hsq : (s.card : ℝ) ^ ((1 : ℝ) / 2) ≤ 4 * t₁.card := by nlinarith
  -- the two walls, one per branch: `X ≤ |s|^(1/2)` and `X ≤ |s|^(1/2-δ)`
  have hexp₁ : (s.card : ℝ) ^ ((1 : ℝ) / 2 + 1 / 25) ≤ (s.card : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hs1' (by norm_num)
  have hexp₂ : (s.card : ℝ) ^ ((1 : ℝ) / 2 + 1 / 25) ≤ (s.card : ℝ) ^ ((1 : ℝ) / 2 - 1 / 100) :=
    Real.rpow_le_rpow_of_exponent_le hs1' (by norm_num)
  rcases le_or_gt 6 (κ * (s.card : ℝ) ^ ((1 : ℝ) / 2 - 1 / 100)) with h6 | h6
  · -- dense enough: the two-vertex set wins
    refine ⟨t₂, hts₂, hind₂, ?_⟩
    nlinarith
  · -- otherwise the `√|s|` set
    refine ⟨t₁, hts₁, hind₁, ?_⟩
    nlinarith

-- N14
theorem sparse_branch_arith (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (N E t : ℝ) (hN : 1 ≤ N)
    (hE0 : 0 ≤ E) (hE : E ≤ N ^ ((3 : ℝ) / 2 - δ)) (ht : N ^ 2 ≤ 2 * (4 * E + N) * t) :
    N ^ ((1 : ℝ) / 2 + δ) ≤ 10 * t := by
  have hN0 : 0 < N := by linarith
  have hA : 0 < N ^ ((3 : ℝ) / 2 - δ) := Real.rpow_pos_of_pos hN0 _
  have hN1 : N ≤ N ^ ((3 : ℝ) / 2 - δ) := by
    calc N = N ^ (1 : ℝ) := (Real.rpow_one N).symm
      _ ≤ N ^ ((3 : ℝ) / 2 - δ) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hsplit : N ^ 2 = N ^ ((1 : ℝ) / 2 + δ) * N ^ ((3 : ℝ) / 2 - δ) := by
    rw [← Real.rpow_add hN0, show (1 : ℝ) / 2 + δ + (3 / 2 - δ) = (2 : ℝ) by ring, Real.rpow_two]
  have ht0 : 0 ≤ t := by
    by_contra h
    push Not at h
    have : 2 * (4 * E + N) * t < 0 := mul_neg_of_pos_of_neg (by linarith) h
    linarith [sq_nonneg N]
  have key : N ^ ((1 : ℝ) / 2 + δ) * N ^ ((3 : ℝ) / 2 - δ) ≤ 10 * t * N ^ ((3 : ℝ) / 2 - δ) := by
    rw [← hsplit]
    calc N ^ 2 ≤ 2 * (4 * E + N) * t := ht
      _ ≤ 2 * (4 * N ^ ((3 : ℝ) / 2 - δ) + N ^ ((3 : ℝ) / 2 - δ)) * t := by
          apply mul_le_mul_of_nonneg_right _ ht0
          linarith
      _ = 10 * t * N ^ ((3 : ℝ) / 2 - δ) := by ring
  exact le_of_mul_le_mul_right key hA

-- N15
theorem dense_branch_arith (δ η K : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 8) (hη : 4 * δ ≤ η) (hK : 0 < K)
    (N M : ℝ) (hN : 1 ≤ N) (hM : 0 ≤ M) (hNM : N ^ (1 - 2 * δ) ≤ 8 * M) :
    K * (8 : ℝ) ^ (-((1 : ℝ) / 2 + η)) * N ^ ((1 : ℝ) / 2 + η / 2) ≤ K * M ^ ((1 : ℝ) / 2 + η) := by
  have hN0 : 0 < N := by linarith
  have hq : 0 ≤ (1 : ℝ) / 2 + η := by linarith
  have hB : 0 ≤ N ^ (1 - 2 * δ) := Real.rpow_nonneg hN0.le _
  have h1 : N ^ (1 - 2 * δ) / 8 ≤ M := by linarith
  have h2 : (N ^ (1 - 2 * δ) / 8) ^ ((1 : ℝ) / 2 + η) ≤ M ^ ((1 : ℝ) / 2 + η) :=
    Real.rpow_le_rpow (div_nonneg hB (by norm_num)) h1 hq
  have h3 : (N ^ (1 - 2 * δ) / 8) ^ ((1 : ℝ) / 2 + η)
      = (8 : ℝ) ^ (-((1 : ℝ) / 2 + η)) * N ^ ((1 - 2 * δ) * ((1 : ℝ) / 2 + η)) := by
    rw [Real.div_rpow hB (by norm_num : (0 : ℝ) ≤ 8), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 8),
      Real.rpow_mul hN0.le, div_eq_mul_inv]
    ring
  have h4 : N ^ ((1 : ℝ) / 2 + η / 2) ≤ N ^ ((1 - 2 * δ) * ((1 : ℝ) / 2 + η)) :=
    Real.rpow_le_rpow_of_exponent_le hN (by
      nlinarith [mul_nonneg (sub_nonneg.2 hη) (by linarith : (0 : ℝ) ≤ 1 / 2 - 2 * δ),
        mul_nonneg hδ.le (by linarith : (0 : ℝ) ≤ 1 - 8 * δ)])
  have h8 : 0 ≤ (8 : ℝ) ^ (-((1 : ℝ) / 2 + η)) := Real.rpow_nonneg (by norm_num) _
  calc K * (8 : ℝ) ^ (-((1 : ℝ) / 2 + η)) * N ^ ((1 : ℝ) / 2 + η / 2)
      ≤ K * (8 : ℝ) ^ (-((1 : ℝ) / 2 + η)) * N ^ ((1 - 2 * δ) * ((1 : ℝ) / 2 + η)) :=
        mul_le_mul_of_nonneg_left h4 (mul_nonneg hK.le h8)
    _ = K * (N ^ (1 - 2 * δ) / 8) ^ ((1 : ℝ) / 2 + η) := by rw [h3]; ring
    _ ≤ K * M ^ ((1 : ℝ) / 2 + η) := mul_le_mul_of_nonneg_left h2 hK.le

/-! ### The two branches of N16 -/

/-- Sparse branch of N16: few edges, so the Turán-type bound N10 with N14 gives a large
independent set. -/
theorem sparse_case (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (N : ℕ) (hN : 1 ≤ N)
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (hE : (G.edgeFinset.card : ℝ) ≤ (N : ℝ) ^ ((3 : ℝ) / 2 - δ)) :
    ∃ t : Finset (Fin N), G.IsIndepSet (t : Set (Fin N)) ∧
      (1 / 10 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 2 + δ) ≤ (t.card : ℝ) := by
  obtain ⟨t, htind, ht⟩ := turan_weak G
  rw [Fintype.card_fin] at ht
  have ht' : ((N ^ 2 : ℕ) : ℝ) ≤ ((2 * (4 * G.edgeFinset.card + N) * t.card : ℕ) : ℝ) := by
    exact_mod_cast ht
  push_cast at ht'
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have := sparse_branch_arith δ hδ hδ' N (G.edgeFinset.card) (t.card) hN1 (Nat.cast_nonneg _) hE ht'
  exact ⟨t, htind, by linarith⟩

/-- Dense branch of N16, assuming the open core N13 (as a hypothesis `h13`, with `κ = 1/2`):
a dense core `s` (N11) of minimum internal degree about `N^(1/2-δ)` has size at least about
`N^(1-2δ)` (N12), and N13 then gives an independent set of size `K₁ |s|^(1/2+η)`, which N15
converts into a power of `N`. -/
theorem dense_case (δ η K₁ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 8) (hη : 4 * δ ≤ η) (hK₁ : 0 < K₁)
    (h13 : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (s : Finset V),
        ¬ (SimpleGraph.cycleGraph 4).IsContained G →
        (∀ v ∈ s, (1 / 2 : ℝ) * (s.card : ℝ) ^ ((1 : ℝ) / 2 - δ) ≤ ((s.filter (G.Adj v)).card : ℝ)) →
        ∃ t ⊆ s, G.IsIndepSet (t : Set V) ∧ K₁ * (s.card : ℝ) ^ ((1 : ℝ) / 2 + η) ≤ (t.card : ℝ))
    (N : ℕ) (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (hG : ¬ (SimpleGraph.cycleGraph 4).IsContained G)
    (hN2 : (2 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - δ))
    (hE : (N : ℝ) ^ ((3 : ℝ) / 2 - δ) < (G.edgeFinset.card : ℝ)) :
    ∃ t : Finset (Fin N), G.IsIndepSet (t : Set (Fin N)) ∧
      K₁ * (8 : ℝ) ^ (-((1 : ℝ) / 2 + η)) * (N : ℝ) ^ ((1 : ℝ) / 2 + η / 2) ≤ (t.card : ℝ) := by
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h
      simp only [Nat.cast_zero] at hN2
      rw [Real.zero_rpow (by linarith : (0 : ℝ) < 1 / 2 - δ).ne'] at hN2
      linarith
    · exact h
  have : Nonempty (Fin N) := ⟨⟨0, hNpos⟩⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have hN0ne : (N : ℝ) ≠ 0 := by positivity
  set x : ℝ := (N : ℝ) ^ ((1 : ℝ) / 2 - δ) with hx
  have hx0 : 0 ≤ x := Real.rpow_nonneg (Nat.cast_nonneg _) _
  set d : ℕ := ⌊x⌋₊ with hd
  have hdx : (d : ℝ) ≤ x := Nat.floor_le hx0
  have hxd : x - 1 ≤ d := by
    have := Nat.lt_floor_add_one x
    linarith
  have hd2 : x / 2 ≤ d := by linarith
  have hdN : d * Fintype.card (Fin N) ≤ G.edgeFinset.card := by
    rw [Fintype.card_fin]
    have : ((d * N : ℕ) : ℝ) ≤ (G.edgeFinset.card : ℝ) := by
      push_cast
      calc (d : ℝ) * N ≤ x * N := mul_le_mul_of_nonneg_right hdx (Nat.cast_nonneg _)
        _ = (N : ℝ) ^ ((3 : ℝ) / 2 - δ) := by
            rw [hx, ← Real.rpow_add_one hN0ne]
            congr 1
            ring
        _ ≤ G.edgeFinset.card := hE.le
    exact_mod_cast this
  obtain ⟨s, hsne, hsmin⟩ := exists_dense_core G d hdN
  have hmoore := moore_bound_c4_free G hG s d hsne hsmin
  have hsN : s.card ≤ N := by simpa using Finset.card_le_univ s
  have hκ : ∀ v ∈ s, (1 / 2 : ℝ) * (s.card : ℝ) ^ ((1 : ℝ) / 2 - δ)
      ≤ ((s.filter (G.Adj v)).card : ℝ) := by
    intro v hv
    have h1 : (d : ℝ) ≤ ((s.filter (G.Adj v)).card : ℝ) := by exact_mod_cast hsmin v hv
    have h2 : (s.card : ℝ) ^ ((1 : ℝ) / 2 - δ) ≤ x := by
      rw [hx]
      exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hsN) (by linarith)
    linarith
  obtain ⟨t, -, htind, htcard⟩ := h13 (Fin N) G s hG hκ
  have hNM : (N : ℝ) ^ (1 - 2 * δ) ≤ 8 * s.card := by
    have hx2 : (N : ℝ) ^ (1 - 2 * δ) = x ^ 2 := by
      rw [show (1 : ℝ) - 2 * δ = ((1 : ℝ) / 2 - δ) * ((2 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_mul (Nat.cast_nonneg _), Real.rpow_natCast]
    have hm : ((d * d : ℕ) : ℝ) ≤ ((2 * s.card : ℕ) : ℝ) := by exact_mod_cast hmoore
    push_cast at hm
    rw [hx2]
    nlinarith [mul_nonneg (sub_nonneg.2 hd2) (by linarith : (0 : ℝ) ≤ d + x / 2), hm]
  have := dense_branch_arith δ η K₁ hδ hδ' hη hK₁ N s.card hN1 (Nat.cast_nonneg _) hNM
  exact ⟨t, htind, this.trans htcard⟩

-- N16 (proved modulo N13)
theorem c4_free_indep_power :
    ∃ ε K : ℝ, 0 < ε ∧ 0 < K ∧ ∀ (N : ℕ) (G : SimpleGraph (Fin N)) [DecidableRel G.Adj],
      ¬ (SimpleGraph.cycleGraph 4).IsContained G →
      ∃ t : Finset (Fin N), G.IsIndepSet (t : Set (Fin N)) ∧ K * (N : ℝ) ^ ((1 : ℝ) / 2 + ε) ≤ (t.card : ℝ) := by
  obtain ⟨δ, η, hδ, hδ', hη, h13⟩ := core_near_extremal
  obtain ⟨K₁, hK₁, h13'⟩ := h13 (1 / 2) (by norm_num)
  set K₂ : ℝ := K₁ * (8 : ℝ) ^ (-((1 : ℝ) / 2 + η)) with hK₂
  have hK₂pos : 0 < K₂ := mul_pos hK₁ (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨δ, min (1 / 256) K₂, hδ, lt_min (by norm_num) hK₂pos, ?_⟩
  intro N G _ hG
  have hKle1 : min (1 / 256 : ℝ) K₂ ≤ 1 / 256 := min_le_left _ _
  have hKle2 : min (1 / 256 : ℝ) K₂ ≤ K₂ := min_le_right _ _
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    refine ⟨∅, ?_, ?_⟩
    · rw [Finset.coe_empty]
      exact Set.pairwise_empty _
    · simp only [Nat.cast_zero, Finset.card_empty]
      rw [Real.zero_rpow (by positivity)]
      simp
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have h3 : 0 ≤ (N : ℝ) ^ ((1 : ℝ) / 2 + δ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  rcases Nat.lt_or_ge N 256 with hsmall | hbig
  · -- small `N`: a single vertex suffices
    refine ⟨{⟨0, hNpos⟩}, ?_, ?_⟩
    · rw [Finset.coe_singleton]
      exact Set.pairwise_singleton _ _
    · rw [Finset.card_singleton, Nat.cast_one]
      have h1 : (N : ℝ) ^ ((1 : ℝ) / 2 + δ) ≤ (N : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      rw [Real.rpow_one] at h1
      have h2 : (N : ℝ) ≤ 256 := by exact_mod_cast hsmall.le
      calc min (1 / 256 : ℝ) K₂ * (N : ℝ) ^ ((1 : ℝ) / 2 + δ)
          ≤ (1 / 256) * (N : ℝ) ^ ((1 : ℝ) / 2 + δ) := mul_le_mul_of_nonneg_right hKle1 h3
        _ ≤ (1 / 256) * 256 := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            linarith
        _ = 1 := by norm_num
  · -- large `N`
    have hN2 : (2 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - δ) := by
      have h256 : (256 : ℝ) ≤ N := by exact_mod_cast hbig
      have h8 : (256 : ℝ) ^ ((3 : ℝ) / 8) = 8 := by
        rw [show (256 : ℝ) = (2 : ℝ) ^ ((8 : ℕ) : ℝ) by rw [Real.rpow_natCast]; norm_num,
          ← Real.rpow_mul (by norm_num),
          show ((8 : ℕ) : ℝ) * ((3 : ℝ) / 8) = ((3 : ℕ) : ℝ) by push_cast; ring,
          Real.rpow_natCast]
        norm_num
      calc (2 : ℝ) ≤ 8 := by norm_num
        _ = (256 : ℝ) ^ ((3 : ℝ) / 8) := h8.symm
        _ ≤ (N : ℝ) ^ ((3 : ℝ) / 8) := Real.rpow_le_rpow (by norm_num) h256 (by norm_num)
        _ ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - δ) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    rcases le_or_gt (G.edgeFinset.card : ℝ) ((N : ℝ) ^ ((3 : ℝ) / 2 - δ)) with hE | hE
    · obtain ⟨t, htind, ht⟩ := sparse_case δ hδ (by linarith) N hNpos G hE
      refine ⟨t, htind, ?_⟩
      calc min (1 / 256 : ℝ) K₂ * (N : ℝ) ^ ((1 : ℝ) / 2 + δ)
          ≤ (1 / 256) * (N : ℝ) ^ ((1 : ℝ) / 2 + δ) := mul_le_mul_of_nonneg_right hKle1 h3
        _ ≤ (1 / 10) * (N : ℝ) ^ ((1 : ℝ) / 2 + δ) := mul_le_mul_of_nonneg_right (by norm_num) h3
        _ ≤ t.card := ht
    · obtain ⟨t, htind, ht⟩ := dense_case δ η K₁ hδ hδ' hη hK₁ h13' N G hG hN2 hE
      refine ⟨t, htind, ?_⟩
      have h4 : (N : ℝ) ^ ((1 : ℝ) / 2 + δ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 + η / 2) :=
        Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      calc min (1 / 256 : ℝ) K₂ * (N : ℝ) ^ ((1 : ℝ) / 2 + δ)
          ≤ K₂ * (N : ℝ) ^ ((1 : ℝ) / 2 + δ) := mul_le_mul_of_nonneg_right hKle2 h3
        _ ≤ K₂ * (N : ℝ) ^ ((1 : ℝ) / 2 + η / 2) := mul_le_mul_of_nonneg_left h4 hK₂pos.le
        _ ≤ t.card := ht

-- N17
theorem rpow_inversion (K ε N x : ℝ) (hK : 0 < K) (hε : 0 < ε) (hN : 0 ≤ N) (hx : 0 ≤ x)
    (h : K * N ^ ((1 : ℝ) / 2 + ε) ≤ x) :
    N ≤ K ^ (-(2 / (1 + 2 * ε))) * x ^ (2 - 4 * ε / (1 + 2 * ε)) := by
  have hden : (1 + 2 * ε) ≠ 0 := by positivity
  have hi : (1 + 2 * ε)⁻¹ * (1 + 2 * ε) = 1 := inv_mul_cancel₀ hden
  have hp0 : 0 ≤ 2 / (1 + 2 * ε) := by positivity
  have hexp : 2 - 4 * ε / (1 + 2 * ε) = 2 / (1 + 2 * ε) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    linear_combination (-2 : ℝ) * hi
  have hmul : ((1 : ℝ) / 2 + ε) * (2 / (1 + 2 * ε)) = 1 := by
    rw [div_eq_mul_inv]
    linear_combination hi
  have h1 : N ^ ((1 : ℝ) / 2 + ε) ≤ x / K := by
    rw [le_div_iff₀ hK]
    linarith [h]
  have h2 : N = (N ^ ((1 : ℝ) / 2 + ε)) ^ (2 / (1 + 2 * ε)) := by
    rw [← Real.rpow_mul hN, hmul, Real.rpow_one]
  rw [hexp]
  calc N = (N ^ ((1 : ℝ) / 2 + ε)) ^ (2 / (1 + 2 * ε)) := h2
    _ ≤ (x / K) ^ (2 / (1 + 2 * ε)) := Real.rpow_le_rpow (Real.rpow_nonneg hN _) h1 hp0
    _ = K ^ (-(2 / (1 + 2 * ε))) * x ^ (2 / (1 + 2 * ε)) := by
        rw [Real.div_rpow hx hK.le, Real.rpow_neg hK.le, div_eq_inv_mul]

-- N18 (proved modulo N13, through N16)
theorem card_le_power_of_c4_free :
    ∃ c C : ℝ, 0 < c ∧ c ≤ 2 ∧ 0 ≤ C ∧ ∀ (n N : ℕ) (G : SimpleGraph (Fin N)) [DecidableRel G.Adj], 1 ≤ n →
      ¬ (SimpleGraph.cycleGraph 4).IsContained G → G.IndepSetFree n → (N : ℝ) ≤ C * (n : ℝ) ^ (2 - c) := by
  obtain ⟨ε, K, hε, hK, hmain⟩ := c4_free_indep_power
  have hden : (0 : ℝ) < 1 + 2 * ε := by positivity
  have hc2 : 4 * ε / (1 + 2 * ε) ≤ 2 := by
    rw [div_le_iff₀ hden]
    linarith
  refine ⟨4 * ε / (1 + 2 * ε), K ^ (-(2 / (1 + 2 * ε))), by positivity, hc2,
    Real.rpow_nonneg hK.le _, ?_⟩
  intro n N G _ _ hG hα
  obtain ⟨t, htind, htcard⟩ := hmain N G hG
  have ht := card_lt_of_indepSetFree G hα htind
  have ht' : (t.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast ht.le
  have h1 := rpow_inversion K ε (N : ℝ) (t.card : ℝ) hK hε (Nat.cast_nonneg N) (Nat.cast_nonneg _)
    htcard
  calc (N : ℝ) ≤ K ^ (-(2 / (1 + 2 * ε))) * (t.card : ℝ) ^ (2 - 4 * ε / (1 + 2 * ε)) := h1
    _ ≤ K ^ (-(2 / (1 + 2 * ε))) * (n : ℝ) ^ (2 - 4 * ε / (1 + 2 * ε)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hK.le _)
        exact Real.rpow_le_rpow (Nat.cast_nonneg _) ht' (by linarith)

-- N19
theorem floor_succ_le_power (c C x : ℝ) (hc : c ≤ 2) (hC : 0 ≤ C) (n : ℕ) (hn : 1 ≤ n)
    (hx : x ≤ C * (n : ℝ) ^ (2 - c)) :
    ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ (C + 1) * (n : ℝ) ^ (2 - c) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : (1 : ℝ) ≤ (n : ℝ) ^ (2 - c) := Real.one_le_rpow hn' (by linarith)
  have hfloor : ((⌊x⌋₊ : ℕ) : ℝ) ≤ C * (n : ℝ) ^ (2 - c) := by
    rcases le_or_gt 0 x with h0 | h0
    · exact (Nat.floor_le h0).trans hx
    · rw [Nat.floor_of_nonpos h0.le]
      simp only [Nat.cast_zero]
      exact mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  push_cast
  linarith

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
  -- ROOT (proved modulo N13, through N18)
  obtain ⟨c, C, hc, hc2, hC, hmain⟩ := card_le_power_of_c4_free
  refine ⟨c, hc, C + 1, ?_⟩
  intro n hn
  have hR := graphRamsey_le_of_c4_free_bound n (⌊C * (n : ℝ) ^ (2 - c)⌋₊ + 1) (fun G hG hα => by
    classical
    have h1 := hmain n _ G hn hG hα
    have h2 := Nat.lt_floor_add_one (C * (n : ℝ) ^ (2 - c))
    push_cast at h1
    linarith)
  calc (SimpleGraph.graphRamsey (SimpleGraph.cycleGraph 4) (SimpleGraph.completeGraph (Fin n)) : ℝ)
      ≤ ((⌊C * (n : ℝ) ^ (2 - c)⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hR
    _ ≤ (C + 1) * (n : ℝ) ^ (2 - c) := floor_succ_le_power c C _ hc2 hC n hn le_rfl

end Erdos159
