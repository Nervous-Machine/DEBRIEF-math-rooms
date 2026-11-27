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

/-! ## N01 -/

theorem graphRamsey_le_of_forall {α β : Type*} [Fintype α] [Fintype β]
    (G : SimpleGraph α) (H : SimpleGraph β) (N : ℕ)
    (h : ∀ C : SimpleGraph (Fin N), G.IsContained C ∨ H.IsContained Cᶜ) :
    SimpleGraph.graphRamsey G H ≤ N := by
  unfold SimpleGraph.graphRamsey
  exact Nat.sInf_le h

/-! ## N02 -/

theorem complete_isContained_compl_iff {V : Type*} (C : SimpleGraph V) (n : ℕ) :
    (SimpleGraph.completeGraph (Fin n)).IsContained Cᶜ ↔ ¬ C.IndepSetFree n := by
  rw [← SimpleGraph.not_cliqueFree_iff_top_isContained, SimpleGraph.cliqueFree_compl]

/-! ## helper: a 4-cycle from four vertices -/

theorem c4_of_four {V : Type*} (G : SimpleGraph V) (x0 x1 x2 x3 : V)
    (h01 : G.Adj x0 x1) (h12 : G.Adj x1 x2) (h23 : G.Adj x2 x3) (h30 : G.Adj x3 x0)
    (n02 : x0 ≠ x2) (n13 : x1 ≠ x3) : (SimpleGraph.cycleGraph 4).IsContained G := by
  let f : Fin 4 → V := ![x0, x1, x2, x3]
  have e0 : f 0 = x0 := by first | rfl | simp [f]
  have e1 : f 1 = x1 := by first | rfl | simp [f]
  have e2 : f 2 = x2 := by first | rfl | simp [f]
  have e3 : f 3 = x3 := by first | rfl | simp [f]
  have n01 : x0 ≠ x1 := h01.ne
  have n12 : x1 ≠ x2 := h12.ne
  have n23 : x2 ≠ x3 := h23.ne
  have n30 : x3 ≠ x0 := h30.ne
  have hadjkey : ∀ i j : Fin 4, (SimpleGraph.cycleGraph 4).Adj i j →
      (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨
      (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨ (i = 3 ∧ j = 0) ∨ (i = 0 ∧ j = 3) := by
    first | decide | (simp only [SimpleGraph.cycleGraph_adj']; decide)
  have hnekey : ∀ i j : Fin 4, i ≠ j →
      (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨
      (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨ (i = 3 ∧ j = 0) ∨ (i = 0 ∧ j = 3) ∨
      (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨ (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) := by
    decide
  have hadj : ∀ i j : Fin 4, (SimpleGraph.cycleGraph 4).Adj i j → G.Adj (f i) (f j) := by
    intro i j hij
    rcases hadjkey i j hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [e0, e1]; exact h01
    · rw [e1, e0]; exact h01.symm
    · rw [e1, e2]; exact h12
    · rw [e2, e1]; exact h12.symm
    · rw [e2, e3]; exact h23
    · rw [e3, e2]; exact h23.symm
    · rw [e3, e0]; exact h30
    · rw [e0, e3]; exact h30.symm
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    rcases hnekey i j hne with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [e0, e1] at hij; exact n01 hij
    · rw [e1, e0] at hij; exact n01 hij.symm
    · rw [e1, e2] at hij; exact n12 hij
    · rw [e2, e1] at hij; exact n12 hij.symm
    · rw [e2, e3] at hij; exact n23 hij
    · rw [e3, e2] at hij; exact n23 hij.symm
    · rw [e3, e0] at hij; exact n30 hij
    · rw [e0, e3] at hij; exact n30 hij.symm
    · rw [e0, e2] at hij; exact n02 hij
    · rw [e2, e0] at hij; exact n02 hij.symm
    · rw [e1, e3] at hij; exact n13 hij
    · rw [e3, e1] at hij; exact n13 hij.symm
  exact ⟨⟨⟨f, fun {i j} h => hadj i j h⟩, hinj⟩⟩

/-! ## N03 -/

theorem c4_free_common_nbrs {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ¬ (SimpleGraph.cycleGraph 4).IsContained G) {u v : V} (huv : u ≠ v) :
    (G.neighborFinset u ∩ G.neighborFinset v).card ≤ 1 := by
  by_contra h
  have h' : 1 < (G.neighborFinset u ∩ G.neighborFinset v).card := not_le.mp h
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h'
  rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset] at ha hb
  exact hG (c4_of_four G u a v b ha.1 ha.2.symm hb.2 hb.1.symm huv hab)

/-! ## N04 -/

theorem c4_free_nbhd_local_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ¬ (SimpleGraph.cycleGraph 4).IsContained G) (v w : V) (hw : G.Adj v w) :
    ((G.neighborFinset v).filter (G.Adj w)).card ≤ 1 := by
  refine le_trans (Finset.card_le_card ?_) (c4_free_common_nbrs G hG hw.ne)
  intro x hx
  rw [Finset.mem_filter] at hx
  rw [Finset.mem_inter]
  refine ⟨hx.1, ?_⟩
  rw [SimpleGraph.mem_neighborFinset]
  exact hx.2

/-! ## N05 -/

theorem greedy_indep_local {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) (D : ℕ)
    (hD : ∀ v ∈ s, (s.filter (G.Adj v)).card ≤ D) :
    ∃ t ⊆ s, G.IsIndepSet (t : Set V) ∧ s.card ≤ (D + 1) * t.card := by
  have H : ∀ k, ∀ s : Finset V, s.card = k → (∀ v ∈ s, (s.filter (G.Adj v)).card ≤ D) →
      ∃ t ⊆ s, G.IsIndepSet (t : Set V) ∧ s.card ≤ (D + 1) * t.card := by
    intro k
    refine Nat.strong_induction_on k ?_
    intro k ih s hks hDs
    rcases s.eq_empty_or_nonempty with hs | ⟨v, hv⟩
    · subst hs
      exact ⟨∅, Finset.empty_subset _, (by first | simp | exact Set.pairwise_empty _), (by simp)⟩
    · have hs's : (s \ s.filter (G.Adj v)).erase v ⊆ s := fun x hx =>
        (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase hx)).1
      have hvs' : v ∉ (s \ s.filter (G.Adj v)).erase v := Finset.notMem_erase v _
      have hsub : s ⊆ insert v ((s \ s.filter (G.Adj v)).erase v ∪ s.filter (G.Adj v)) := by
        intro x hx
        by_cases hxv : x = v
        · rw [hxv]; exact Finset.mem_insert_self _ _
        · by_cases hxN : x ∈ s.filter (G.Adj v)
          · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hxN)
          · exact Finset.mem_insert_of_mem (Finset.mem_union_left _
              (Finset.mem_erase.mpr ⟨hxv, Finset.mem_sdiff.mpr ⟨hx, hxN⟩⟩))
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_insert_le v ((s \ s.filter (G.Adj v)).erase v ∪ s.filter (G.Adj v))
      have h3 := Finset.card_union_le ((s \ s.filter (G.Adj v)).erase v) (s.filter (G.Adj v))
      have h4 : (s.filter (G.Adj v)).card ≤ D := hDs v hv
      have hcard : s.card ≤ ((s \ s.filter (G.Adj v)).erase v).card + (D + 1) := by omega
      have hlt' : ((s \ s.filter (G.Adj v)).erase v).card < s.card :=
        Finset.card_lt_card ((Finset.ssubset_iff_of_subset hs's).mpr ⟨v, hv, hvs'⟩)
      have hlt : ((s \ s.filter (G.Adj v)).erase v).card < k := by omega
      obtain ⟨t', ht's', ht'i, ht'c⟩ := ih _ hlt ((s \ s.filter (G.Adj v)).erase v) rfl
        (fun x hx => le_trans (Finset.card_le_card (Finset.filter_subset_filter _ hs's))
          (hDs x (hs's hx)))
      have hvt' : v ∉ t' := fun h => hvs' (ht's' h)
      refine ⟨insert v t', Finset.insert_subset hv (ht's'.trans hs's), ?_, ?_⟩
      · rw [Finset.coe_insert]
        refine Set.Pairwise.insert ht'i ?_
        intro b hb _
        have hb' : b ∈ (s \ s.filter (G.Adj v)).erase v := ht's' (Finset.mem_coe.mp hb)
        have hbs : b ∈ s := hs's hb'
        have hbN : b ∉ s.filter (G.Adj v) := (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase hb')).2
        have hnadj : ¬ G.Adj v b := fun hadj => hbN (Finset.mem_filter.mpr ⟨hbs, hadj⟩)
        exact ⟨hnadj, fun hadj => hnadj hadj.symm⟩
      · rw [Finset.card_insert_of_notMem hvt']
        nlinarith [hcard, ht'c]
  exact H _ s rfl hD

/-! ## N06 -/

theorem degree_lt_of_c4_free_indepSetFree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ¬ (SimpleGraph.cycleGraph 4).IsContained G) {n : ℕ} (hα : G.IndepSetFree n) (v : V) :
    G.degree v < 2 * n := by
  obtain ⟨t, hts, hti, htc⟩ := greedy_indep_local G (G.neighborFinset v) 1
    (fun w hw => c4_free_nbhd_local_degree G hG v w (by rwa [SimpleGraph.mem_neighborFinset] at hw))
  by_contra hcon
  have hdeg : 2 * n ≤ (G.neighborFinset v).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]; omega
  have hn : n ≤ t.card := by omega
  obtain ⟨u, hut, huc⟩ := Finset.exists_subset_card_eq hn
  exact hα u ⟨Set.Pairwise.mono (Finset.coe_subset.mpr hut) hti, huc⟩

/-! ## N07 -/

theorem card_le_quadratic_of_c4_free {N n : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (hG : ¬ (SimpleGraph.cycleGraph 4).IsContained G) (hα : G.IndepSetFree n) :
    N ≤ 2 * n * n := by
  by_contra hN
  have hN' : 2 * n * n < N := not_le.mp hN
  obtain ⟨t, -, hti, htc⟩ := greedy_indep_local G (Finset.univ : Finset (Fin N)) (2 * n)
    (fun v _ => by
      have h1 := degree_lt_of_c4_free_indepSetFree G hG hα v
      have h2 : ((Finset.univ : Finset (Fin N)).filter (G.Adj v)).card ≤
          (G.neighborFinset v).card := by
        apply Finset.card_le_card
        intro x hx
        rw [SimpleGraph.mem_neighborFinset]
        exact (Finset.mem_filter.mp hx).2
      rw [SimpleGraph.card_neighborFinset_eq_degree] at h2
      omega)
  have hU : (Finset.univ : Finset (Fin N)).card = N := Finset.card_fin N
  rw [hU] at htc
  by_cases hT : n ≤ t.card
  · obtain ⟨u, hut, huc⟩ := Finset.exists_subset_card_eq hT
    exact hα u ⟨Set.Pairwise.mono (Finset.coe_subset.mpr hut) hti, huc⟩
  · have hT' : t.card + 1 ≤ n := by omega
    nlinarith [Nat.mul_le_mul (le_refl (2 * n + 1)) hT']

/-! ## N08 -/

theorem graphRamsey_le_of_c4_free_bound (n N : ℕ)
    (h : ∀ G : SimpleGraph (Fin N), ¬ (SimpleGraph.cycleGraph 4).IsContained G → ¬ G.IndepSetFree n) :
    SimpleGraph.graphRamsey (SimpleGraph.cycleGraph 4) (SimpleGraph.completeGraph (Fin n)) ≤ N := by
  apply graphRamsey_le_of_forall
  intro C
  by_cases hC : (SimpleGraph.cycleGraph 4).IsContained C
  · exact Or.inl hC
  · exact Or.inr ((complete_isContained_compl_iff C n).mpr (h C hC))

/-! ## N09 -/

theorem graphRamsey_c4_le_quadratic (n : ℕ) :
    SimpleGraph.graphRamsey (SimpleGraph.cycleGraph 4) (SimpleGraph.completeGraph (Fin n)) ≤ 2 * n * n + 1 := by
  apply graphRamsey_le_of_c4_free_bound
  intro G hG hα
  classical
  have := card_le_quadratic_of_c4_free G hG hα
  omega

/-! ## N10 -/

theorem turan_weak {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ t : Finset V, G.IsIndepSet (t : Set V) ∧
      Fintype.card V ^ 2 ≤ 2 * (4 * G.edgeFinset.card + Fintype.card V) * t.card := by
  rcases Nat.eq_zero_or_pos (Fintype.card V) with hN0 | hNpos
  · refine ⟨∅, (by first | simp | exact Set.pairwise_empty _), ?_⟩
    rw [hN0]; simp
  · obtain ⟨D, hD⟩ : ∃ D : ℕ, D = 4 * G.edgeFinset.card / Fintype.card V := ⟨_, rfl⟩
    have hDN : D * Fintype.card V ≤ 4 * G.edgeFinset.card := by
      rw [hD]; exact Nat.div_mul_le_self _ _
    have hA : (Finset.univ.filter
          (fun v => ¬ (Fintype.card V * G.degree v ≤ 4 * G.edgeFinset.card))).card *
        (4 * G.edgeFinset.card + 1) ≤ Fintype.card V * (2 * G.edgeFinset.card) := by
      have h1 := Finset.card_nsmul_le_sum (Finset.univ.filter
          (fun v => ¬ (Fintype.card V * G.degree v ≤ 4 * G.edgeFinset.card)))
        (fun v => Fintype.card V * G.degree v) (4 * G.edgeFinset.card + 1)
        (fun v hv => not_le.mp (Finset.mem_filter.mp hv).2)
      rw [smul_eq_mul] at h1
      have h2 : ∑ v ∈ Finset.univ.filter
            (fun v => ¬ (Fintype.card V * G.degree v ≤ 4 * G.edgeFinset.card)),
            Fintype.card V * G.degree v ≤ ∑ v, Fintype.card V * G.degree v :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      have h3 : ∑ v, Fintype.card V * G.degree v = Fintype.card V * (2 * G.edgeFinset.card) := by
        rw [← Finset.mul_sum, SimpleGraph.sum_degrees_eq_twice_card_edges]
      exact le_trans h1 (le_trans h2 (le_of_eq h3))
    have hsc : 2 * (Finset.univ.filter
        (fun v => ¬ (Fintype.card V * G.degree v ≤ 4 * G.edgeFinset.card))).card ≤
        Fintype.card V := by
      nlinarith [Nat.zero_le G.edgeFinset.card]
    have hpart : (Finset.univ.filter
          (fun v => Fintype.card V * G.degree v ≤ 4 * G.edgeFinset.card)).card +
        (Finset.univ.filter
          (fun v => ¬ (Fintype.card V * G.degree v ≤ 4 * G.edgeFinset.card))).card =
        (Finset.univ : Finset V).card :=
      Finset.card_filter_add_card_filter_not _
    rw [Finset.card_univ] at hpart
    obtain ⟨t, -, hti, htc⟩ := greedy_indep_local G
      (Finset.univ.filter (fun v => Fintype.card V * G.degree v ≤ 4 * G.edgeFinset.card)) D
      (fun v hv => by
        have hv' : Fintype.card V * G.degree v ≤ 4 * G.edgeFinset.card :=
          (Finset.mem_filter.mp hv).2
        have h1 : ((Finset.univ.filter
            (fun v => Fintype.card V * G.degree v ≤ 4 * G.edgeFinset.card)).filter
              (G.Adj v)).card ≤ G.degree v := by
          rw [← SimpleGraph.card_neighborFinset_eq_degree]
          apply Finset.card_le_card
          intro x hx
          rw [SimpleGraph.mem_neighborFinset]
          exact (Finset.mem_filter.mp hx).2
        have h2 : G.degree v ≤ D := by
          rw [hD, Nat.le_div_iff_mul_le hNpos]
          first
            | linarith
            | (rw [Nat.mul_comm]; exact hv')
            | nlinarith [hv']
        exact le_trans h1 h2)
    refine ⟨t, hti, ?_⟩
    have hNs : Fintype.card V ≤ 2 * (Finset.univ.filter
        (fun v => Fintype.card V * G.degree v ≤ 4 * G.edgeFinset.card)).card := by
      omega
    rw [sq]
    nlinarith [Nat.mul_le_mul (le_refl (Fintype.card V)) hNs,
      Nat.mul_le_mul (le_refl (Fintype.card V)) htc, Nat.mul_le_mul hDN (le_refl t.card)]

/-! ## N11 -/

theorem exists_dense_core {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
    (hd : d * Fintype.card V ≤ G.edgeFinset.card) :
    ∃ s : Finset V, s.Nonempty ∧ ∀ v ∈ s, d ≤ (s.filter (G.Adj v)).card := by
  have key : ∀ k, ∀ s : Finset V, s.card = k → s.Nonempty →
      2 * d * s.card ≤ ∑ w ∈ s, (s.filter (G.Adj w)).card →
      ∃ s : Finset V, s.Nonempty ∧ ∀ v ∈ s, d ≤ (s.filter (G.Adj v)).card := by
    intro k
    refine Nat.strong_induction_on k ?_
    intro k ih s hks hsne hsum
    by_cases hall : ∀ v ∈ s, d ≤ (s.filter (G.Adj v)).card
    · exact ⟨s, hsne, hall⟩
    · push Not at hall
      obtain ⟨v, hv, hvd⟩ := hall
      have h1 : (s.filter (G.Adj v)).card + ∑ w ∈ s.erase v, (s.filter (G.Adj w)).card
          = ∑ w ∈ s, (s.filter (G.Adj w)).card :=
        Finset.add_sum_erase s (fun w => (s.filter (G.Adj w)).card) hv
      have h2 : ∀ w ∈ s.erase v, (s.filter (G.Adj w)).card ≤
          ((s.erase v).filter (G.Adj w)).card + (if G.Adj v w then 1 else 0) := by
        intro w _
        by_cases hvw : G.Adj v w
        · rw [if_pos hvw]
          have hsub : s.filter (G.Adj w) ⊆ insert v ((s.erase v).filter (G.Adj w)) := by
            intro x hx
            rw [Finset.mem_filter] at hx
            by_cases hxv : x = v
            · rw [hxv]; exact Finset.mem_insert_self _ _
            · exact Finset.mem_insert_of_mem
                (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hxv, hx.1⟩, hx.2⟩)
          exact le_trans (Finset.card_le_card hsub) (Finset.card_insert_le _ _)
        · rw [if_neg hvw, Nat.add_zero]
          apply Finset.card_le_card
          intro x hx
          rw [Finset.mem_filter] at hx
          have hxv : x ≠ v := by
            rintro rfl
            exact hvw hx.2.symm
          exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hxv, hx.1⟩, hx.2⟩
      have h3 : ∑ w ∈ s.erase v, (s.filter (G.Adj w)).card ≤
          ∑ w ∈ s.erase v, (((s.erase v).filter (G.Adj w)).card + (if G.Adj v w then 1 else 0)) :=
        Finset.sum_le_sum h2
      have h4 : ∑ w ∈ s.erase v, (((s.erase v).filter (G.Adj w)).card + (if G.Adj v w then 1 else 0))
          = ∑ w ∈ s.erase v, ((s.erase v).filter (G.Adj w)).card +
            ((s.erase v).filter (G.Adj v)).card := by
        rw [Finset.sum_add_distrib]
        congr 1
        first
          | exact (Finset.card_filter (G.Adj v) (s.erase v)).symm
          | simp
          | rw [Finset.sum_boole]; rfl
      have h5 : ((s.erase v).filter (G.Adj v)).card ≤ (s.filter (G.Adj v)).card :=
        Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset v s))
      have hcard : (s.erase v).card + 1 = s.card := Finset.card_erase_add_one hv
      have hlt : (s.erase v).card < k := by omega
      rw [← hcard] at hsum
      have hsum' : 2 * d * (s.erase v).card <
          ∑ w ∈ s.erase v, ((s.erase v).filter (G.Adj w)).card := by
        first | linarith | nlinarith
      have hne : (s.erase v).Nonempty := by
        rcases (s.erase v).eq_empty_or_nonempty with h | h
        · rw [h] at hsum'; simp at hsum'
        · exact h
      exact ih _ hlt (s.erase v) rfl hne hsum'.le
  have hdeg : ∀ v, G.degree v ≤ (Finset.univ.filter (G.Adj v)).card := by
    intro v
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    apply Finset.card_le_card
    intro x hx
    rw [SimpleGraph.mem_neighborFinset] at hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
  have h1 : ∑ v, G.degree v ≤ ∑ v, (Finset.univ.filter (G.Adj v)).card :=
    Finset.sum_le_sum (fun v _ => hdeg v)
  have h2 := SimpleGraph.sum_degrees_eq_twice_card_edges G
  have hS : 2 * d * (Finset.univ : Finset V).card ≤
      ∑ w ∈ (Finset.univ : Finset V), ((Finset.univ : Finset V).filter (G.Adj w)).card := by
    rw [Finset.card_univ]
    first | linarith | nlinarith
  exact key _ Finset.univ rfl Finset.univ_nonempty hS

/-! ## N12 -/

theorem moore_bound_c4_free {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ¬ (SimpleGraph.cycleGraph 4).IsContained G) (s : Finset V) (d : ℕ) (hs : s.Nonempty)
    (hmin : ∀ v ∈ s, d ≤ (s.filter (G.Adj v)).card) :
    d * d ≤ 2 * s.card := by
  obtain ⟨v, hv⟩ := hs
  have hdA : d ≤ (s.filter (G.Adj v)).card := hmin v hv
  have hdisj : ((s.filter (G.Adj v) : Finset V) : Set V).PairwiseDisjoint
      (fun a => (s.filter (G.Adj a)).erase v) := by
    intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_filter] at ha hb
    show Disjoint ((s.filter (G.Adj a)).erase v) ((s.filter (G.Adj b)).erase v)
    rw [Finset.disjoint_left]
    intro x hxa hxb
    rw [Finset.mem_erase, Finset.mem_filter] at hxa hxb
    have hsub : ({v, x} : Finset V) ⊆ G.neighborFinset a ∩ G.neighborFinset b := by
      intro y hy
      rw [Finset.mem_insert, Finset.mem_singleton] at hy
      rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset]
      rcases hy with hy | hy
      · rw [hy]; exact ⟨ha.2.symm, hb.2.symm⟩
      · rw [hy]; exact ⟨hxa.2.2, hxb.2.2⟩
    have h2 : ({v, x} : Finset V).card = 2 := Finset.card_pair (Ne.symm hxa.1)
    have h3 := Finset.card_le_card hsub
    have h4 := c4_free_common_nbrs G hG hab
    omega
  have hU : (s.filter (G.Adj v)).biUnion (fun a => (s.filter (G.Adj a)).erase v) ⊆ s := by
    rw [Finset.biUnion_subset]
    intro a _ x hx
    exact (Finset.mem_filter.mp (Finset.mem_of_mem_erase hx)).1
  have hcardU : ((s.filter (G.Adj v)).biUnion (fun a => (s.filter (G.Adj a)).erase v)).card =
      ∑ a ∈ s.filter (G.Adj v), ((s.filter (G.Adj a)).erase v).card :=
    Finset.card_biUnion hdisj
  have hle := Finset.card_le_card hU
  have hlow : ∀ a ∈ s.filter (G.Adj v), d ≤ ((s.filter (G.Adj a)).erase v).card + 1 := by
    intro a ha
    have e1 := hmin a (Finset.mem_filter.mp ha).1
    have e2 := Finset.pred_card_le_card_erase (s := s.filter (G.Adj a)) (a := v)
    omega
  have hsum := Finset.card_nsmul_le_sum (s.filter (G.Adj v))
    (fun a => ((s.filter (G.Adj a)).erase v).card + 1) d hlow
  rw [smul_eq_mul, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one] at hsum
  have hAs : (s.filter (G.Adj v)).card ≤ s.card := Finset.card_le_card (Finset.filter_subset _ _)
  nlinarith [Nat.mul_le_mul hdA (le_refl d)]

/-! ## N13 (the open core; not proved) -/

theorem core_near_extremal :
    ∃ δ η : ℝ, 0 < δ ∧ δ ≤ 1 / 8 ∧ 4 * δ ≤ η ∧ ∀ κ : ℝ, 0 < κ → ∃ K : ℝ, 0 < K ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V),
        ¬ (SimpleGraph.cycleGraph 4).IsContained G →
        (∀ v ∈ s, κ * (s.card : ℝ) ^ ((1 : ℝ) / 2 - δ) ≤ ((s.filter (G.Adj v)).card : ℝ)) →
        ∃ t ⊆ s, G.IsIndepSet (t : Set V) ∧ K * (s.card : ℝ) ^ ((1 : ℝ) / 2 + η) ≤ (t.card : ℝ) := by
  sorry

/-! ## N14 -/

theorem sparse_branch_arith (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (N E t : ℝ) (hN : 1 ≤ N)
    (hE0 : 0 ≤ E) (hE : E ≤ N ^ ((3 : ℝ) / 2 - δ)) (ht : N ^ 2 ≤ 2 * (4 * E + N) * t) :
    N ^ ((1 : ℝ) / 2 + δ) ≤ 10 * t := by
  have hN0 : 0 < N := by linarith
  have hb : 0 < N ^ ((3 : ℝ) / 2 - δ) := Real.rpow_pos_of_pos hN0 _
  have hNb : N ≤ N ^ ((3 : ℝ) / 2 - δ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hN (show (1 : ℝ) ≤ 3 / 2 - δ by linarith)
    rwa [Real.rpow_one] at h
  have hprod : N ^ ((1 : ℝ) / 2 + δ) * N ^ ((3 : ℝ) / 2 - δ) = N ^ 2 := by
    rw [← Real.rpow_add hN0]
    have h : (1 : ℝ) / 2 + δ + (3 / 2 - δ) = 2 := by ring
    rw [h, Real.rpow_two]
  have ht0 : 0 ≤ t := by
    rcases le_or_gt 0 t with h | h
    · exact h
    · exfalso
      have h' : 2 * (4 * E + N) * t < 0 := mul_neg_of_pos_of_neg (by linarith) h
      nlinarith [sq_nonneg N]
  have key : N ^ ((1 : ℝ) / 2 + δ) * N ^ ((3 : ℝ) / 2 - δ) ≤
      (10 * t) * N ^ ((3 : ℝ) / 2 - δ) := by
    rw [hprod]
    nlinarith [mul_le_mul_of_nonneg_right hE ht0, mul_le_mul_of_nonneg_right hNb ht0]
  exact le_of_mul_le_mul_right key hb

/-! ## N15 -/

theorem dense_branch_arith (δ η K : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 8) (hη : 4 * δ ≤ η) (hK : 0 < K)
    (N M : ℝ) (hN : 1 ≤ N) (hM : 0 ≤ M) (hNM : N ^ (1 - 2 * δ) ≤ 8 * M) :
    K * (8 : ℝ) ^ (-((1 : ℝ) / 2 + η)) * N ^ ((1 : ℝ) / 2 + η / 2) ≤ K * M ^ ((1 : ℝ) / 2 + η) := by
  have hN0 : 0 < N := by linarith
  have hp : 0 ≤ (1 : ℝ) / 2 + η := by linarith
  have hexp : (1 : ℝ) / 2 + η / 2 ≤ (1 - 2 * δ) * ((1 : ℝ) / 2 + η) := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ η - 4 * δ by linarith)
        (show (0 : ℝ) ≤ 1 / 2 - 2 * δ by linarith),
      mul_nonneg hδ.le (show (0 : ℝ) ≤ 1 - 8 * δ by linarith)]
  have h1 : N ^ ((1 : ℝ) / 2 + η / 2) ≤ N ^ ((1 - 2 * δ) * ((1 : ℝ) / 2 + η)) :=
    Real.rpow_le_rpow_of_exponent_le hN hexp
  have h2 : N ^ ((1 - 2 * δ) * ((1 : ℝ) / 2 + η)) = (N ^ (1 - 2 * δ)) ^ ((1 : ℝ) / 2 + η) :=
    Real.rpow_mul hN0.le _ _
  have h3 : (N ^ (1 - 2 * δ)) ^ ((1 : ℝ) / 2 + η) ≤ (8 * M) ^ ((1 : ℝ) / 2 + η) :=
    Real.rpow_le_rpow (Real.rpow_nonneg hN0.le _) hNM hp
  have h4 : (8 * M) ^ ((1 : ℝ) / 2 + η) = (8 : ℝ) ^ ((1 : ℝ) / 2 + η) * M ^ ((1 : ℝ) / 2 + η) :=
    Real.mul_rpow (by norm_num) hM
  have h5 : (8 : ℝ) ^ (-((1 : ℝ) / 2 + η)) = ((8 : ℝ) ^ ((1 : ℝ) / 2 + η))⁻¹ :=
    Real.rpow_neg (by norm_num) _
  have h8pos : 0 < (8 : ℝ) ^ ((1 : ℝ) / 2 + η) := Real.rpow_pos_of_pos (by norm_num) _
  have hchain : N ^ ((1 : ℝ) / 2 + η / 2) ≤
      (8 : ℝ) ^ ((1 : ℝ) / 2 + η) * M ^ ((1 : ℝ) / 2 + η) := by
    rw [← h4]
    rw [h2] at h1
    exact le_trans h1 h3
  have hinv : ((8 : ℝ) ^ ((1 : ℝ) / 2 + η))⁻¹ * N ^ ((1 : ℝ) / 2 + η / 2) ≤
      M ^ ((1 : ℝ) / 2 + η) := by
    rw [inv_mul_le_iff₀ h8pos]
    exact hchain
  rw [h5, mul_assoc]
  exact mul_le_mul_of_nonneg_left hinv hK.le

/-! ## N16 -/

theorem c4_free_indep_power :
    ∃ ε K : ℝ, 0 < ε ∧ 0 < K ∧ ∀ (N : ℕ) (G : SimpleGraph (Fin N)) [DecidableRel G.Adj],
      ¬ (SimpleGraph.cycleGraph 4).IsContained G →
      ∃ t : Finset (Fin N), G.IsIndepSet (t : Set (Fin N)) ∧ K * (N : ℝ) ^ ((1 : ℝ) / 2 + ε) ≤ (t.card : ℝ) := by
  obtain ⟨δ, η, hδ, hδ8, hδη, hcore⟩ := core_near_extremal
  obtain ⟨K₀, hK₀, hcoreK⟩ := hcore (1 / 2) (by norm_num)
  have hK₁pos : 0 < K₀ * (8 : ℝ) ^ (-((1 : ℝ) / 2 + η)) :=
    mul_pos hK₀ (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨δ, min (1 / 10) (K₀ * (8 : ℝ) ^ (-((1 : ℝ) / 2 + η))), hδ,
    lt_min (by norm_num) hK₁pos, ?_⟩
  intro N G _ hG
  have hexp0 : ((1 : ℝ) / 2 + δ) ≠ 0 := (by linarith : (0 : ℝ) < 1 / 2 + δ).ne'
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · refine ⟨∅, (by first | simp | exact Set.pairwise_empty _), ?_⟩
    have hNr : (N : ℝ) = 0 := by exact_mod_cast hN0
    rw [hNr, Real.zero_rpow hexp0, mul_zero]
    exact Nat.cast_nonneg _
  · have hNpos1 : 1 ≤ N := hNpos
    have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNpos1
    have hN0r : (0 : ℝ) < (N : ℝ) := by linarith
    by_cases hsp : (G.edgeFinset.card : ℝ) ≤ (N : ℝ) ^ ((3 : ℝ) / 2 - δ)
    · -- sparse branch
      obtain ⟨t, hti, htc⟩ := turan_weak G
      rw [Fintype.card_fin] at htc
      have htc' : (N : ℝ) ^ 2 ≤ 2 * (4 * (G.edgeFinset.card : ℝ) + (N : ℝ)) * (t.card : ℝ) := by
        exact_mod_cast htc
      have h1 := sparse_branch_arith δ hδ (by linarith) (N : ℝ) (G.edgeFinset.card : ℝ)
        (t.card : ℝ) hNr (Nat.cast_nonneg _) hsp htc'
      refine ⟨t, hti, ?_⟩
      have hmin : min (1 / 10) (K₀ * (8 : ℝ) ^ (-((1 : ℝ) / 2 + η))) ≤ 1 / 10 := min_le_left _ _
      have hpow0 : 0 ≤ (N : ℝ) ^ ((1 : ℝ) / 2 + δ) := Real.rpow_nonneg hN0r.le _
      first
        | linarith [mul_le_mul_of_nonneg_right hmin hpow0]
        | nlinarith [mul_le_mul_of_nonneg_right hmin hpow0]
    · -- dense branch
      have hEgt : (N : ℝ) ^ ((3 : ℝ) / 2 - δ) < (G.edgeFinset.card : ℝ) := not_le.mp hsp
      obtain ⟨y, hy⟩ : ∃ y : ℝ, y = (N : ℝ) ^ ((1 : ℝ) / 2 - δ) := ⟨_, rfl⟩
      have hy1 : (1 : ℝ) ≤ y := by rw [hy]; exact Real.one_le_rpow hNr (by linarith)
      have hy0 : (0 : ℝ) ≤ y := by linarith
      obtain ⟨d, hd⟩ : ∃ d : ℕ, d = ⌊y⌋₊ := ⟨_, rfl⟩
      have hd1 : (d : ℝ) ≤ y := by rw [hd]; exact Nat.floor_le hy0
      have hd2 : y < (d : ℝ) + 1 := by rw [hd]; exact Nat.lt_floor_add_one y
      have hdpos : 1 ≤ d := by rw [hd]; exact (Nat.one_le_floor_iff y).mpr hy1
      have hdpos' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdpos
      have hy2d : y ≤ 2 * (d : ℝ) := by linarith
      have hyN : y * (N : ℝ) = (N : ℝ) ^ ((3 : ℝ) / 2 - δ) := by
        rw [hy]
        have h : (3 : ℝ) / 2 - δ = ((1 : ℝ) / 2 - δ) + 1 := by ring
        rw [h, Real.rpow_add hN0r, Real.rpow_one]
      have hdE : d * Fintype.card (Fin N) ≤ G.edgeFinset.card := by
        rw [Fintype.card_fin]
        have h : (d : ℝ) * (N : ℝ) ≤ (G.edgeFinset.card : ℝ) := by
          have h' := mul_le_mul_of_nonneg_right hd1 hN0r.le
          linarith
        exact_mod_cast h
      haveI : Nonempty (Fin N) := ⟨⟨0, hNpos⟩⟩
      obtain ⟨s, hsne, hsmin⟩ := exists_dense_core G d hdE
      have hmoore := moore_bound_c4_free G hG s d hsne hsmin
      have hsN : s.card ≤ N := by
        have h := Finset.card_le_univ s
        rwa [Fintype.card_fin] at h
      have hsNr : (s.card : ℝ) ≤ (N : ℝ) := by exact_mod_cast hsN
      have hmoore' : (d : ℝ) * (d : ℝ) ≤ 2 * (s.card : ℝ) := by exact_mod_cast hmoore
      have hspow : (s.card : ℝ) ^ ((1 : ℝ) / 2 - δ) ≤ y := by
        rw [hy]
        exact Real.rpow_le_rpow (Nat.cast_nonneg _) hsNr (by linarith)
      have hcond : ∀ v ∈ s, (1 / 2 : ℝ) * (s.card : ℝ) ^ ((1 : ℝ) / 2 - δ) ≤
          ((s.filter (G.Adj v)).card : ℝ) := by
        intro v hv
        have h1 : (d : ℝ) ≤ ((s.filter (G.Adj v)).card : ℝ) := by exact_mod_cast hsmin v hv
        linarith
      obtain ⟨t, -, hti, htK⟩ := hcoreK (Fin N) G s hG hcond
      have hNM : (N : ℝ) ^ (1 - 2 * δ) ≤ 8 * (s.card : ℝ) := by
        have hy2 : y ^ 2 = (N : ℝ) ^ (1 - 2 * δ) := by
          rw [hy, ← Real.rpow_two, ← Real.rpow_mul hN0r.le]
          congr 1
          ring
        rw [← hy2]
        first
          | linarith [mul_le_mul hy2d hy2d hy0 (by linarith : (0 : ℝ) ≤ 2 * (d : ℝ))]
          | nlinarith [mul_le_mul hy2d hy2d hy0 (by linarith : (0 : ℝ) ≤ 2 * (d : ℝ))]
      have h15 := dense_branch_arith δ η K₀ hδ hδ8 hδη hK₀ (N : ℝ) (s.card : ℝ) hNr
        (Nat.cast_nonneg _) hNM
      have hexpmono : (N : ℝ) ^ ((1 : ℝ) / 2 + δ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 + η / 2) :=
        Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
      refine ⟨t, hti, ?_⟩
      have hmin : min (1 / 10) (K₀ * (8 : ℝ) ^ (-((1 : ℝ) / 2 + η))) ≤
          K₀ * (8 : ℝ) ^ (-((1 : ℝ) / 2 + η)) := min_le_right _ _
      have hpow0 : 0 ≤ (N : ℝ) ^ ((1 : ℝ) / 2 + δ) := Real.rpow_nonneg hN0r.le _
      calc min (1 / 10) (K₀ * (8 : ℝ) ^ (-((1 : ℝ) / 2 + η))) * (N : ℝ) ^ ((1 : ℝ) / 2 + δ)
          ≤ K₀ * (8 : ℝ) ^ (-((1 : ℝ) / 2 + η)) * (N : ℝ) ^ ((1 : ℝ) / 2 + δ) :=
            mul_le_mul_of_nonneg_right hmin hpow0
        _ ≤ K₀ * (8 : ℝ) ^ (-((1 : ℝ) / 2 + η)) * (N : ℝ) ^ ((1 : ℝ) / 2 + η / 2) :=
            mul_le_mul_of_nonneg_left hexpmono hK₁pos.le
        _ ≤ K₀ * (s.card : ℝ) ^ ((1 : ℝ) / 2 + η) := h15
        _ ≤ (t.card : ℝ) := htK

/-! ## N17 -/

theorem rpow_inversion (K ε N x : ℝ) (hK : 0 < K) (hε : 0 < ε) (hN : 0 ≤ N) (hx : 0 ≤ x)
    (h : K * N ^ ((1 : ℝ) / 2 + ε) ≤ x) :
    N ≤ K ^ (-(2 / (1 + 2 * ε))) * x ^ (2 - 4 * ε / (1 + 2 * ε)) := by
  have hpos : 0 < 1 + 2 * ε := by linarith
  have hne : 1 + 2 * ε ≠ 0 := hpos.ne'
  have hq : (2 : ℝ) - 4 * ε / (1 + 2 * ε) = 2 / (1 + 2 * ε) := by
    rw [eq_div_iff hne, sub_mul, div_mul_cancel₀ (4 * ε) hne]
    ring
  have hq0 : 0 ≤ 2 / (1 + 2 * ε) := div_nonneg (by norm_num) hpos.le
  have hpq : ((1 : ℝ) / 2 + ε) * (2 / (1 + 2 * ε)) = 1 := by
    rw [← mul_div_assoc, div_eq_one_iff_eq hne]
    ring
  rw [hq]
  have h1 : N ^ ((1 : ℝ) / 2 + ε) ≤ x / K := by
    rw [le_div_iff₀ hK]
    first
      | (rw [mul_comm]; exact h)
      | linarith
  have h2 : (N ^ ((1 : ℝ) / 2 + ε)) ^ (2 / (1 + 2 * ε)) ≤ (x / K) ^ (2 / (1 + 2 * ε)) :=
    Real.rpow_le_rpow (Real.rpow_nonneg hN _) h1 hq0
  rw [← Real.rpow_mul hN, hpq, Real.rpow_one, Real.div_rpow hx hK.le] at h2
  rw [Real.rpow_neg hK.le]
  calc N ≤ x ^ (2 / (1 + 2 * ε)) / K ^ (2 / (1 + 2 * ε)) := h2
    _ = (K ^ (2 / (1 + 2 * ε)))⁻¹ * x ^ (2 / (1 + 2 * ε)) := by ring

/-! ## N18 -/

theorem card_le_power_of_c4_free :
    ∃ c C : ℝ, 0 < c ∧ c ≤ 2 ∧ 0 ≤ C ∧ ∀ (n N : ℕ) (G : SimpleGraph (Fin N)) [DecidableRel G.Adj], 1 ≤ n →
      ¬ (SimpleGraph.cycleGraph 4).IsContained G → G.IndepSetFree n → (N : ℝ) ≤ C * (n : ℝ) ^ (2 - c) := by
  obtain ⟨ε, K, hε, hK, hmain⟩ := c4_free_indep_power
  have hpos : 0 < 1 + 2 * ε := by linarith
  refine ⟨4 * ε / (1 + 2 * ε), K ^ (-(2 / (1 + 2 * ε))), div_pos (by linarith) hpos, ?_,
    Real.rpow_nonneg hK.le _, ?_⟩
  · rw [div_le_iff₀ hpos]
    linarith
  · intro n N G _ _ hG hα
    obtain ⟨t, hti, htK⟩ := hmain N G hG
    have htn : t.card < n := by
      by_contra hcon
      obtain ⟨u, hut, huc⟩ := Finset.exists_subset_card_eq (not_lt.mp hcon)
      exact hα u ⟨Set.Pairwise.mono (Finset.coe_subset.mpr hut) hti, huc⟩
    have htn' : (t.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast htn.le
    exact rpow_inversion K ε N n hK hε (Nat.cast_nonneg N) (Nat.cast_nonneg n) (le_trans htK htn')

/-! ## N19 -/

theorem floor_succ_le_power (c C x : ℝ) (hc : c ≤ 2) (hC : 0 ≤ C) (n : ℕ) (hn : 1 ≤ n)
    (hx : x ≤ C * (n : ℝ) ^ (2 - c)) :
    ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ (C + 1) * (n : ℝ) ^ (2 - c) := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hp : 1 ≤ (n : ℝ) ^ (2 - c) := Real.one_le_rpow hn' (by linarith)
  have hCp : 0 ≤ C * (n : ℝ) ^ (2 - c) := mul_nonneg hC (by linarith)
  rw [Nat.cast_add, Nat.cast_one]
  rcases le_or_gt 0 x with h0 | h0
  · have hfl : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le h0
    nlinarith
  · have hfl : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
    rw [hfl, Nat.cast_zero]
    nlinarith

/-! ## ROOT -/

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
  obtain ⟨c, C, hc, hc2, hC, hmain⟩ := card_le_power_of_c4_free
  refine ⟨c, hc, C + 1, ?_⟩
  intro n hn
  have hR := graphRamsey_le_of_c4_free_bound n (⌊C * (n : ℝ) ^ (2 - c)⌋₊ + 1) (by
    intro G hG hα
    classical
    have h1 := hmain n _ G hn hG hα
    have h2 := Nat.lt_floor_add_one (C * (n : ℝ) ^ (2 - c))
    push_cast at h1
    linarith)
  calc (SimpleGraph.graphRamsey (SimpleGraph.cycleGraph 4)
        (SimpleGraph.completeGraph (Fin n)) : ℝ)
      ≤ ((⌊C * (n : ℝ) ^ (2 - c)⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hR
    _ ≤ (C + 1) * (n : ℝ) ^ (2 - c) := floor_succ_le_power c C _ hc2 hC n hn le_rfl

end Erdos159
