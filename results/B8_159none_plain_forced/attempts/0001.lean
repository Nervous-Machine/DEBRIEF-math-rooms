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

/-! ### N01 -/

theorem graphRamsey_le_of_forall {α β : Type*} [Fintype α] [Fintype β]
    (G : SimpleGraph α) (H : SimpleGraph β) (N : ℕ)
    (h : ∀ C : SimpleGraph (Fin N), G.IsContained C ∨ H.IsContained Cᶜ) :
    SimpleGraph.graphRamsey G H ≤ N := by
  unfold SimpleGraph.graphRamsey
  exact Nat.sInf_le
    (show N ∈ {n : ℕ | ∀ C : SimpleGraph (Fin n), G.IsContained C ∨ H.IsContained Cᶜ} from h)

/-! ### N02 -/

theorem complete_isContained_compl_iff {V : Type*} (C : SimpleGraph V) (n : ℕ) :
    (SimpleGraph.completeGraph (Fin n)).IsContained Cᶜ ↔ ¬ C.IndepSetFree n := by
  rw [← SimpleGraph.not_cliqueFree_iff_top_isContained, SimpleGraph.cliqueFree_compl]

/-! ### N03 -/

theorem c4_free_common_nbrs {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ¬ (SimpleGraph.cycleGraph 4).IsContained G) {u v : V} (huv : u ≠ v) :
    (G.neighborFinset u ∩ G.neighborFinset v).card ≤ 1 := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hlt
  simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at ha hb
  obtain ⟨hua, hva⟩ := ha
  obtain ⟨hub, hvb⟩ := hb
  have hau : a ≠ u := hua.ne'
  have hav : a ≠ v := hva.ne'
  have hbu : b ≠ u := hub.ne'
  have hbv : b ≠ v := hvb.ne'
  have hua' : u ≠ a := hua.ne
  have hva' : v ≠ a := hva.ne
  have hub' : u ≠ b := hub.ne
  have hvb' : v ≠ b := hvb.ne
  have hba : b ≠ a := hab.symm
  have hvu : v ≠ u := huv.symm
  apply hG
  rw [SimpleGraph.cycleGraph_isContained_iff (show (2 : ℕ) < 4 by norm_num)]
  refine ⟨u, SimpleGraph.Walk.cons hua (SimpleGraph.Walk.cons hva.symm
    (SimpleGraph.Walk.cons hvb (SimpleGraph.Walk.cons hub.symm SimpleGraph.Walk.nil))), ?_,
    by first | rfl | simp⟩
  rw [SimpleGraph.Walk.cons_isCycle_iff]
  simp [SimpleGraph.Walk.cons_isPath_iff, SimpleGraph.Walk.IsPath.nil, SimpleGraph.Walk.support_cons,
    SimpleGraph.Walk.support_nil, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, Sym2.eq_iff,
    hau, hav, hbu, hbv, hua', hva', hub', hvb', hab, hba, huv, hvu] <;> tauto

/-! ### N04 -/

theorem c4_free_nbhd_local_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ¬ (SimpleGraph.cycleGraph 4).IsContained G) (v w : V) (hw : G.Adj v w) :
    ((G.neighborFinset v).filter (G.Adj w)).card ≤ 1 := by
  calc ((G.neighborFinset v).filter (G.Adj w)).card
      ≤ (G.neighborFinset v ∩ G.neighborFinset w).card := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hx
        simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
        exact hx
    _ ≤ 1 := c4_free_common_nbrs G hG hw.ne

/-! ### N05 -/

theorem greedy_indep_local {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) (D : ℕ)
    (hD : ∀ v ∈ s, (s.filter (G.Adj v)).card ≤ D) :
    ∃ t ⊆ s, G.IsIndepSet (t : Set V) ∧ s.card ≤ (D + 1) * t.card := by
  induction s using Finset.strongInduction with
  | H s ih =>
    rcases s.eq_empty_or_nonempty with hs | hs
    · refine ⟨∅, Finset.empty_subset _, ?_, ?_⟩
      · rw [Finset.coe_empty]
        exact Set.pairwise_empty _
      · rw [hs, Finset.card_empty]
        exact Nat.zero_le _
    · obtain ⟨v, hv⟩ := hs
      obtain ⟨s', hs'⟩ : ∃ s' : Finset V, s' = s \ insert v (s.filter (G.Adj v)) := ⟨_, rfl⟩
      have hins : insert v (s.filter (G.Adj v)) ⊆ s := by
        intro x hx
        rw [Finset.mem_insert] at hx
        rcases hx with hx | hx
        · rw [hx]; exact hv
        · exact (Finset.mem_filter.mp hx).1
      have hsub : s' ⊆ s := by
        rw [hs']
        exact Finset.sdiff_subset
      have hss : s' ⊂ s := by
        rw [hs']
        exact Finset.sdiff_ssubset hins ⟨v, Finset.mem_insert_self v _⟩
      have hD' : ∀ u ∈ s', (s'.filter (G.Adj u)).card ≤ D := fun u hu =>
        le_trans (Finset.card_le_card (Finset.filter_subset_filter (G.Adj u) hsub)) (hD u (hsub hu))
      obtain ⟨t', ht's, ht'ind, ht'card⟩ := ih s' hss hD'
      have hmem : ∀ x ∈ t', x ∈ s ∧ x ∉ insert v (s.filter (G.Adj v)) := by
        intro x hx
        have hx' := ht's hx
        rw [hs', Finset.mem_sdiff] at hx'
        exact hx'
      have hvt' : v ∉ t' := fun h => (hmem v h).2 (Finset.mem_insert_self v _)
      have hnadj : ∀ b ∈ t', ¬ G.Adj v b := fun b hb hadj =>
        (hmem b hb).2 (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨(hmem b hb).1, hadj⟩))
      refine ⟨insert v t', Finset.insert_subset hv (fun x hx => (hmem x hx).1), ?_, ?_⟩
      · intro x hx y hy hxy
        show ¬ G.Adj x y
        rw [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx hy
        rcases hx with hx | hx <;> rcases hy with hy | hy
        · exact absurd (hx.trans hy.symm) hxy
        · rw [hx]; exact hnadj y hy
        · rw [hy]; intro h; exact hnadj x hx h.symm
        · exact ht'ind hx hy hxy
      · have h1 : s'.card + (insert v (s.filter (G.Adj v))).card = s.card := by
          rw [hs']
          exact Finset.card_sdiff_add_card_eq_card hins
        have h2 : (insert v (s.filter (G.Adj v))).card ≤ D + 1 :=
          le_trans (Finset.card_insert_le _ _) (Nat.add_le_add_right (hD v hv) 1)
        rw [Finset.card_insert_of_notMem hvt', mul_add, mul_one]
        omega

/-! ### N06 -/

theorem degree_lt_of_c4_free_indepSetFree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ¬ (SimpleGraph.cycleGraph 4).IsContained G) {n : ℕ} (hα : G.IndepSetFree n) (v : V) :
    G.degree v < 2 * n := by
  have hD : ∀ w ∈ G.neighborFinset v, ((G.neighborFinset v).filter (G.Adj w)).card ≤ 1 := by
    intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw
    exact c4_free_nbhd_local_degree G hG v w hw
  obtain ⟨t, hts, htind, htcard⟩ := greedy_indep_local G (G.neighborFinset v) 1 hD
  have htn : t.card < n := by
    by_contra hle
    rw [not_lt] at hle
    obtain ⟨u, hut, hucard⟩ := Finset.exists_subset_card_eq hle
    exact hα u ⟨Set.Pairwise.mono (Finset.coe_subset.mpr hut) htind, hucard⟩
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  omega

/-! Helper: the filter of `univ` by adjacency is the neighbourhood. -/

theorem card_filter_univ_adj {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    ((Finset.univ : Finset V).filter (G.Adj v)).card = G.degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  congr 1
  ext w
  simp [SimpleGraph.mem_neighborFinset]

/-! ### N07 -/

theorem card_le_quadratic_of_c4_free {N n : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (hG : ¬ (SimpleGraph.cycleGraph 4).IsContained G) (hα : G.IndepSetFree n) :
    N ≤ 2 * n * n := by
  have hD : ∀ v ∈ (Finset.univ : Finset (Fin N)),
      ((Finset.univ : Finset (Fin N)).filter (G.Adj v)).card ≤ 2 * n := by
    intro v _
    have h1 := card_filter_univ_adj G v
    have h2 := degree_lt_of_c4_free_indepSetFree G hG hα v
    omega
  obtain ⟨t, -, htind, htcard⟩ := greedy_indep_local G Finset.univ (2 * n) hD
  have htn : t.card < n := by
    by_contra hle
    rw [not_lt] at hle
    obtain ⟨u, hut, hucard⟩ := Finset.exists_subset_card_eq hle
    exact hα u ⟨Set.Pairwise.mono (Finset.coe_subset.mpr hut) htind, hucard⟩
  rw [Finset.card_univ, Fintype.card_fin] at htcard
  have h3 : t.card + 1 ≤ n := htn
  have h4 : (2 * n + 1) * (t.card + 1) ≤ (2 * n + 1) * n := Nat.mul_le_mul (le_refl _) h3
  nlinarith

/-! ### N08 -/

theorem graphRamsey_le_of_c4_free_bound (n N : ℕ)
    (h : ∀ G : SimpleGraph (Fin N), ¬ (SimpleGraph.cycleGraph 4).IsContained G → ¬ G.IndepSetFree n) :
    SimpleGraph.graphRamsey (SimpleGraph.cycleGraph 4) (SimpleGraph.completeGraph (Fin n)) ≤ N := by
  apply graphRamsey_le_of_forall
  intro C
  rw [complete_isContained_compl_iff]
  exact or_iff_not_imp_left.mpr (h C)

/-! ### N09 -/

theorem graphRamsey_c4_le_quadratic (n : ℕ) :
    SimpleGraph.graphRamsey (SimpleGraph.cycleGraph 4) (SimpleGraph.completeGraph (Fin n)) ≤ 2 * n * n + 1 := by
  apply graphRamsey_le_of_c4_free_bound
  intro G hG hα
  classical
  have h := card_le_quadratic_of_c4_free G hG hα
  omega

/-! Helper for N10: the pure arithmetic. -/

theorem turan_arith (m e D s b a : ℕ) (h1 : s + b = m) (h2 : b * (D + 1) ≤ 2 * e)
    (h3 : m * D ≤ 4 * e) (h4 : 4 * e < m * (D + 1)) (h5 : s ≤ (D + 1) * a) :
    m ^ 2 ≤ 2 * (4 * e + m) * a := by
  have h2b : 2 * b < m := by
    by_contra hcon
    rw [not_lt] at hcon
    have key : m * (D + 1) ≤ 2 * b * (D + 1) := Nat.mul_le_mul hcon (le_refl _)
    have key2 : 2 * b * (D + 1) = 2 * (b * (D + 1)) := mul_assoc _ _ _
    omega
  have hms : m ≤ 2 * s := by omega
  have h6 : m * m ≤ m * (2 * ((D + 1) * a)) :=
    Nat.mul_le_mul (le_refl m) (le_trans hms (Nat.mul_le_mul (le_refl 2) h5))
  have h7 : m * (2 * ((D + 1) * a)) = 2 * (m * D + m) * a := by ring
  have h8 : 2 * (m * D + m) * a ≤ 2 * (4 * e + m) * a :=
    Nat.mul_le_mul (Nat.mul_le_mul (le_refl 2) (Nat.add_le_add_right h3 m)) (le_refl a)
  calc m ^ 2 = m * m := by ring
    _ ≤ m * (2 * ((D + 1) * a)) := h6
    _ = 2 * (m * D + m) * a := h7
    _ ≤ 2 * (4 * e + m) * a := h8

/-! ### N10 -/

theorem turan_weak {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ t : Finset V, G.IsIndepSet (t : Set V) ∧
      Fintype.card V ^ 2 ≤ 2 * (4 * G.edgeFinset.card + Fintype.card V) * t.card := by
  rcases Nat.eq_zero_or_pos (Fintype.card V) with hm | hm
  · refine ⟨∅, ?_, ?_⟩
    · rw [Finset.coe_empty]
      exact Set.pairwise_empty _
    · rw [hm]
      first
        | (simp; done)
        | norm_num
        | exact Nat.zero_le _
  · obtain ⟨D, hD1, hD2⟩ : ∃ D : ℕ, Fintype.card V * D ≤ 4 * G.edgeFinset.card ∧
        4 * G.edgeFinset.card < Fintype.card V * (D + 1) :=
      ⟨4 * G.edgeFinset.card / Fintype.card V, Nat.mul_div_le _ _, Nat.lt_mul_div_succ _ hm⟩
    have hD : ∀ v ∈ ((Finset.univ : Finset V).filter fun v => G.degree v ≤ D),
        (((Finset.univ : Finset V).filter fun v => G.degree v ≤ D).filter (G.Adj v)).card ≤ D := by
      intro v hv
      rw [Finset.mem_filter] at hv
      calc (((Finset.univ : Finset V).filter fun v => G.degree v ≤ D).filter (G.Adj v)).card
          ≤ (G.neighborFinset v).card := by
            apply Finset.card_le_card
            intro x hx
            rw [Finset.mem_filter] at hx
            rw [SimpleGraph.mem_neighborFinset]
            exact hx.2
        _ = G.degree v := rfl
        _ ≤ D := hv.2
    obtain ⟨t, -, htind, htcard⟩ := greedy_indep_local G _ D hD
    have hsum : ∑ v, G.degree v = 2 * G.edgeFinset.card := by
      convert SimpleGraph.sum_degrees_eq_twice_card_edges G
    have hbig : ((Finset.univ : Finset V).filter fun v => ¬ G.degree v ≤ D).card * (D + 1)
        ≤ 2 * G.edgeFinset.card := by
      rw [← hsum]
      calc ((Finset.univ : Finset V).filter fun v => ¬ G.degree v ≤ D).card * (D + 1)
          = ∑ v ∈ ((Finset.univ : Finset V).filter fun v => ¬ G.degree v ≤ D), (D + 1) := by
            rw [Finset.sum_const, smul_eq_mul]
        _ ≤ ∑ v ∈ ((Finset.univ : Finset V).filter fun v => ¬ G.degree v ≤ D), G.degree v := by
            apply Finset.sum_le_sum
            intro v hv
            rw [Finset.mem_filter] at hv
            omega
        _ ≤ ∑ v, G.degree v := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset V))
      (fun v => G.degree v ≤ D)
    rw [Finset.card_univ] at hsplit
    exact ⟨t, htind, turan_arith (Fintype.card V) G.edgeFinset.card D _ _ t.card hsplit hbig hD1 hD2 htcard⟩

/-! ### N11 -/

theorem exists_dense_core {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
    (hd : d * Fintype.card V ≤ G.edgeFinset.card) :
    ∃ s : Finset V, s.Nonempty ∧ ∀ v ∈ s, d ≤ (s.filter (G.Adj v)).card := by
  -- removing a vertex `v` from `s` loses at most `2 * (internal degree of v)` from the degree sum
  have hrem : ∀ (s : Finset V) (v : V), v ∈ s →
      ∑ u ∈ s, (s.filter (G.Adj u)).card ≤
        ∑ u ∈ s.erase v, ((s.erase v).filter (G.Adj u)).card + 2 * (s.filter (G.Adj v)).card := by
    intro s v hv
    rw [← Finset.add_sum_erase s _ hv]
    have hterm : ∀ u ∈ s.erase v, (s.filter (G.Adj u)).card ≤
        ((s.erase v).filter (G.Adj u)).card + (if G.Adj v u then 1 else 0) := by
      intro u hu
      by_cases h : G.Adj v u
      · rw [if_pos h]
        calc (s.filter (G.Adj u)).card ≤ (insert v ((s.erase v).filter (G.Adj u))).card := by
              apply Finset.card_le_card
              intro x hx
              rw [Finset.mem_filter] at hx
              rw [Finset.mem_insert, Finset.mem_filter, Finset.mem_erase]
              by_cases hxv : x = v
              · exact Or.inl hxv
              · exact Or.inr ⟨⟨hxv, hx.1⟩, hx.2⟩
          _ ≤ ((s.erase v).filter (G.Adj u)).card + 1 := Finset.card_insert_le _ _
      · rw [if_neg h, Nat.add_zero]
        apply Finset.card_le_card
        intro x hx
        rw [Finset.mem_filter] at hx
        rw [Finset.mem_filter, Finset.mem_erase]
        refine ⟨⟨?_, hx.1⟩, hx.2⟩
        intro hxv
        rw [hxv] at hx
        exact h hx.2.symm
    have hsum : ∑ u ∈ s.erase v, (s.filter (G.Adj u)).card ≤
        ∑ u ∈ s.erase v, ((s.erase v).filter (G.Adj u)).card +
          ∑ u ∈ s.erase v, (if G.Adj v u then 1 else 0) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum hterm
    have hind : ∑ u ∈ s.erase v, (if G.Adj v u then 1 else 0) = ((s.erase v).filter (G.Adj v)).card :=
      (Finset.card_filter _ _).symm
    have hle : ((s.erase v).filter (G.Adj v)).card ≤ (s.filter (G.Adj v)).card :=
      Finset.card_le_card (Finset.filter_subset_filter (G.Adj v) (Finset.erase_subset v s))
    omega
  -- strong induction: a set with large degree sum contains a nonempty core of minimum degree `d`
  have main : ∀ s : Finset V, s.Nonempty → 2 * d * s.card ≤ ∑ u ∈ s, (s.filter (G.Adj u)).card →
      ∃ s' ⊆ s, s'.Nonempty ∧ ∀ v ∈ s', d ≤ (s'.filter (G.Adj v)).card := by
    intro s
    induction s using Finset.strongInduction with
    | H s ih =>
      intro hs hf
      by_cases hall : ∀ v ∈ s, d ≤ (s.filter (G.Adj v)).card
      · exact ⟨s, Finset.Subset.refl s, hs, hall⟩
      · push_neg at hall
        obtain ⟨v, hv, hk⟩ := hall
        have h1 := hrem s v hv
        have hcard : (s.erase v).card = s.card - 1 := Finset.card_erase_of_mem hv
        have hpos : 1 ≤ s.card := Finset.card_pos.mpr hs
        have hmul : 2 * d * (s.card - 1) = 2 * d * s.card - 2 * d := Nat.mul_sub_one _ _
        have hf' : 2 * d * (s.erase v).card ≤ ∑ u ∈ s.erase v, ((s.erase v).filter (G.Adj u)).card := by
          rw [hcard]
          omega
        have hne : (s.erase v).Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro hemp
          rw [hemp, Finset.sum_empty] at h1
          have h2 : 2 * d * 1 ≤ 2 * d * s.card := Nat.mul_le_mul (le_refl _) hpos
          omega
        obtain ⟨s', hs's, hs'ne, hs'min⟩ := ih (s.erase v) (Finset.erase_ssubset hv) hne hf'
        exact ⟨s', Finset.Subset.trans hs's (Finset.erase_subset v s), hs'ne, hs'min⟩
  have hsum : ∑ v, G.degree v = 2 * G.edgeFinset.card := by
    convert SimpleGraph.sum_degrees_eq_twice_card_edges G
  have huniv : 2 * d * (Finset.univ : Finset V).card ≤
      ∑ u ∈ (Finset.univ : Finset V), ((Finset.univ : Finset V).filter (G.Adj u)).card := by
    have h1 : ∑ u ∈ (Finset.univ : Finset V), ((Finset.univ : Finset V).filter (G.Adj u)).card
        = ∑ u, G.degree u :=
      Finset.sum_congr rfl (fun u _ => card_filter_univ_adj G u)
    rw [h1, hsum, Finset.card_univ]
    have h2 : 2 * (d * Fintype.card V) ≤ 2 * G.edgeFinset.card := Nat.mul_le_mul (le_refl 2) hd
    rw [mul_assoc]
    exact h2
  obtain ⟨s, -, hsne, hsmin⟩ := main Finset.univ Finset.univ_nonempty huniv
  exact ⟨s, hsne, hsmin⟩

/-! ### N12 -/

theorem moore_bound_c4_free {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ¬ (SimpleGraph.cycleGraph 4).IsContained G) (s : Finset V) (d : ℕ) (hs : s.Nonempty)
    (hmin : ∀ v ∈ s, d ≤ (s.filter (G.Adj v)).card) :
    d * d ≤ 2 * s.card := by
  obtain ⟨v, hv⟩ := hs
  have hdA : d ≤ (s.filter (G.Adj v)).card := hmin v hv
  have hT : ∀ w ∈ s.filter (G.Adj v), d - 1 ≤ ((s.filter (G.Adj w)).erase v).card := by
    intro w hw
    rw [Finset.mem_filter] at hw
    have hvw : v ∈ s.filter (G.Adj w) := Finset.mem_filter.mpr ⟨hv, hw.2.symm⟩
    rw [Finset.card_erase_of_mem hvw]
    exact Nat.sub_le_sub_right (hmin w hw.1) 1
  have hdisj : ((s.filter (G.Adj v) : Finset V) : Set V).PairwiseDisjoint
      (fun w => (s.filter (G.Adj w)).erase v) := by
    intro w hw w' hw' hne
    show Disjoint ((s.filter (G.Adj w)).erase v) ((s.filter (G.Adj w')).erase v)
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_erase, Finset.mem_filter] at hx hx'
    have hw2 := Finset.mem_filter.mp (Finset.mem_coe.mp hw)
    have hw2' := Finset.mem_filter.mp (Finset.mem_coe.mp hw')
    have hc := c4_free_common_nbrs G hG hne
    have hx_mem : x ∈ G.neighborFinset w ∩ G.neighborFinset w' := by
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨hx.2.2, hx'.2.2⟩
    have hv_mem : v ∈ G.neighborFinset w ∩ G.neighborFinset w' := by
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨hw2.2.symm, hw2'.2.symm⟩
    exact hx.1 (Finset.card_le_one.mp hc x hx_mem v hv_mem)
  have hunion : ((s.filter (G.Adj v)).biUnion fun w => (s.filter (G.Adj w)).erase v) ⊆ s := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨w, -, hx⟩ := hx
    exact (Finset.mem_filter.mp (Finset.mem_of_mem_erase hx)).1
  have hcard : (s.filter (G.Adj v)).card * (d - 1) ≤ s.card := by
    calc (s.filter (G.Adj v)).card * (d - 1)
        = ∑ w ∈ s.filter (G.Adj v), (d - 1) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ w ∈ s.filter (G.Adj v), ((s.filter (G.Adj w)).erase v).card := Finset.sum_le_sum hT
      _ = ((s.filter (G.Adj v)).biUnion fun w => (s.filter (G.Adj w)).erase v).card :=
          (Finset.card_biUnion hdisj).symm
      _ ≤ s.card := Finset.card_le_card hunion
  have hAs : (s.filter (G.Adj v)).card ≤ s.card := Finset.card_le_card (Finset.filter_subset _ _)
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · rw [hd0]
    omega
  · have hd1 : 1 ≤ d := hdpos
    have h1 : d * (d - 1) ≤ (s.filter (G.Adj v)).card * (d - 1) := Nat.mul_le_mul hdA (le_refl _)
    have h2 : d * (d - 1) + d = d * d := by
      have h3 : d - 1 + 1 = d := Nat.sub_add_cancel hd1
      calc d * (d - 1) + d = d * (d - 1 + 1) := by ring
        _ = d * d := by rw [h3]
    omega

/-! ### N13 (the open core; not proved) -/

theorem core_near_extremal :
    ∃ δ η : ℝ, 0 < δ ∧ δ ≤ 1 / 8 ∧ 4 * δ ≤ η ∧ ∀ κ : ℝ, 0 < κ → ∃ K : ℝ, 0 < K ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V),
        ¬ (SimpleGraph.cycleGraph 4).IsContained G →
        (∀ v ∈ s, κ * (s.card : ℝ) ^ ((1 : ℝ) / 2 - δ) ≤ ((s.filter (G.Adj v)).card : ℝ)) →
        ∃ t ⊆ s, G.IsIndepSet (t : Set V) ∧ K * (s.card : ℝ) ^ ((1 : ℝ) / 2 + η) ≤ (t.card : ℝ) := by
  sorry

/-! ### N14 -/

theorem sparse_branch_arith (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (N E t : ℝ) (hN : 1 ≤ N)
    (hE0 : 0 ≤ E) (hE : E ≤ N ^ ((3 : ℝ) / 2 - δ)) (ht : N ^ 2 ≤ 2 * (4 * E + N) * t) :
    N ^ ((1 : ℝ) / 2 + δ) ≤ 10 * t := by
  have hN0 : 0 < N := by linarith
  have hP1 : N ≤ N ^ ((3 : ℝ) / 2 - δ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hN (show (1 : ℝ) ≤ 3 / 2 - δ by linarith)
    rwa [Real.rpow_one] at h
  have hPpos : 0 < N ^ ((3 : ℝ) / 2 - δ) := Real.rpow_pos_of_pos hN0 _
  have hprod : N ^ ((1 : ℝ) / 2 + δ) * N ^ ((3 : ℝ) / 2 - δ) = N ^ 2 := by
    rw [← Real.rpow_add hN0, show (1 : ℝ) / 2 + δ + ((3 : ℝ) / 2 - δ) = 2 by ring, Real.rpow_two]
  have ht0 : 0 ≤ t := by
    by_contra hneg
    rw [not_le] at hneg
    nlinarith [sq_nonneg N]
  have key : N ^ ((1 : ℝ) / 2 + δ) * N ^ ((3 : ℝ) / 2 - δ) ≤ 10 * t * N ^ ((3 : ℝ) / 2 - δ) := by
    rw [hprod]
    nlinarith [mul_nonneg ht0 (sub_nonneg.mpr hE), mul_nonneg ht0 (sub_nonneg.mpr hP1)]
  exact le_of_mul_le_mul_right key hPpos

/-! ### N15 -/

theorem dense_branch_arith (δ η K : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 8) (hη : 4 * δ ≤ η) (hK : 0 < K)
    (N M : ℝ) (hN : 1 ≤ N) (hM : 0 ≤ M) (hNM : N ^ (1 - 2 * δ) ≤ 8 * M) :
    K * (8 : ℝ) ^ (-((1 : ℝ) / 2 + η)) * N ^ ((1 : ℝ) / 2 + η / 2) ≤ K * M ^ ((1 : ℝ) / 2 + η) := by
  have hN0 : 0 < N := by linarith
  have hM' : N ^ (1 - 2 * δ) / 8 ≤ M := by linarith
  have hNpow0 : 0 ≤ N ^ (1 - 2 * δ) / 8 := by positivity
  have h1 : (N ^ (1 - 2 * δ) / 8) ^ ((1 : ℝ) / 2 + η) ≤ M ^ ((1 : ℝ) / 2 + η) :=
    Real.rpow_le_rpow hNpow0 hM' (by linarith)
  have h2 : (N ^ (1 - 2 * δ) / 8) ^ ((1 : ℝ) / 2 + η)
      = N ^ ((1 - 2 * δ) * ((1 : ℝ) / 2 + η)) * (8 : ℝ) ^ (-((1 : ℝ) / 2 + η)) := by
    rw [Real.div_rpow (Real.rpow_nonneg hN0.le _) (show (0 : ℝ) ≤ 8 by norm_num),
      ← Real.rpow_mul hN0.le, Real.rpow_neg (show (0 : ℝ) ≤ 8 by norm_num), div_eq_mul_inv]
  have h3 : N ^ ((1 : ℝ) / 2 + η / 2) ≤ N ^ ((1 - 2 * δ) * ((1 : ℝ) / 2 + η)) := by
    apply Real.rpow_le_rpow_of_exponent_le hN
    nlinarith [mul_nonneg (sub_nonneg.mpr hη) (show (0 : ℝ) ≤ 1 / 2 - 2 * δ by linarith),
      mul_nonneg hδ.le (sub_nonneg.mpr hδ')]
  have h8 : 0 < (8 : ℝ) ^ (-((1 : ℝ) / 2 + η)) := Real.rpow_pos_of_pos (by norm_num) _
  calc K * (8 : ℝ) ^ (-((1 : ℝ) / 2 + η)) * N ^ ((1 : ℝ) / 2 + η / 2)
      ≤ K * (8 : ℝ) ^ (-((1 : ℝ) / 2 + η)) * N ^ ((1 - 2 * δ) * ((1 : ℝ) / 2 + η)) :=
        mul_le_mul_of_nonneg_left h3 (mul_nonneg hK.le h8.le)
    _ = K * ((N ^ (1 - 2 * δ) / 8) ^ ((1 : ℝ) / 2 + η)) := by rw [h2]; ring
    _ ≤ K * M ^ ((1 : ℝ) / 2 + η) := mul_le_mul_of_nonneg_left h1 hK.le

/-! ### N16 (rests on the open core N13) -/

theorem c4_free_indep_power :
    ∃ ε K : ℝ, 0 < ε ∧ 0 < K ∧ ∀ (N : ℕ) (G : SimpleGraph (Fin N)) [DecidableRel G.Adj],
      ¬ (SimpleGraph.cycleGraph 4).IsContained G →
      ∃ t : Finset (Fin N), G.IsIndepSet (t : Set (Fin N)) ∧ K * (N : ℝ) ^ ((1 : ℝ) / 2 + ε) ≤ (t.card : ℝ) := by
  obtain ⟨δ, η, hδ, hδ', hη, hcore⟩ := core_near_extremal
  obtain ⟨K, hK, hK'⟩ := hcore (1 / 2) (by norm_num)
  have h8 : 0 < (8 : ℝ) ^ (-((1 : ℝ) / 2 + η)) := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨δ, min (1 / 10) (K * (8 : ℝ) ^ (-((1 : ℝ) / 2 + η))), hδ,
    lt_min (by norm_num) (mul_pos hK h8), ?_⟩
  intro N G _ hG
  have hKmin1 : min (1 / 10) (K * (8 : ℝ) ^ (-((1 : ℝ) / 2 + η))) ≤ 1 / 10 := min_le_left _ _
  have hKmin2 : min (1 / 10) (K * (8 : ℝ) ^ (-((1 : ℝ) / 2 + η)))
      ≤ K * (8 : ℝ) ^ (-((1 : ℝ) / 2 + η)) := min_le_right _ _
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · -- no vertices: the empty set
    subst hN0
    refine ⟨∅, ?_, ?_⟩
    · rw [Finset.coe_empty]
      exact Set.pairwise_empty _
    · rw [Nat.cast_zero, Finset.card_empty, Nat.cast_zero,
        Real.zero_rpow (by positivity), mul_zero]
  · have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNpos
    have hNr0 : (0 : ℝ) < (N : ℝ) := by linarith
    have hpowN : (0 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 + δ) := Real.rpow_nonneg hNr0.le _
    by_cases hsparse : (G.edgeFinset.card : ℝ) ≤ (N : ℝ) ^ ((3 : ℝ) / 2 - δ)
    · -- sparse branch: Turán-type bound N10 and the arithmetic N14
      obtain ⟨t, htind, htcard⟩ := turan_weak G
      rw [Fintype.card_fin] at htcard
      have htR : (N : ℝ) ^ 2 ≤ 2 * (4 * (G.edgeFinset.card : ℝ) + N) * (t.card : ℝ) := by
        exact_mod_cast htcard
      have h14 := sparse_branch_arith δ hδ (by linarith) (N : ℝ) (G.edgeFinset.card : ℝ) (t.card : ℝ)
        hN1 (Nat.cast_nonneg _) hsparse htR
      refine ⟨t, htind, ?_⟩
      calc min (1 / 10) (K * (8 : ℝ) ^ (-((1 : ℝ) / 2 + η))) * (N : ℝ) ^ ((1 : ℝ) / 2 + δ)
          ≤ 1 / 10 * (N : ℝ) ^ ((1 : ℝ) / 2 + δ) := mul_le_mul_of_nonneg_right hKmin1 hpowN
        _ ≤ (t.card : ℝ) := by linarith
    · -- dense branch: a core N11, the Moore bound N12, the open core N13 and the arithmetic N15
      rw [not_le] at hsparse
      have hx1 : (1 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - δ) := Real.one_le_rpow hN1 (by linarith)
      have hx0 : (0 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - δ) := by linarith
      have hd1 : 1 ≤ ⌊(N : ℝ) ^ ((1 : ℝ) / 2 - δ)⌋₊ := Nat.le_floor (by rw [Nat.cast_one]; exact hx1)
      have hdx : ((⌊(N : ℝ) ^ ((1 : ℝ) / 2 - δ)⌋₊ : ℕ) : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - δ) :=
        Nat.floor_le hx0
      have hxd : (N : ℝ) ^ ((1 : ℝ) / 2 - δ) < ((⌊(N : ℝ) ^ ((1 : ℝ) / 2 - δ)⌋₊ : ℕ) : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      have hd1R : (1 : ℝ) ≤ ((⌊(N : ℝ) ^ ((1 : ℝ) / 2 - δ)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hd1
      have hx2d : (N : ℝ) ^ ((1 : ℝ) / 2 - δ) ≤ 2 * ((⌊(N : ℝ) ^ ((1 : ℝ) / 2 - δ)⌋₊ : ℕ) : ℝ) := by
        linarith
      have hdN : ⌊(N : ℝ) ^ ((1 : ℝ) / 2 - δ)⌋₊ * Fintype.card (Fin N) ≤ G.edgeFinset.card := by
        rw [Fintype.card_fin]
        have h1 : ((⌊(N : ℝ) ^ ((1 : ℝ) / 2 - δ)⌋₊ : ℕ) : ℝ) * (N : ℝ) ≤ (G.edgeFinset.card : ℝ) := by
          calc ((⌊(N : ℝ) ^ ((1 : ℝ) / 2 - δ)⌋₊ : ℕ) : ℝ) * (N : ℝ)
              ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - δ) * (N : ℝ) := mul_le_mul_of_nonneg_right hdx hNr0.le
            _ = (N : ℝ) ^ ((3 : ℝ) / 2 - δ) := by
              rw [← Real.rpow_add_one hNr0.ne']
              congr 1
              ring
            _ ≤ (G.edgeFinset.card : ℝ) := hsparse.le
        exact_mod_cast h1
      haveI : Nonempty (Fin N) := ⟨⟨0, hNpos⟩⟩
      obtain ⟨s, hsne, hsmin⟩ := exists_dense_core G _ hdN
      have hmoore := moore_bound_c4_free G hG s _ hsne hsmin
      have hsN : s.card ≤ N := by
        have h := Finset.card_le_univ s
        rwa [Fintype.card_fin] at h
      have hsNR : (s.card : ℝ) ≤ (N : ℝ) := by exact_mod_cast hsN
      have hs0 : (0 : ℝ) ≤ (s.card : ℝ) := Nat.cast_nonneg _
      have hdeg : ∀ v ∈ s, (1 / 2 : ℝ) * (s.card : ℝ) ^ ((1 : ℝ) / 2 - δ)
          ≤ ((s.filter (G.Adj v)).card : ℝ) := by
        intro v hv
        have h1 : ((⌊(N : ℝ) ^ ((1 : ℝ) / 2 - δ)⌋₊ : ℕ) : ℝ) ≤ ((s.filter (G.Adj v)).card : ℝ) := by
          exact_mod_cast hsmin v hv
        have h2 : (s.card : ℝ) ^ ((1 : ℝ) / 2 - δ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - δ) :=
          Real.rpow_le_rpow hs0 hsNR (by linarith)
        linarith
      obtain ⟨t, -, htind, htcard⟩ := hK' (Fin N) G s hG hdeg
      have hmooreR : ((⌊(N : ℝ) ^ ((1 : ℝ) / 2 - δ)⌋₊ : ℕ) : ℝ) * ((⌊(N : ℝ) ^ ((1 : ℝ) / 2 - δ)⌋₊ : ℕ) : ℝ)
          ≤ 2 * (s.card : ℝ) := by exact_mod_cast hmoore
      have hNM : (N : ℝ) ^ (1 - 2 * δ) ≤ 8 * (s.card : ℝ) := by
        have h1 : (N : ℝ) ^ (1 - 2 * δ) = (N : ℝ) ^ ((1 : ℝ) / 2 - δ) * (N : ℝ) ^ ((1 : ℝ) / 2 - δ) := by
          rw [← Real.rpow_add hNr0]
          congr 1
          ring
        rw [h1]
        have h2 := mul_le_mul hx2d hx2d hx0 (by linarith)
        nlinarith
      have h15 := dense_branch_arith δ η K hδ hδ' hη hK (N : ℝ) (s.card : ℝ) hN1 hs0 hNM
      have hexp : (N : ℝ) ^ ((1 : ℝ) / 2 + δ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 + η / 2) :=
        Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      refine ⟨t, htind, ?_⟩
      calc min (1 / 10) (K * (8 : ℝ) ^ (-((1 : ℝ) / 2 + η))) * (N : ℝ) ^ ((1 : ℝ) / 2 + δ)
          ≤ K * (8 : ℝ) ^ (-((1 : ℝ) / 2 + η)) * (N : ℝ) ^ ((1 : ℝ) / 2 + δ) :=
            mul_le_mul_of_nonneg_right hKmin2 hpowN
        _ ≤ K * (8 : ℝ) ^ (-((1 : ℝ) / 2 + η)) * (N : ℝ) ^ ((1 : ℝ) / 2 + η / 2) :=
            mul_le_mul_of_nonneg_left hexp (mul_pos hK h8).le
        _ ≤ K * (s.card : ℝ) ^ ((1 : ℝ) / 2 + η) := h15
        _ ≤ (t.card : ℝ) := htcard

/-! ### N17 -/

theorem rpow_inversion (K ε N x : ℝ) (hK : 0 < K) (hε : 0 < ε) (hN : 0 ≤ N) (hx : 0 ≤ x)
    (h : K * N ^ ((1 : ℝ) / 2 + ε) ≤ x) :
    N ≤ K ^ (-(2 / (1 + 2 * ε))) * x ^ (2 - 4 * ε / (1 + 2 * ε)) := by
  have hpos : (0 : ℝ) < 1 + 2 * ε := by linarith
  have hne : (1 + 2 * ε : ℝ) ≠ 0 := ne_of_gt hpos
  have hq : (2 : ℝ) - 4 * ε / (1 + 2 * ε) = 2 / (1 + 2 * ε) := by
    rw [eq_div_iff hne, sub_mul, div_mul_cancel₀ _ hne]
    ring
  have hmul : ((1 : ℝ) / 2 + ε) * (2 / (1 + 2 * ε)) = 1 := by
    rw [← mul_div_assoc, div_eq_one_iff_eq hne]
    ring
  have hq0 : (0 : ℝ) ≤ 2 / (1 + 2 * ε) := by positivity
  have hNa : (0 : ℝ) ≤ N ^ ((1 : ℝ) / 2 + ε) := Real.rpow_nonneg hN _
  have h1 : N ^ ((1 : ℝ) / 2 + ε) ≤ x / K := by
    rw [le_div_iff₀ hK]
    linarith
  have h2 : (N ^ ((1 : ℝ) / 2 + ε)) ^ (2 / (1 + 2 * ε)) ≤ (x / K) ^ (2 / (1 + 2 * ε)) :=
    Real.rpow_le_rpow hNa h1 hq0
  rw [← Real.rpow_mul hN, hmul, Real.rpow_one, Real.div_rpow hx hK.le] at h2
  rw [hq, Real.rpow_neg hK.le]
  calc N ≤ x ^ (2 / (1 + 2 * ε)) / K ^ (2 / (1 + 2 * ε)) := h2
    _ = (K ^ (2 / (1 + 2 * ε)))⁻¹ * x ^ (2 / (1 + 2 * ε)) := by ring

/-! ### N18 (rests on N16, hence on the open core N13) -/

theorem card_le_power_of_c4_free :
    ∃ c C : ℝ, 0 < c ∧ c ≤ 2 ∧ 0 ≤ C ∧ ∀ (n N : ℕ) (G : SimpleGraph (Fin N)) [DecidableRel G.Adj], 1 ≤ n →
      ¬ (SimpleGraph.cycleGraph 4).IsContained G → G.IndepSetFree n → (N : ℝ) ≤ C * (n : ℝ) ^ (2 - c) := by
  obtain ⟨ε, K, hε, hK, hmain⟩ := c4_free_indep_power
  have hpos : (0 : ℝ) < 1 + 2 * ε := by linarith
  refine ⟨4 * ε / (1 + 2 * ε), K ^ (-(2 / (1 + 2 * ε))), div_pos (by linarith) hpos, ?_,
    (Real.rpow_pos_of_pos hK _).le, ?_⟩
  · rw [div_le_iff₀ hpos]
    linarith
  · intro n N G _ hn hG hα
    obtain ⟨t, htind, htcard⟩ := hmain N G hG
    have htn : t.card < n := by
      by_contra hle
      rw [not_lt] at hle
      obtain ⟨u, hut, hucard⟩ := Finset.exists_subset_card_eq hle
      exact hα u ⟨Set.Pairwise.mono (Finset.coe_subset.mpr hut) htind, hucard⟩
    have htnR : (t.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast htn.le
    have h17 := rpow_inversion K ε (N : ℝ) (t.card : ℝ) hK hε (Nat.cast_nonneg _) (Nat.cast_nonneg _) htcard
    have hc2 : (0 : ℝ) ≤ 2 - 4 * ε / (1 + 2 * ε) := by
      rw [sub_nonneg, div_le_iff₀ hpos]
      linarith
    calc (N : ℝ) ≤ K ^ (-(2 / (1 + 2 * ε))) * (t.card : ℝ) ^ (2 - 4 * ε / (1 + 2 * ε)) := h17
      _ ≤ K ^ (-(2 / (1 + 2 * ε))) * (n : ℝ) ^ (2 - 4 * ε / (1 + 2 * ε)) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) htnR hc2)
            (Real.rpow_pos_of_pos hK _).le

/-! ### N19 -/

theorem floor_succ_le_power (c C x : ℝ) (hc : c ≤ 2) (hC : 0 ≤ C) (n : ℕ) (hn : 1 ≤ n)
    (hx : x ≤ C * (n : ℝ) ^ (2 - c)) :
    ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ (C + 1) * (n : ℝ) ^ (2 - c) := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpow : (1 : ℝ) ≤ (n : ℝ) ^ (2 - c) := Real.one_le_rpow hn' (by linarith)
  push_cast
  rcases le_or_gt 0 x with hx0 | hx0
  · have h1 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
    nlinarith
  · have h1 : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
    rw [h1]
    push_cast
    nlinarith

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
  have hR : SimpleGraph.graphRamsey (SimpleGraph.cycleGraph 4) (SimpleGraph.completeGraph (Fin n))
      ≤ ⌊C * (n : ℝ) ^ (2 - c)⌋₊ + 1 := by
    apply graphRamsey_le_of_c4_free_bound
    intro G hG hα
    classical
    have h := hmain n (⌊C * (n : ℝ) ^ (2 - c)⌋₊ + 1) G hn hG hα
    have h2 := Nat.lt_floor_add_one (C * (n : ℝ) ^ (2 - c))
    push_cast at h
    linarith
  have h19 := floor_succ_le_power c C (C * (n : ℝ) ^ (2 - c)) hc2 hC n hn le_rfl
  calc (SimpleGraph.graphRamsey (SimpleGraph.cycleGraph 4) (SimpleGraph.completeGraph (Fin n)) : ℝ)
      ≤ ((⌊C * (n : ℝ) ^ (2 - c)⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hR
    _ ≤ (C + 1) * (n : ℝ) ^ (2 - c) := h19

end Erdos159
