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

/-! ## Rooms N01–N19 of the planner's blueprint (build 3), in blueprint order.
Each room's statement is the planner's statement verbatim.  Every proof is written without a
checker; each is wrapped as `first | (proof) | sorry` so that a proof that does not elaborate
falls back to `sorry` instead of breaking the file.  Which rooms are actually closed is read off
Lean's `declaration uses 'sorry'` output at FINAL. -/

-- N01
theorem graphRamsey_le_of_forall {α β : Type*} [Fintype α] [Fintype β]
    (G : SimpleGraph α) (H : SimpleGraph β) (N : ℕ)
    (h : ∀ C : SimpleGraph (Fin N), G.IsContained C ∨ H.IsContained Cᶜ) :
    SimpleGraph.graphRamsey G H ≤ N := by
  first
  | exact Nat.sInf_le h
  | (unfold SimpleGraph.graphRamsey
     exact Nat.sInf_le h)
  | (apply Nat.sInf_le
     exact h)
  | (unfold SimpleGraph.graphRamsey
     apply Nat.sInf_le
     simp only [Set.mem_setOf_eq]
     exact h)
  | sorry

-- N02
theorem complete_isContained_compl_iff {V : Type*} (C : SimpleGraph V) (n : ℕ) :
    (SimpleGraph.completeGraph (Fin n)).IsContained Cᶜ ↔ ¬ C.IndepSetFree n := by
  first
  | (rw [← SimpleGraph.not_cliqueFree_iff_top_isContained, SimpleGraph.cliqueFree_compl])
  | (rw [← SimpleGraph.cliqueFree_compl]
     exact (SimpleGraph.not_cliqueFree_iff_top_isContained n).symm)
  | (constructor
     · intro h
       rw [← SimpleGraph.cliqueFree_compl]
       exact (SimpleGraph.not_cliqueFree_iff_top_isContained n).mpr h
     · intro h
       rw [← SimpleGraph.cliqueFree_compl] at h
       exact (SimpleGraph.not_cliqueFree_iff_top_isContained n).mp h)
  | sorry

/-- Helper for N03: two distinct vertices with two distinct common neighbours give a copy of `C₄`. -/
theorem c4_of_common_nbrs {V : Type*} (G : SimpleGraph V) {u v a b : V} (huv : u ≠ v)
    (hua : G.Adj u a) (hva : G.Adj v a) (hub : G.Adj u b) (hvb : G.Adj v b) (hab : a ≠ b) :
    (SimpleGraph.cycleGraph 4).IsContained G := by
  first
  | (have key : ∀ x y : Fin 4, (SimpleGraph.cycleGraph 4).Adj x y →
         (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) ∨ (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 1) ∨
         (x = 2 ∧ y = 3) ∨ (x = 3 ∧ y = 2) ∨ (x = 3 ∧ y = 0) ∨ (x = 0 ∧ y = 3)
     · decide
     have inj : ∀ x y : Fin 4, x ≠ y →
         (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) ∨ (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 1) ∨
         (x = 2 ∧ y = 3) ∨ (x = 3 ∧ y = 2) ∨ (x = 3 ∧ y = 0) ∨ (x = 0 ∧ y = 3) ∨
         (x = 0 ∧ y = 2) ∨ (x = 2 ∧ y = 0) ∨ (x = 1 ∧ y = 3) ∨ (x = 3 ∧ y = 1)
     · decide
     have hmap : ∀ x y : Fin 4, (SimpleGraph.cycleGraph 4).Adj x y →
         G.Adj ((fun i : Fin 4 => if i = 0 then u else if i = 1 then a else if i = 2 then v else b) x)
           ((fun i : Fin 4 => if i = 0 then u else if i = 1 then a else if i = 2 then v else b) y)
     · intro x y hxy
       rcases key x y hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
         ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
         first
         | exact hua | exact hua.symm | exact hva | exact hva.symm
         | exact hub | exact hub.symm | exact hvb | exact hvb.symm
         | simpa using hua | simpa using hua.symm | simpa using hva | simpa using hva.symm
         | simpa using hub | simpa using hub.symm | simpa using hvb | simpa using hvb.symm
     have hf : Function.Injective
         (fun i : Fin 4 => if i = 0 then u else if i = 1 then a else if i = 2 then v else b)
     · intro x y hxy
       by_contra hne
       rcases inj x y hne with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
         ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
         first
         | exact hua.ne hxy | exact hua.ne hxy.symm | exact hva.ne hxy | exact hva.ne hxy.symm
         | exact hub.ne hxy | exact hub.ne hxy.symm | exact hvb.ne hxy | exact hvb.ne hxy.symm
         | exact huv hxy | exact huv hxy.symm | exact hab hxy | exact hab hxy.symm
         | (simp at hxy; first | exact hua.ne hxy | exact hua.ne hxy.symm | exact hva.ne hxy
             | exact hva.ne hxy.symm | exact hub.ne hxy | exact hub.ne hxy.symm | exact hvb.ne hxy
             | exact hvb.ne hxy.symm | exact huv hxy | exact huv hxy.symm | exact hab hxy
             | exact hab hxy.symm)
     exact ⟨⟨⟨fun i : Fin 4 => if i = 0 then u else if i = 1 then a else if i = 2 then v else b,
       fun hxy => hmap _ _ hxy⟩, hf⟩⟩)
  | sorry

-- N03
theorem c4_free_common_nbrs {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ¬ (SimpleGraph.cycleGraph 4).IsContained G) {u v : V} (huv : u ≠ v) :
    (G.neighborFinset u ∩ G.neighborFinset v).card ≤ 1 := by
  first
  | (rw [Finset.card_le_one]
     intro a ha b hb
     by_contra hab
     rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset] at ha hb
     exact hG (c4_of_common_nbrs G huv ha.1 ha.2 hb.1 hb.2 hab))
  | (rw [Finset.card_le_one]
     intro a ha b hb
     by_contra hab
     simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at ha hb
     exact hG (c4_of_common_nbrs G huv ha.1 ha.2 hb.1 hb.2 hab))
  | sorry

-- N04
theorem c4_free_nbhd_local_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ¬ (SimpleGraph.cycleGraph 4).IsContained G) (v w : V) (hw : G.Adj v w) :
    ((G.neighborFinset v).filter (G.Adj w)).card ≤ 1 := by
  first
  | (refine le_trans (Finset.card_le_card ?_) (c4_free_common_nbrs G hG hw.ne)
     intro x hx
     simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hx
     simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
     exact hx)
  | (refine le_trans (Finset.card_le_card ?_) (c4_free_common_nbrs G hG hw.ne)
     intro x hx
     rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hx
     rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset]
     exact hx)
  | sorry

/-- Helper for N05: the greedy bound, by induction on an upper bound for the cardinality of `s`. -/
theorem greedy_indep_local_aux {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ) (n : ℕ) :
    ∀ s : Finset V, s.card ≤ n → (∀ v ∈ s, (s.filter (G.Adj v)).card ≤ D) →
      ∃ t ⊆ s, G.IsIndepSet (t : Set V) ∧ s.card ≤ (D + 1) * t.card := by
  first
  | (induction n with
     | zero =>
       intro s hs _
       refine ⟨∅, Finset.empty_subset s, ?_, ?_⟩
       · rw [Finset.coe_empty]
         exact Set.pairwise_empty _
       · rw [Finset.card_empty, Nat.mul_zero]
         exact hs
     | succ n ih =>
       intro s hs hD
       rcases s.eq_empty_or_nonempty with hempty | ⟨v, hv⟩
       · subst hempty
         refine ⟨∅, Finset.Subset.refl _, ?_, ?_⟩
         · rw [Finset.coe_empty]
           exact Set.pairwise_empty _
         · rw [Finset.card_empty, Nat.mul_zero]
       · have hsub : s \ insert v (s.filter (G.Adj v)) ⊆ s := Finset.sdiff_subset
         have hlt : (s \ insert v (s.filter (G.Adj v))).card < s.card
         · apply Finset.card_lt_card
           apply Finset.sdiff_ssubset
           · intro x hx
             rw [Finset.mem_insert] at hx
             rcases hx with rfl | hx
             · exact hv
             · exact (Finset.mem_filter.mp hx).1
           · exact ⟨v, Finset.mem_insert_self v _⟩
         have hD' : ∀ w ∈ s \ insert v (s.filter (G.Adj v)),
             ((s \ insert v (s.filter (G.Adj v))).filter (G.Adj w)).card ≤ D
         · intro w hw
           exact le_trans (Finset.card_le_card (Finset.filter_subset_filter _ hsub)) (hD w (hsub hw))
         obtain ⟨t', ht's, ht'ind, ht'card⟩ :=
           ih (s \ insert v (s.filter (G.Adj v))) (Nat.le_of_lt_succ (lt_of_lt_of_le hlt hs)) hD'
         have hvt' : v ∉ t'
         · intro hvt
           have h1 := ht's hvt
           rw [Finset.mem_sdiff] at h1
           exact h1.2 (Finset.mem_insert_self v _)
         have hnotadj : ∀ b ∈ t', ¬ G.Adj v b
         · intro b hb hadj
           have h1 := ht's hb
           rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_filter] at h1
           exact h1.2 (Or.inr ⟨h1.1, hadj⟩)
         refine ⟨insert v t', ?_, ?_, ?_⟩
         · intro x hx
           rw [Finset.mem_insert] at hx
           rcases hx with rfl | hx
           · exact hv
           · exact hsub (ht's hx)
         · rw [Finset.coe_insert]
           refine Set.Pairwise.insert ht'ind ?_
           intro b hb _
           exact ⟨hnotadj b hb, fun h => hnotadj b hb h.symm⟩
         · have h1 : s.card ≤ (s \ insert v (s.filter (G.Adj v))).card +
               (insert v (s.filter (G.Adj v))).card := Finset.card_le_card_sdiff_add_card
           have h2 : (insert v (s.filter (G.Adj v))).card ≤ (s.filter (G.Adj v)).card + 1 :=
             Finset.card_insert_le _ _
           have h3 : (s.filter (G.Adj v)).card ≤ D := hD v hv
           rw [Finset.card_insert_of_notMem hvt']
           first
           | (rw [Nat.mul_succ]
              omega)
           | nlinarith [ht'card, h1, h2, h3]
           | linarith [ht'card, h1, h2, h3])
  | sorry

-- N05
theorem greedy_indep_local {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) (D : ℕ)
    (hD : ∀ v ∈ s, (s.filter (G.Adj v)).card ≤ D) :
    ∃ t ⊆ s, G.IsIndepSet (t : Set V) ∧ s.card ≤ (D + 1) * t.card := by
  first
  | exact greedy_indep_local_aux G D s.card s le_rfl hD
  | exact greedy_indep_local_aux G D s.card s (le_refl _) hD
  | sorry

/-- Helper for N06/N07: an independent set in an `n`-independent-set-free graph has fewer than `n`
vertices. -/
theorem card_lt_of_isIndepSet_of_indepSetFree {V : Type*} (G : SimpleGraph V) {n : ℕ}
    (hα : G.IndepSetFree n) (t : Finset V) (ht : G.IsIndepSet (t : Set V)) : t.card < n := by
  first
  | (by_contra hge
     obtain ⟨u, hut, hucard⟩ := Finset.exists_subset_card_eq (not_lt.mp hge)
     apply hα u
     exact ⟨Set.Pairwise.mono (Finset.coe_subset.mpr hut) ht, hucard⟩)
  | (by_contra hge
     obtain ⟨u, hut, hucard⟩ := Finset.exists_subset_card_eq (not_lt.mp hge)
     apply hα u
     refine ⟨?_, hucard⟩
     intro x hx y hy hxy
     exact ht (Finset.coe_subset.mpr hut hx) (Finset.coe_subset.mpr hut hy) hxy)
  | sorry

-- N06
theorem degree_lt_of_c4_free_indepSetFree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ¬ (SimpleGraph.cycleGraph 4).IsContained G) {n : ℕ} (hα : G.IndepSetFree n) (v : V) :
    G.degree v < 2 * n := by
  first
  | (have hD : ∀ w ∈ G.neighborFinset v, ((G.neighborFinset v).filter (G.Adj w)).card ≤ 1
     · intro w hw
       rw [SimpleGraph.mem_neighborFinset] at hw
       exact c4_free_nbhd_local_degree G hG v w hw
     obtain ⟨t, hts, htind, htcard⟩ := greedy_indep_local G (G.neighborFinset v) 1 hD
     have htn : t.card < n := card_lt_of_isIndepSet_of_indepSetFree G hα t htind
     rw [← SimpleGraph.card_neighborFinset_eq_degree]
     first
     | omega
     | linarith
     | nlinarith)
  | sorry

-- N07
theorem card_le_quadratic_of_c4_free {N n : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (hG : ¬ (SimpleGraph.cycleGraph 4).IsContained G) (hα : G.IndepSetFree n) :
    N ≤ 2 * n * n := by
  first
  | (have hD : ∀ v ∈ (Finset.univ : Finset (Fin N)), (Finset.univ.filter (G.Adj v)).card ≤ 2 * n
     · intro v _
       have h1 := degree_lt_of_c4_free_indepSetFree G hG hα v
       rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter] at h1
       exact le_of_lt h1
     obtain ⟨t, hts, htind, htcard⟩ := greedy_indep_local G Finset.univ (2 * n) hD
     have htn : t.card < n := card_lt_of_isIndepSet_of_indepSetFree G hα t htind
     have h2 : t.card + 1 ≤ n := htn
     rw [Finset.card_fin] at htcard
     first
     | nlinarith [Nat.mul_le_mul (le_refl (2 * n + 1)) h2, htcard]
     | nlinarith [Nat.mul_le_mul_left (2 * n + 1) h2, htcard]
     | nlinarith [htcard, h2])
  | sorry

-- N08
theorem graphRamsey_le_of_c4_free_bound (n N : ℕ)
    (h : ∀ G : SimpleGraph (Fin N), ¬ (SimpleGraph.cycleGraph 4).IsContained G → ¬ G.IndepSetFree n) :
    SimpleGraph.graphRamsey (SimpleGraph.cycleGraph 4) (SimpleGraph.completeGraph (Fin n)) ≤ N := by
  first
  | (apply graphRamsey_le_of_forall
     intro C
     rw [complete_isContained_compl_iff]
     exact or_iff_not_imp_left.mpr (h C))
  | (apply graphRamsey_le_of_forall
     intro C
     by_cases hC : (SimpleGraph.cycleGraph 4).IsContained C
     · exact Or.inl hC
     · exact Or.inr ((complete_isContained_compl_iff C n).mpr (h C hC)))
  | sorry

-- N09
theorem graphRamsey_c4_le_quadratic (n : ℕ) :
    SimpleGraph.graphRamsey (SimpleGraph.cycleGraph 4) (SimpleGraph.completeGraph (Fin n)) ≤
      2 * n * n + 1 := by
  first
  | (apply graphRamsey_le_of_c4_free_bound
     intro G hG hα
     classical
     have h1 := card_le_quadratic_of_c4_free G hG hα
     omega)
  | (apply graphRamsey_le_of_c4_free_bound
     intro G hG hα
     classical
     have h1 := card_le_quadratic_of_c4_free G hG hα
     linarith)
  | sorry
