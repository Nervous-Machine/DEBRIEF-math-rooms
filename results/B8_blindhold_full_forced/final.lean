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
Each room's statement is the planner's statement verbatim.  The earlier blind arm's fallbacks
have been removed (B8); only the proof branches remain. -/

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
         | (simp at hxy; exact hua.ne hxy) | (simp at hxy; exact hua.ne hxy.symm)
         | (simp at hxy; exact hva.ne hxy) | (simp at hxy; exact hva.ne hxy.symm)
         | (simp at hxy; exact hub.ne hxy) | (simp at hxy; exact hub.ne hxy.symm)
         | (simp at hxy; exact hvb.ne hxy) | (simp at hxy; exact hvb.ne hxy.symm)
         | (simp at hxy; exact huv hxy) | (simp at hxy; exact huv hxy.symm)
         | (simp at hxy; exact hab hxy) | (simp at hxy; exact hab hxy.symm)
     exact ⟨⟨⟨fun i : Fin 4 => if i = 0 then u else if i = 1 then a else if i = 2 then v else b,
       fun hxy => hmap _ _ hxy⟩, hf⟩⟩)

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
         · first
           | (rw [Finset.card_empty, Nat.mul_zero]
              done)
           | (rw [Finset.card_empty, Nat.mul_zero]
              exact le_refl _)
           | (simp
              done)
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

-- N05
theorem greedy_indep_local {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) (D : ℕ)
    (hD : ∀ v ∈ s, (s.filter (G.Adj v)).card ≤ D) :
    ∃ t ⊆ s, G.IsIndepSet (t : Set V) ∧ s.card ≤ (D + 1) * t.card := by
  first
  | exact greedy_indep_local_aux G D s.card s le_rfl hD
  | exact greedy_indep_local_aux G D s.card s (le_refl _) hD

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

/-- Helper for N10: Markov step in the form needed, `c * (4m+1) ≤ n * (2m)` gives `2c ≤ n`. -/
theorem two_mul_le_of_markov (c n m : ℕ) (h : c * (4 * m + 1) ≤ n * (2 * m)) : 2 * c ≤ n := by
  first
  | nlinarith [h, Nat.zero_le m, Nat.zero_le c, Nat.zero_le n]
  | (by_contra hc
     have hc' : n + 1 ≤ 2 * c := Nat.lt_of_not_le hc
     have h2 := Nat.mul_le_mul_right (4 * m + 1) hc'
     nlinarith [h, h2, Nat.zero_le m, Nat.zero_le c, Nat.zero_le n])

-- N10
theorem turan_weak {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ t : Finset V, G.IsIndepSet (t : Set V) ∧
      Fintype.card V ^ 2 ≤ 2 * (4 * G.edgeFinset.card + Fintype.card V) * t.card := by
  first
  | (rcases Nat.eq_zero_or_pos (Fintype.card V) with hV | hV
     · refine ⟨∅, ?_, ?_⟩
       · rw [Finset.coe_empty]
         exact Set.pairwise_empty _
       · rw [hV]
         first
         | (simp
            done)
         | (norm_num
            done)
         | nlinarith
     · have hdeg : ∀ u : V, (Finset.univ.filter (G.Adj u)).card = G.degree u
       · intro u
         first
         | (rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
            done)
         | (rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
            exact rfl)
         | (simp only [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
            done)
       have hsum : ∑ u : V, G.degree u = 2 * G.edgeFinset.card :=
         SimpleGraph.sum_degrees_eq_twice_card_edges G
       have hD : ∀ v ∈ Finset.univ.filter
           (fun v => Fintype.card V * G.degree v ≤ 4 * G.edgeFinset.card),
           ((Finset.univ.filter
             (fun v => Fintype.card V * G.degree v ≤ 4 * G.edgeFinset.card)).filter (G.Adj v)).card
             ≤ 4 * G.edgeFinset.card / Fintype.card V
       · intro v hv
         rw [Finset.mem_filter] at hv
         refine le_trans (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))) ?_
         rw [hdeg v, Nat.le_div_iff_mul_le hV]
         first
         | (rw [mul_comm]
            exact hv.2)
         | linarith [hv.2]
         | exact (mul_comm _ _).le.trans hv.2
       obtain ⟨t, hts, htind, htcard⟩ := greedy_indep_local G _ _ hD
       have hsplit : (Finset.univ.filter
           (fun v => Fintype.card V * G.degree v ≤ 4 * G.edgeFinset.card)).card +
           (Finset.univ.filter
             (fun v => ¬ (Fintype.card V * G.degree v ≤ 4 * G.edgeFinset.card))).card = Fintype.card V
       · first
         | rw [Finset.card_filter_add_card_filter_not, Finset.card_univ]
         | exact (Finset.card_filter_add_card_filter_not _).trans Finset.card_univ
       have hmark : ∀ v ∈ Finset.univ.filter
           (fun v => ¬ (Fintype.card V * G.degree v ≤ 4 * G.edgeFinset.card)),
           4 * G.edgeFinset.card + 1 ≤ Fintype.card V * G.degree v
       · intro v hv
         rw [Finset.mem_filter] at hv
         first
         | exact Nat.lt_of_not_le hv.2
         | exact not_le.mp hv.2
         | omega
       have h1 := Finset.card_nsmul_le_sum _ _ _ hmark
       first
       | rw [smul_eq_mul, ← Finset.mul_sum] at h1
       | simp only [smul_eq_mul, ← Finset.mul_sum] at h1
       | simp only [nsmul_eq_mul, Nat.cast_id, ← Finset.mul_sum] at h1
       have h2 : ∑ v ∈ Finset.univ.filter
           (fun v => ¬ (Fintype.card V * G.degree v ≤ 4 * G.edgeFinset.card)), G.degree v ≤
           ∑ v : V, G.degree v :=
         Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
       rw [hsum] at h2
       have h3 := le_trans h1 (Nat.mul_le_mul_left (Fintype.card V) h2)
       have h4 := two_mul_le_of_markov _ _ _ h3
       have hDn : 4 * G.edgeFinset.card / Fintype.card V * Fintype.card V ≤ 4 * G.edgeFinset.card :=
         Nat.div_mul_le_self _ _
       refine ⟨t, htind, ?_⟩
       have h5 := Nat.mul_le_mul_left (Fintype.card V) htcard
       have h6 := Nat.mul_le_mul_right t.card hDn
       have h7 : Fintype.card V ≤ 2 * (Finset.univ.filter
           (fun v => Fintype.card V * G.degree v ≤ 4 * G.edgeFinset.card)).card
       · omega
       have h8 := Nat.mul_le_mul_left (Fintype.card V) h7
       first
       | nlinarith [h4, h5, h6, h7, h8, hsplit]
       | linarith [h4, h5, h6, h7, h8, hsplit])

/-- Helper for N11: removing `v` from `s` loses at most one neighbour of `u`, and only if `u ~ v`. -/
theorem filter_card_le_erase_add {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Finset V) (u v : V) :
    (s.filter (G.Adj u)).card ≤
      ((s.erase v).filter (G.Adj u)).card + (if G.Adj u v then 1 else 0) := by
  first
  | (by_cases h : G.Adj u v
     · rw [if_pos h]
       refine le_trans (Finset.card_le_card ?_) (Finset.card_insert_le v _)
       intro x hx
       rw [Finset.mem_filter] at hx
       rw [Finset.mem_insert, Finset.mem_filter, Finset.mem_erase]
       by_cases hxv : x = v
       · exact Or.inl hxv
       · exact Or.inr ⟨⟨hxv, hx.1⟩, hx.2⟩
     · rw [if_neg h, Nat.add_zero]
       apply Finset.card_le_card
       intro x hx
       rw [Finset.mem_filter] at hx
       rw [Finset.mem_filter, Finset.mem_erase]
       refine ⟨⟨?_, hx.1⟩, hx.2⟩
       intro hxv
       subst hxv
       exact h hx.2)

/-- Helper for N11: the degree sum inside `s` drops by at most `2 deg_s(v)` when `v` is removed. -/
theorem phi_le_phi_erase_add {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Finset V) (v : V) (hv : v ∈ s) :
    ∑ u ∈ s, (s.filter (G.Adj u)).card ≤
      (∑ u ∈ s.erase v, ((s.erase v).filter (G.Adj u)).card) + 2 * (s.filter (G.Adj v)).card := by
  first
  | (have hsum : (∑ u ∈ s, (s.filter (G.Adj u)).card) =
         (s.filter (G.Adj v)).card + ∑ u ∈ s.erase v, (s.filter (G.Adj u)).card :=
       (Finset.add_sum_erase s (fun u => (s.filter (G.Adj u)).card) hv).symm
     have h2 : (∑ u ∈ s.erase v, (s.filter (G.Adj u)).card) ≤
         ∑ u ∈ s.erase v, (((s.erase v).filter (G.Adj u)).card + (if G.Adj u v then 1 else 0)) :=
       Finset.sum_le_sum (fun u _ => filter_card_le_erase_add G s u v)
     rw [Finset.sum_add_distrib] at h2
     have h3 : (∑ u ∈ s.erase v, (if G.Adj u v then 1 else 0)) =
         ((s.erase v).filter (fun u => G.Adj u v)).card :=
       (Finset.card_filter (fun u => G.Adj u v) (s.erase v)).symm
     have h4 : ((s.erase v).filter (fun u => G.Adj u v)).card ≤ (s.filter (G.Adj v)).card
     · apply Finset.card_le_card
       intro x hx
       rw [Finset.mem_filter, Finset.mem_erase] at hx
       rw [Finset.mem_filter]
       exact ⟨hx.1.2, hx.2.symm⟩
     first
     | omega
     | linarith [hsum, h2, h3, h4])

/-- Helper for N11: the dense-core extraction, by induction on an upper bound for the cardinality. -/
theorem exists_dense_core_aux {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) (n : ℕ) :
    ∀ s : Finset V, s.card ≤ n → s.Nonempty →
      2 * d * s.card ≤ ∑ u ∈ s, (s.filter (G.Adj u)).card →
      ∃ t ⊆ s, t.Nonempty ∧ ∀ v ∈ t, d ≤ (t.filter (G.Adj v)).card := by
  first
  | (induction n with
     | zero =>
       intro s hs hne _
       have h1 : 0 < s.card := Finset.card_pos.mpr hne
       omega
     | succ n ih =>
       intro s hs hne hΦ
       by_cases hall : ∀ v ∈ s, d ≤ (s.filter (G.Adj v)).card
       · exact ⟨s, Finset.Subset.refl s, hne, hall⟩
       · push_neg at hall
         obtain ⟨v, hv, hdeg⟩ := hall
         have hphi := phi_le_phi_erase_add G s v hv
         have hcard : s.card = (s.erase v).card + 1 := (Finset.card_erase_add_one hv).symm
         rw [hcard, Nat.mul_succ] at hΦ
         have hs'ne : (s.erase v).Nonempty
         · by_contra hemp
           rw [Finset.not_nonempty_iff_eq_empty] at hemp
           simp only [hemp, Finset.sum_empty, Finset.card_empty, Nat.mul_zero, mul_zero,
             Nat.zero_add, zero_add, Nat.add_zero, add_zero] at hphi hΦ
           omega
         have hΦ' : 2 * d * (s.erase v).card ≤ ∑ u ∈ s.erase v, ((s.erase v).filter (G.Adj u)).card
         · first
           | omega
           | linarith [hΦ, hphi, hdeg]
         have hle : (s.erase v).card ≤ n :=
           Nat.le_of_lt_succ (lt_of_lt_of_le (Finset.card_erase_lt_of_mem hv) hs)
         obtain ⟨t, hts, htne, ht⟩ := ih (s.erase v) hle hs'ne hΦ'
         exact ⟨t, Finset.Subset.trans hts (Finset.erase_subset v s), htne, ht⟩)

-- N11
theorem exists_dense_core {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
    (hd : d * Fintype.card V ≤ G.edgeFinset.card) :
    ∃ s : Finset V, s.Nonempty ∧ ∀ v ∈ s, d ≤ (s.filter (G.Adj v)).card := by
  first
  | (have hdeg : ∀ u ∈ (Finset.univ : Finset V), (Finset.univ.filter (G.Adj u)).card = G.degree u
     · intro u _
       first
       | (rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
          done)
       | (rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
          exact rfl)
       | (simp only [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
          done)
     have hΦ : 2 * d * (Finset.univ : Finset V).card ≤
         ∑ u ∈ (Finset.univ : Finset V), ((Finset.univ : Finset V).filter (G.Adj u)).card
     · rw [Finset.sum_congr rfl hdeg, SimpleGraph.sum_degrees_eq_twice_card_edges, Finset.card_univ]
       first
       | (rw [mul_assoc]
          omega)
       | linarith [hd]
       | nlinarith [hd]
     obtain ⟨t, _, htne, ht⟩ :=
       exists_dense_core_aux G d (Finset.univ : Finset V).card Finset.univ le_rfl
         Finset.univ_nonempty hΦ
     exact ⟨t, htne, ht⟩)

-- N12
theorem moore_bound_c4_free {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ¬ (SimpleGraph.cycleGraph 4).IsContained G) (s : Finset V) (d : ℕ) (hs : s.Nonempty)
    (hmin : ∀ v ∈ s, d ≤ (s.filter (G.Adj v)).card) :
    d * d ≤ 2 * s.card := by
  first
  | (obtain ⟨v, hv⟩ := hs
     rcases d with _ | d'
     · first
       | omega
       | (simp
          done)
       | exact Nat.zero_le _
     · have hA : d' + 1 ≤ (s.filter (G.Adj v)).card := hmin v hv
       have hAs : (s.filter (G.Adj v)).card ≤ s.card := Finset.card_le_card (Finset.filter_subset _ s)
       have hsub : (s.filter (G.Adj v)).biUnion (fun a => (s.filter (G.Adj a)).erase v) ⊆ s
       · intro x hx
         rw [Finset.mem_biUnion] at hx
         obtain ⟨a, _, hx⟩ := hx
         exact (Finset.mem_filter.mp (Finset.mem_of_mem_erase hx)).1
       have hdisj : ((s.filter (G.Adj v) : Finset V) : Set V).PairwiseDisjoint
           (fun a => (s.filter (G.Adj a)).erase v)
       · intro a ha a' ha' hne
         have ha1 := Finset.mem_filter.mp (Finset.mem_coe.mp ha)
         have ha1' := Finset.mem_filter.mp (Finset.mem_coe.mp ha')
         show Disjoint ((s.filter (G.Adj a)).erase v) ((s.filter (G.Adj a')).erase v)
         rw [Finset.disjoint_left]
         intro x hx hx'
         rw [Finset.mem_erase, Finset.mem_filter] at hx hx'
         exact hG (c4_of_common_nbrs G hne ha1.2.symm ha1'.2.symm hx.2.2 hx'.2.2
           (fun h => hx.1 h.symm))
       have hlow : ∀ a ∈ s.filter (G.Adj v), d' ≤ ((s.filter (G.Adj a)).erase v).card
       · intro a ha
         have ha1 := Finset.mem_filter.mp ha
         have hva : v ∈ s.filter (G.Adj a) := Finset.mem_filter.mpr ⟨hv, ha1.2.symm⟩
         have h1 := Finset.card_erase_of_mem hva
         have h2 := hmin a ha1.1
         omega
       have h1 := Finset.card_nsmul_le_sum (s.filter (G.Adj v))
         (fun a => ((s.filter (G.Adj a)).erase v).card) d' hlow
       first
       | rw [smul_eq_mul] at h1
       | simp only [smul_eq_mul] at h1
       | simp only [nsmul_eq_mul, Nat.cast_id] at h1
       rw [← Finset.card_biUnion hdisj] at h1
       have h2 := Finset.card_le_card hsub
       have h3 : (d' + 1) * d' ≤ (s.filter (G.Adj v)).card * d' := Nat.mul_le_mul_right d' hA
       first
       | nlinarith [h1, h2, h3, hA, hAs]
       | linarith [h1, h2, h3, hA, hAs])

-- N13 (open core: left open; see NOTES.md)
theorem core_near_extremal :
    ∃ δ η : ℝ, 0 < δ ∧ δ ≤ 1 / 8 ∧ 4 * δ ≤ η ∧ ∀ κ : ℝ, 0 < κ → ∃ K : ℝ, 0 < K ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V),
        ¬ (SimpleGraph.cycleGraph 4).IsContained G →
        (∀ v ∈ s, κ * (s.card : ℝ) ^ ((1 : ℝ) / 2 - δ) ≤ ((s.filter (G.Adj v)).card : ℝ)) →
        ∃ t ⊆ s, G.IsIndepSet (t : Set V) ∧ K * (s.card : ℝ) ^ ((1 : ℝ) / 2 + η) ≤ (t.card : ℝ) := by
  sorry

-- N14
theorem sparse_branch_arith (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (N E t : ℝ) (hN : 1 ≤ N)
    (hE0 : 0 ≤ E) (hE : E ≤ N ^ ((3 : ℝ) / 2 - δ)) (ht : N ^ 2 ≤ 2 * (4 * E + N) * t) :
    N ^ ((1 : ℝ) / 2 + δ) ≤ 10 * t := by
  first
  | (have hNpos : 0 < N := lt_of_lt_of_le one_pos hN
     have hexp : (1 : ℝ) ≤ (3 : ℝ) / 2 - δ
     · linarith
     have hB : N ≤ N ^ ((3 : ℝ) / 2 - δ)
     · have h1 : N ^ (1 : ℝ) ≤ N ^ ((3 : ℝ) / 2 - δ) := Real.rpow_le_rpow_of_exponent_le hN hexp
       rw [Real.rpow_one] at h1
       exact h1
     have hBpos : 0 < N ^ ((3 : ℝ) / 2 - δ) := Real.rpow_pos_of_pos hNpos _
     have hAB : N ^ ((1 : ℝ) / 2 + δ) * N ^ ((3 : ℝ) / 2 - δ) = N ^ 2
     · rw [← Real.rpow_add hNpos]
       have h2 : (1 : ℝ) / 2 + δ + ((3 : ℝ) / 2 - δ) = 2
       · ring
       rw [h2]
       exact Real.rpow_two N
     have h3 : (0 : ℝ) ≤ 2 * (4 * E + N)
     · linarith
     have ht0 : 0 < t
     · by_contra h0
       push_neg at h0
       nlinarith [mul_nonneg h3 (neg_nonneg.mpr h0), hN, ht]
     have h5 : N ^ ((1 : ℝ) / 2 + δ) * N ^ ((3 : ℝ) / 2 - δ) ≤ (10 * t) * N ^ ((3 : ℝ) / 2 - δ)
     · rw [hAB]
       first
       | linarith [ht, mul_le_mul_of_nonneg_right hE ht0.le, mul_le_mul_of_nonneg_right hB ht0.le]
       | nlinarith [ht, hE, hB, ht0.le, mul_le_mul_of_nonneg_right hE ht0.le,
           mul_le_mul_of_nonneg_right hB ht0.le]
     exact le_of_mul_le_mul_right h5 hBpos)

-- N15
theorem dense_branch_arith (δ η K : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 8) (hη : 4 * δ ≤ η) (hK : 0 < K)
    (N M : ℝ) (hN : 1 ≤ N) (hM : 0 ≤ M) (hNM : N ^ (1 - 2 * δ) ≤ 8 * M) :
    K * (8 : ℝ) ^ (-((1 : ℝ) / 2 + η)) * N ^ ((1 : ℝ) / 2 + η / 2) ≤ K * M ^ ((1 : ℝ) / 2 + η) := by
  first
  | (have hNpos : 0 < N := lt_of_lt_of_le one_pos hN
     have hexp : (1 : ℝ) / 2 + η / 2 ≤ (1 - 2 * δ) * ((1 : ℝ) / 2 + η)
     · nlinarith [mul_nonneg (sub_nonneg.mpr hη) (sub_nonneg.mpr hδ'),
         mul_nonneg hδ.le (sub_nonneg.mpr hη), mul_nonneg hδ.le (sub_nonneg.mpr hδ')]
     have hpos : (0 : ℝ) ≤ (1 : ℝ) / 2 + η
     · linarith
     have h8 : (0 : ℝ) ≤ 8
     · norm_num
     have h8' : (0 : ℝ) < 8
     · norm_num
     have h1 : N ^ ((1 : ℝ) / 2 + η / 2) ≤ N ^ ((1 - 2 * δ) * ((1 : ℝ) / 2 + η)) :=
       Real.rpow_le_rpow_of_exponent_le hN hexp
     have h2 : N ^ ((1 - 2 * δ) * ((1 : ℝ) / 2 + η)) = (N ^ (1 - 2 * δ)) ^ ((1 : ℝ) / 2 + η) :=
       Real.rpow_mul hNpos.le _ _
     have h3 : (N ^ (1 - 2 * δ)) ^ ((1 : ℝ) / 2 + η) ≤ (8 * M) ^ ((1 : ℝ) / 2 + η) :=
       Real.rpow_le_rpow (Real.rpow_nonneg hNpos.le _) hNM hpos
     have h4 : (8 * M) ^ ((1 : ℝ) / 2 + η) =
         (8 : ℝ) ^ ((1 : ℝ) / 2 + η) * M ^ ((1 : ℝ) / 2 + η) :=
       Real.mul_rpow h8 hM
     have h5 : (8 : ℝ) ^ (-((1 : ℝ) / 2 + η)) = ((8 : ℝ) ^ ((1 : ℝ) / 2 + η))⁻¹ :=
       Real.rpow_neg h8 _
     have h6 : 0 < (8 : ℝ) ^ ((1 : ℝ) / 2 + η) := Real.rpow_pos_of_pos h8' _
     have h7 : N ^ ((1 : ℝ) / 2 + η / 2) ≤
         (8 : ℝ) ^ ((1 : ℝ) / 2 + η) * M ^ ((1 : ℝ) / 2 + η) :=
       h1.trans (h2.le.trans (h3.trans h4.le))
     have h9 : ((8 : ℝ) ^ ((1 : ℝ) / 2 + η))⁻¹ * N ^ ((1 : ℝ) / 2 + η / 2) ≤ M ^ ((1 : ℝ) / 2 + η) :=
       le_trans (mul_le_mul_of_nonneg_left h7 (inv_nonneg.mpr h6.le))
         (le_of_eq (inv_mul_cancel_left₀ h6.ne' _))
     rw [h5, mul_assoc]
     exact mul_le_mul_of_nonneg_left h9 hK.le)

/-- Helper for N16: the sparse branch, N10 (Turán-type bound) fed into N14. -/
theorem c4_free_indep_sparse (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (N : ℕ) (hN : 1 ≤ N)
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (hE : (G.edgeFinset.card : ℝ) ≤ (N : ℝ) ^ ((3 : ℝ) / 2 - δ)) :
    ∃ t : Finset (Fin N), G.IsIndepSet (t : Set (Fin N)) ∧
      (N : ℝ) ^ ((1 : ℝ) / 2 + δ) ≤ 10 * (t.card : ℝ) := by
  obtain ⟨t, htind, htcard⟩ := turan_weak G
  refine ⟨t, htind, ?_⟩
  rw [Fintype.card_fin] at htcard
  have hN' : (1 : ℝ) ≤ (N : ℝ) := Nat.one_le_cast.mpr hN
  have hE0 : (0 : ℝ) ≤ (G.edgeFinset.card : ℝ) := Nat.cast_nonneg _
  have ht : (N : ℝ) ^ 2 ≤ 2 * (4 * (G.edgeFinset.card : ℝ) + (N : ℝ)) * (t.card : ℝ) := by
    exact_mod_cast htcard
  exact sparse_branch_arith δ hδ hδ' (N : ℝ) (G.edgeFinset.card : ℝ) (t.card : ℝ) hN' hE0 hE ht

/-- Helper for N16: the dense branch.  From `N^(3/2-δ) < E`, N11 with `d = ⌊N^(1/2-δ)⌋₊` gives a
core `s` of minimum degree `≥ d`; N12 gives `N^(1-2δ) ≤ 8 |s|`; the N13 data with `κ = 1/2` gives
the independent set inside `s`; N15 converts the bound in `|s|` into a bound in `N`. -/
theorem c4_free_indep_dense (δ η K : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 8) (hη : 4 * δ ≤ η) (hK : 0 < K)
    (h13 : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (s : Finset V), ¬ (SimpleGraph.cycleGraph 4).IsContained G →
        (∀ v ∈ s, (1 / 2 : ℝ) * (s.card : ℝ) ^ ((1 : ℝ) / 2 - δ) ≤ ((s.filter (G.Adj v)).card : ℝ)) →
        ∃ t ⊆ s, G.IsIndepSet (t : Set V) ∧ K * (s.card : ℝ) ^ ((1 : ℝ) / 2 + η) ≤ (t.card : ℝ))
    (N : ℕ) (hN : 1 ≤ N) (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (hG : ¬ (SimpleGraph.cycleGraph 4).IsContained G)
    (hE : (N : ℝ) ^ ((3 : ℝ) / 2 - δ) < (G.edgeFinset.card : ℝ)) :
    ∃ t : Finset (Fin N), G.IsIndepSet (t : Set (Fin N)) ∧
      K * (8 : ℝ) ^ (-((1 : ℝ) / 2 + η)) * (N : ℝ) ^ ((1 : ℝ) / 2 + η / 2) ≤ (t.card : ℝ) := by
  have hN' : (1 : ℝ) ≤ (N : ℝ) := Nat.one_le_cast.mpr hN
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le one_pos hN'
  have hexp0 : (0 : ℝ) ≤ (1 : ℝ) / 2 - δ := by linarith
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (N : ℝ) ^ ((1 : ℝ) / 2 - δ) := ⟨_, rfl⟩
  have hx1 : (1 : ℝ) ≤ x := by
    rw [hx]
    exact Real.one_le_rpow hN' hexp0
  have hx0 : (0 : ℝ) ≤ x := le_trans zero_le_one hx1
  obtain ⟨d, hd⟩ : ∃ d : ℕ, d = ⌊x⌋₊ := ⟨_, rfl⟩
  have hd1 : 0 < d := by
    rw [hd]
    exact Nat.floor_pos.mpr hx1
  have hdx : (d : ℝ) ≤ x := by
    rw [hd]
    exact Nat.floor_le hx0
  have hxd : x < (d : ℝ) + 1 := by
    rw [hd]
    exact Nat.lt_floor_add_one x
  have hd1' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
  have hxd2 : x / 2 ≤ (d : ℝ) := by linarith
  have hdN : (d : ℝ) * (N : ℝ) ≤ (G.edgeFinset.card : ℝ) := by
    have h1 : x * (N : ℝ) = (N : ℝ) ^ ((3 : ℝ) / 2 - δ) := by
      rw [hx, ← Real.rpow_add_one hNpos.ne']
      congr 1
      ring
    have h2 : (d : ℝ) * (N : ℝ) ≤ x * (N : ℝ) := mul_le_mul_of_nonneg_right hdx hNpos.le
    linarith
  have hdN' : d * Fintype.card (Fin N) ≤ G.edgeFinset.card := by
    rw [Fintype.card_fin]
    exact_mod_cast hdN
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨s, hsne, hsmin⟩ := exists_dense_core G d hdN'
  have hmoore : d * d ≤ 2 * s.card := moore_bound_c4_free G hG s d hsne hsmin
  have hsN : s.card ≤ N := by
    have h1 := Finset.card_le_univ s
    rwa [Fintype.card_fin] at h1
  have hsN' : (s.card : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hsN
  have hs0 : (0 : ℝ) ≤ (s.card : ℝ) := Nat.cast_nonneg _
  have hdeg : ∀ v ∈ s,
      (1 / 2 : ℝ) * (s.card : ℝ) ^ ((1 : ℝ) / 2 - δ) ≤ ((s.filter (G.Adj v)).card : ℝ) := by
    intro v hv
    have h1 : (s.card : ℝ) ^ ((1 : ℝ) / 2 - δ) ≤ x := by
      rw [hx]
      exact Real.rpow_le_rpow hs0 hsN' hexp0
    have h2 : (d : ℝ) ≤ ((s.filter (G.Adj v)).card : ℝ) := Nat.cast_le.mpr (hsmin v hv)
    linarith
  obtain ⟨t, _, htind, htcard⟩ := h13 (Fin N) G s hG hdeg
  refine ⟨t, htind, ?_⟩
  have hmoore' : (d : ℝ) * (d : ℝ) ≤ 2 * (s.card : ℝ) := by exact_mod_cast hmoore
  have hNM : (N : ℝ) ^ (1 - 2 * δ) ≤ 8 * (s.card : ℝ) := by
    have h1 : (N : ℝ) ^ (1 - 2 * δ) = x ^ (2 : ℝ) := by
      rw [hx, ← Real.rpow_mul hNpos.le]
      congr 1
      ring
    rw [h1, Real.rpow_two]
    have h3 : (x / 2) * (x / 2) ≤ (d : ℝ) * (d : ℝ) :=
      mul_le_mul hxd2 hxd2 (by linarith) (by linarith)
    nlinarith [h3, hmoore']
  have h15 := dense_branch_arith δ η K hδ hδ' hη hK (N : ℝ) (s.card : ℝ) hN' hs0 hNM
  exact le_trans h15 htcard

-- N16 (join over N10–N15; rests on the open room N13, which is left open; see NOTES.md)
theorem c4_free_indep_power :
    ∃ ε K : ℝ, 0 < ε ∧ 0 < K ∧ ∀ (N : ℕ) (G : SimpleGraph (Fin N)) [DecidableRel G.Adj],
      ¬ (SimpleGraph.cycleGraph 4).IsContained G →
      ∃ t : Finset (Fin N), G.IsIndepSet (t : Set (Fin N)) ∧ K * (N : ℝ) ^ ((1 : ℝ) / 2 + ε) ≤ (t.card : ℝ) := by
  obtain ⟨δ, η, hδ, hδ', hη, h13⟩ := core_near_extremal
  obtain ⟨K', hK', h13'⟩ := h13 (1 / 2 : ℝ) (by norm_num)
  have hK8 : 0 < K' * (8 : ℝ) ^ (-((1 : ℝ) / 2 + η)) :=
    mul_pos hK' (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨δ, min (1 / 10) (K' * (8 : ℝ) ^ (-((1 : ℝ) / 2 + η))), hδ, lt_min (by norm_num) hK8, ?_⟩
  intro N G inst hG
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    refine ⟨∅, ?_, ?_⟩
    · rw [Finset.coe_empty]
      exact Set.pairwise_empty _
    · have hne : ((1 : ℝ) / 2 + δ) ≠ 0 := (by linarith : (0 : ℝ) < (1 : ℝ) / 2 + δ).ne'
      rw [Finset.card_empty, Nat.cast_zero, Real.zero_rpow hne, mul_zero]
  · have hN' : (1 : ℝ) ≤ (N : ℝ) := Nat.one_le_cast.mpr hNpos
    have hpow0 : (0 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 + δ) := Real.rpow_nonneg (Nat.cast_nonneg N) _
    rcases le_or_gt (G.edgeFinset.card : ℝ) ((N : ℝ) ^ ((3 : ℝ) / 2 - δ)) with hE | hE
    · obtain ⟨t, htind, ht⟩ := c4_free_indep_sparse δ hδ (by linarith) N hNpos G hE
      refine ⟨t, htind, ?_⟩
      have h1 : min (1 / 10) (K' * (8 : ℝ) ^ (-((1 : ℝ) / 2 + η))) * (N : ℝ) ^ ((1 : ℝ) / 2 + δ) ≤
          (1 / 10) * (N : ℝ) ^ ((1 : ℝ) / 2 + δ) :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) hpow0
      linarith
    · obtain ⟨t, htind, ht⟩ := c4_free_indep_dense δ η K' hδ hδ' hη hK' h13' N hNpos G hG hE
      refine ⟨t, htind, ?_⟩
      have h1 : (N : ℝ) ^ ((1 : ℝ) / 2 + δ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 + η / 2) :=
        Real.rpow_le_rpow_of_exponent_le hN' (by linarith)
      have h2 : min (1 / 10) (K' * (8 : ℝ) ^ (-((1 : ℝ) / 2 + η))) * (N : ℝ) ^ ((1 : ℝ) / 2 + δ) ≤
          (K' * (8 : ℝ) ^ (-((1 : ℝ) / 2 + η))) * (N : ℝ) ^ ((1 : ℝ) / 2 + η / 2) :=
        mul_le_mul (min_le_right _ _) h1 hpow0 hK8.le
      linarith

-- N17
theorem rpow_inversion (K ε N x : ℝ) (hK : 0 < K) (hε : 0 < ε) (hN : 0 ≤ N) (hx : 0 ≤ x)
    (h : K * N ^ ((1 : ℝ) / 2 + ε) ≤ x) :
    N ≤ K ^ (-(2 / (1 + 2 * ε))) * x ^ (2 - 4 * ε / (1 + 2 * ε)) := by
  first
  | (have hden' : (0 : ℝ) < 1 + 2 * ε
     · linarith
     have hden : (1 + 2 * ε : ℝ) ≠ 0 := hden'.ne'
     have hp : (0 : ℝ) < (1 : ℝ) / 2 + ε
     · linarith
     have e1 : (2 : ℝ) / (1 + 2 * ε) = 2 - 4 * ε / (1 + 2 * ε)
     · first
       | (field_simp
          ring)
       | field_simp
       | (rw [eq_sub_iff_add_eq, div_add_div_same, div_eq_iff hden]
          ring)
     have e2 : ((1 : ℝ) / 2 + ε) * (2 - 4 * ε / (1 + 2 * ε)) = 1
     · first
       | (field_simp
          ring)
       | field_simp
     have hq0 : (0 : ℝ) ≤ 2 - 4 * ε / (1 + 2 * ε)
     · rw [← e1]
       exact div_nonneg zero_le_two hden'.le
     have hNp : 0 ≤ N ^ ((1 : ℝ) / 2 + ε) := Real.rpow_nonneg hN _
     have h1 : N ^ ((1 : ℝ) / 2 + ε) ≤ x / K
     · first
       | (rw [le_div_iff₀ hK, mul_comm]
          exact h)
       | (rw [le_div_iff₀' hK]
          exact h)
     have h2 : (N ^ ((1 : ℝ) / 2 + ε)) ^ (2 - 4 * ε / (1 + 2 * ε)) ≤
         (x / K) ^ (2 - 4 * ε / (1 + 2 * ε)) :=
       Real.rpow_le_rpow hNp h1 hq0
     rw [← Real.rpow_mul hN, e2, Real.rpow_one, Real.div_rpow hx hK.le] at h2
     rw [e1, Real.rpow_neg hK.le]
     first
     | (rw [div_eq_inv_mul] at h2
        exact h2)
     | (rw [div_eq_mul_inv] at h2
        exact h2.trans (mul_comm _ _).le)
     | linarith [h2])

-- N18 (join over N16, N17; inherits N16, which is left open)
theorem card_le_power_of_c4_free :
    ∃ c C : ℝ, 0 < c ∧ c ≤ 2 ∧ 0 ≤ C ∧ ∀ (n N : ℕ) (G : SimpleGraph (Fin N)) [DecidableRel G.Adj], 1 ≤ n →
      ¬ (SimpleGraph.cycleGraph 4).IsContained G → G.IndepSetFree n → (N : ℝ) ≤ C * (n : ℝ) ^ (2 - c) := by
  first
  | (obtain ⟨ε, K, hε, hK, hind⟩ := c4_free_indep_power
     have hden : (0 : ℝ) < 1 + 2 * ε
     · linarith
     have h4 : (0 : ℝ) < 4 * ε
     · linarith
     refine ⟨4 * ε / (1 + 2 * ε), K ^ (-(2 / (1 + 2 * ε))), div_pos h4 hden, ?_,
       (Real.rpow_pos_of_pos hK _).le, ?_⟩
     · rw [div_le_iff₀ hden]
       linarith
     · intro n N G inst hn hG hα
       obtain ⟨t, htind, htcard⟩ := hind N G hG
       have htn : t.card < n := card_lt_of_isIndepSet_of_indepSetFree G hα t htind
       have htn' : (t.card : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr htn.le
       have hx : K * (N : ℝ) ^ ((1 : ℝ) / 2 + ε) ≤ (n : ℝ) := le_trans htcard htn'
       exact rpow_inversion K ε (N : ℝ) (n : ℝ) hK hε (Nat.cast_nonneg N) (Nat.cast_nonneg n) hx)

-- N19
theorem floor_succ_le_power (c C x : ℝ) (hc : c ≤ 2) (hC : 0 ≤ C) (n : ℕ) (hn : 1 ≤ n)
    (hx : x ≤ C * (n : ℝ) ^ (2 - c)) :
    ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ (C + 1) * (n : ℝ) ^ (2 - c) := by
  first
  | (have hn' : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
     have h2c : (0 : ℝ) ≤ 2 - c
     · linarith
     have hpow : (1 : ℝ) ≤ (n : ℝ) ^ (2 - c) := Real.one_le_rpow hn' h2c
     have hCP : 0 ≤ C * (n : ℝ) ^ (2 - c) := mul_nonneg hC (le_trans zero_le_one hpow)
     first
     | rw [Nat.cast_add, Nat.cast_one]
     | push_cast
     rcases le_or_gt 0 x with hx0 | hx0
     · have hfl : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
       first
       | linarith [hfl, hx, hpow, hCP]
       | nlinarith [hfl, hx, hpow, hC, hCP]
     · have hx1 : x < 1
       · linarith
       have hfl : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr hx1
       rw [hfl, Nat.cast_zero, zero_add]
       first
       | linarith [hpow, hCP]
       | nlinarith [hpow, hC, hCP])

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
  first
  | (obtain ⟨c, C, hc, hc2, hC, hbound⟩ := card_le_power_of_c4_free
     refine ⟨c, hc, C + 1, ?_⟩
     intro n hn
     have hle : SimpleGraph.graphRamsey (SimpleGraph.cycleGraph 4) (SimpleGraph.completeGraph (Fin n)) ≤
         ⌊C * (n : ℝ) ^ (2 - c)⌋₊ + 1
     · apply graphRamsey_le_of_c4_free_bound
       intro G hG hα
       classical
       have h1 := hbound n _ G hn hG hα
       have h2 := Nat.lt_floor_add_one (C * (n : ℝ) ^ (2 - c))
       push_cast at h1
       linarith
     have h3 := floor_succ_le_power c C (C * (n : ℝ) ^ (2 - c)) hc2 hC n hn le_rfl
     have h4 : ((SimpleGraph.graphRamsey (SimpleGraph.cycleGraph 4)
         (SimpleGraph.completeGraph (Fin n)) : ℕ) : ℝ) ≤ ((⌊C * (n : ℝ) ^ (2 - c)⌋₊ + 1 : ℕ) : ℝ) :=
       Nat.cast_le.mpr hle
     exact le_trans h4 h3)

end Erdos159
