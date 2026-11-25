/-
Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 Wentao Li.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib

/-!
# Challenge: Erdős Problem 766, the Dirac–Erdős bound

Copied verbatim from `FormalConjectures/ErdosProblems/766.lean` in google-deepmind/formal-conjectures at commit `691719db2653905d5fa0775408370fb058e4c59f` (The Formal Conjectures Authors, Apache-2.0). Only imports, attributes, test lemmas and unrelated declarations are left out.
The `sorry` marks the statement to be proved; it is not a proof.
-/

@[expose] public section

open Filter
open scoped SimpleGraph

namespace Erdos766

/-- $f(n;k,l)$ in the sense of [Er64c], where it is called $f_1(n;k,l)$: the least $m$ such that
every graph with $n$ vertices and $m$ edges contains at least one graph with $k$ vertices and
$l$ edges as a (not necessarily induced) subgraph. There is no graph with $n$ vertices and more
than $\binom{n}{2}$ edges, so the set is nonempty. -/
noncomputable def forcingNumber (n k l : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G}

/-! ### Arithmetic helpers -/

theorem sq_two_mul_div_four (m : ℕ) : (2 * m) ^ 2 / 4 = m ^ 2 := by
  have h : (2 * m) ^ 2 = m ^ 2 * 4 := by ring
  rw [h]
  exact Nat.mul_div_cancel _ (by norm_num)

theorem sq_two_mul_add_one_div_four (m : ℕ) : (2 * m + 1) ^ 2 / 4 = m ^ 2 + m := by
  have h : (2 * m + 1) ^ 2 = 4 * (m ^ 2 + m) + 1 := by ring
  omega

/-! ### N1 -/

theorem two_mul_sq_div_four_succ_lt (N : ℕ) (hN : 4 ≤ N) :
    2 * (N ^ 2 / 4 + 1) < N * (N / 2 + 1) := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' N
  · have hm : 2 ≤ m := by omega
    have h2 : 2 * m / 2 = m := by omega
    rw [sq_two_mul_div_four, h2]
    nlinarith [hm]
  · have hm : 2 ≤ m := by omega
    have h2 : (2 * m + 1) / 2 = m := by omega
    rw [sq_two_mul_add_one_div_four, h2]
    nlinarith [hm]

/-! ### N2 -/

theorem sq_div_four_eq_pred_sq_div_four_add_half (N : ℕ) (hN : 1 ≤ N) :
    N ^ 2 / 4 = (N - 1) ^ 2 / 4 + N / 2 := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' N
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have e1 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
    have e2 : 2 * (k + 1) / 2 = k + 1 := by omega
    rw [e1, e2, sq_two_mul_div_four, sq_two_mul_add_one_div_four]
    ring
  · have e1 : 2 * m + 1 - 1 = 2 * m := by omega
    have e2 : (2 * m + 1) / 2 = m := by omega
    rw [e1, e2, sq_two_mul_div_four, sq_two_mul_add_one_div_four]

/-! ### N3 -/

theorem low_degree_arith (N e d : ℕ) (hN : 4 ≤ N) (he : N ^ 2 / 4 + 1 ≤ e)
    (hd : N * d ≤ 2 * e) : d + (N - 1) ^ 2 / 4 + 1 ≤ e := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' N
  · obtain ⟨a, rfl⟩ : ∃ a, m = a + 2 := ⟨m - 2, by omega⟩
    have e1 : 2 * (a + 2) - 1 = 2 * a + 3 := by omega
    have e3 : (2 * a + 3) ^ 2 / 4 = a ^ 2 + 3 * a + 2 := by
      have h : (2 * a + 3) ^ 2 = 4 * (a ^ 2 + 3 * a + 2) + 1 := by ring
      omega
    have e4 : (a + 2) ^ 2 = a ^ 2 + 4 * a + 4 := by ring
    rw [sq_two_mul_div_four, e4] at he
    rw [e1, e3]
    by_contra hcon
    push_neg at hcon
    have hd' : a + 3 ≤ d := by omega
    have hkey := Nat.mul_le_mul_left (a + 1) hd'
    nlinarith [hkey, hd, hcon, he]
  · obtain ⟨a, rfl⟩ : ∃ a, m = a + 2 := ⟨m - 2, by omega⟩
    have e1 : 2 * (a + 2) + 1 - 1 = 2 * (a + 2) := by omega
    have e4 : (a + 2) ^ 2 = a ^ 2 + 4 * a + 4 := by ring
    rw [sq_two_mul_add_one_div_four, e4] at he
    rw [e1, sq_two_mul_div_four, e4]
    by_contra hcon
    push_neg at hcon
    have hd' : a + 3 ≤ d := by omega
    have hkey := Nat.mul_le_mul_left (2 * a + 3) hd'
    nlinarith [hkey, hd, hcon, he]

/-! ### N4 -/

theorem exists_card_mul_degree_le {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ x : V, Fintype.card V * G.degree x ≤ 2 * G.edgeFinset.card := by
  obtain ⟨x, hx⟩ := G.exists_minimal_degree_vertex
  refine ⟨x, ?_⟩
  have h2 : ∑ _v : V, G.degree x ≤ ∑ v : V, G.degree v :=
    Finset.sum_le_sum (fun v _ => hx.symm.le.trans (G.minDegree_le_degree v))
  rw [G.sum_degrees_eq_twice_card_edges] at h2
  have h1 : ∑ _v : V, G.degree x = Fintype.card V * G.degree x := by
    first
      | (simp; done)
      | (rw [Finset.sum_const, Finset.card_univ, smul_eq_mul])
      | (rw [Finset.sum_const, Finset.card_univ]; rfl)
  rw [← h1]
  exact h2

/-! ### N5 -/

theorem exists_low_degree_vertex {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (N : ℕ) (hc : Fintype.card V = N) (hN : 4 ≤ N)
    (he : N ^ 2 / 4 + 1 ≤ G.edgeFinset.card) :
    ∃ x : V, G.degree x + (N - 1) ^ 2 / 4 + 1 ≤ G.edgeFinset.card := by
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨x, hx⟩ := exists_card_mul_degree_le G
  rw [hc] at hx
  exact ⟨x, low_degree_arith N _ _ hN he hx⟩

/-! ### N6 -/

theorem card_edgeFinset_induce_compl_singleton_eq {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    (G.induce ({x}ᶜ : Set V)).edgeFinset.card = G.edgeFinset.card - G.degree x := by
  rw [SimpleGraph.card_edgeFinset_induce_compl_singleton,
    SimpleGraph.card_edgeFinset_deleteIncidenceSet]

/-! ### N7 -/

theorem card_compl_singleton_subtype {V : Type} [Fintype V] [DecidableEq V] (x : V) :
    Fintype.card ({x}ᶜ : Set V) = Fintype.card V - 1 := by
  first
    | (rw [Fintype.card_compl_set, Set.card_singleton])
    | (rw [Fintype.card_compl_set]; simp)
    | simp

/-! ### N8 -/

theorem exists_vertex_delete_keeps_dense {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (N : ℕ) (hc : Fintype.card V = N) (hN : 4 ≤ N)
    (he : N ^ 2 / 4 + 1 ≤ G.edgeFinset.card) :
    ∃ x : V, (N - 1) ^ 2 / 4 + 1 ≤ (G.induce ({x}ᶜ : Set V)).edgeFinset.card := by
  obtain ⟨x, hx⟩ := exists_low_degree_vertex G N hc hN he
  refine ⟨x, ?_⟩
  rw [card_edgeFinset_induce_compl_singleton_eq]
  omega

/-! ### N9 -/

theorem induce_isContained {V : Type} (G : SimpleGraph V) (s : Set V) :
    G.induce s ⊑ G :=
  ⟨SimpleGraph.Copy.induce G s⟩

/-! ### N10 -/

theorem ncard_edgeSet_eq_card_edgeFinset {V : Type} (G : SimpleGraph V) [Fintype G.edgeSet] :
    G.edgeSet.ncard = G.edgeFinset.card := by
  first
    | exact Set.ncard_eq_toFinset_card' G.edgeSet
    | (rw [SimpleGraph.edgeFinset]; exact Set.ncard_eq_toFinset_card' G.edgeSet)
    | (rw [SimpleGraph.edgeFinset_card, Set.ncard_eq_toFinset_card', Set.toFinset_card])
    | simp [SimpleGraph.edgeFinset]

/-! ### N11 -/

theorem exists_fin_copy {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {k : ℕ} (hc : Fintype.card V = k) :
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = G.edgeFinset.card ∧ H ⊑ G := by
  have h1 : G.edgeSet.ncard = G.edgeFinset.card := ncard_edgeSet_eq_card_edgeFinset G
  have h2 : (G.overFin hc).edgeSet.ncard = G.edgeSet.ncard := by
    first
      | exact Nat.card_congr (G.overFinIso hc).mapEdgeSet.symm
      | (rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
         exact Nat.card_congr (G.overFinIso hc).mapEdgeSet.symm)
  exact ⟨G.overFin hc, h2.trans h1, (G.overFinIso hc).isContained'⟩

/-! ### N12 -/

theorem exists_dense_fin_subgraph (k : ℕ) (hk : 3 ≤ k) :
    ∀ (N : ℕ) (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V = N → k ≤ N → N ^ 2 / 4 + 1 ≤ G.edgeFinset.card →
      ∃ H : SimpleGraph (Fin k), k ^ 2 / 4 + 1 ≤ H.edgeSet.ncard ∧ H ⊑ G := by
  intro N
  induction N with
  | zero =>
    intro V _ _ G _ _ hkN
    exact absurd hkN (by omega)
  | succ N ih =>
    intro V _ _ G _ hc hkN he
    rcases Nat.lt_or_ge N k with hlt | hge
    · have hNk : N + 1 = k := by omega
      obtain ⟨H, hH, hHG⟩ := exists_fin_copy G (hc.trans hNk)
      refine ⟨H, ?_, hHG⟩
      rw [hH, ← hNk]
      exact he
    · obtain ⟨x, hx⟩ := exists_vertex_delete_keeps_dense G (N + 1) hc (by omega) he
      have hx' : N ^ 2 / 4 + 1 ≤ (G.induce ({x}ᶜ : Set V)).edgeFinset.card := by
        have e1 : N + 1 - 1 = N := by omega
        rw [e1] at hx
        exact hx
      have hc' : Fintype.card ({x}ᶜ : Set V) = N := by
        have h := card_compl_singleton_subtype (V := V) x
        omega
      obtain ⟨H, hH, hHG⟩ := ih _ (G.induce ({x}ᶜ : Set V)) hc' hge hx'
      exact ⟨H, hH, SimpleGraph.IsContained.trans hHG (induce_isContained G _)⟩

/-! ### N13 -/

theorem exists_le_ncard_edgeSet_eq {W : Type} [Finite W] (H : SimpleGraph W) (m : ℕ)
    (hm : m ≤ H.edgeSet.ncard) :
    ∃ H' : SimpleGraph W, H'.edgeSet.ncard = m ∧ H' ≤ H := by
  obtain ⟨t, hts, htm⟩ := Set.exists_subset_card_eq hm
  refine ⟨SimpleGraph.fromEdgeSet t, ?_, ?_⟩
  · have hdisj : Disjoint t Sym2.diagSet :=
      Set.disjoint_left.mpr fun e he => H.edgeSet_subset_compl_diagSet (hts he)
    rw [SimpleGraph.edgeSet_fromEdgeSet, hdisj.sdiff_eq_left]
    exact htm
  · have h := SimpleGraph.fromEdgeSet_mono hts
    rwa [SimpleGraph.fromEdgeSet_edgeSet] at h

/-! ### N14 -/

theorem dirac_erdos_exists (n k : ℕ) (hk : 3 ≤ k) (hkn : k ≤ n) (G : SimpleGraph (Fin n))
    (hG : G.edgeSet.ncard = n ^ 2 / 4 + 1) :
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = k ^ 2 / 4 + 1 ∧ H ⊑ G := by
  haveI : DecidableRel G.Adj := Classical.decRel _
  have he : n ^ 2 / 4 + 1 ≤ G.edgeFinset.card := by
    rw [← ncard_edgeSet_eq_card_edgeFinset G]
    first
      | exact hG.symm.le
      | omega
      | exact hG.ge
  obtain ⟨H, hH, hHG⟩ := exists_dense_fin_subgraph k hk n (Fin n) G (Fintype.card_fin n) hkn he
  obtain ⟨H', hH', hle⟩ := exists_le_ncard_edgeSet_eq H (k ^ 2 / 4 + 1) hH
  exact ⟨H', hH', SimpleGraph.IsContained.mono_left hle hHG⟩

/-! ### N15 -/

theorem forcingNumber_le_of_forall (n k l m : ℕ)
    (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
      ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) :
    forcingNumber n k l ≤ m := by
  unfold forcingNumber
  first
    | exact Nat.sInf_le h
    | exact csInf_le' h
    | (apply Nat.sInf_le; exact h)

end Erdos766

end
