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

/-! ## Floor arithmetic (N1–N3) -/

/-- N1 -/
theorem two_mul_sq_div_four_succ_lt (N : ℕ) (hN : 4 ≤ N) :
    2 * (N ^ 2 / 4 + 1) < N * (N / 2 + 1) := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' N
  · have e1 : (2 * k) ^ 2 = k ^ 2 * 4 := by ring
    have h1 : (2 * k) ^ 2 / 4 = k ^ 2 := by
      first
        | omega
        | (rw [e1]; exact Nat.mul_div_cancel _ (by norm_num))
    have h2 : 2 * k / 2 = k := by omega
    have hk : 2 ≤ k := by omega
    rw [h1, h2]
    first
      | nlinarith
      | (ring_nf; omega)
  · have e1 : (2 * k + 1) ^ 2 = 1 + (k ^ 2 + k) * 4 := by ring
    have h1 : (2 * k + 1) ^ 2 / 4 = k ^ 2 + k := by
      first
        | omega
        | (rw [e1, Nat.add_mul_div_right _ _ (by norm_num)]; norm_num)
    have h2 : (2 * k + 1) / 2 = k := by omega
    have hk : 2 ≤ k := by omega
    rw [h1, h2]
    first
      | nlinarith
      | (ring_nf; omega)

/-- N2 -/
theorem sq_div_four_eq_pred_sq_div_four_add_half (N : ℕ) (hN : 1 ≤ N) :
    N ^ 2 / 4 = (N - 1) ^ 2 / 4 + N / 2 := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' N
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have e1 : (2 * (j + 1)) ^ 2 = (j ^ 2 + 2 * j + 1) * 4 := by ring
    have e2 : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
    have e3 : (2 * j + 1) ^ 2 = 1 + (j ^ 2 + j) * 4 := by ring
    have h1 : (2 * (j + 1)) ^ 2 / 4 = j ^ 2 + 2 * j + 1 := by
      first
        | omega
        | (rw [e1]; exact Nat.mul_div_cancel _ (by norm_num))
    have h2 : (2 * (j + 1) - 1) ^ 2 / 4 = j ^ 2 + j := by
      rw [e2]
      first
        | omega
        | (rw [e3, Nat.add_mul_div_right _ _ (by norm_num)]; norm_num)
    have h3 : 2 * (j + 1) / 2 = j + 1 := by omega
    omega
  · have e1 : (2 * k + 1) ^ 2 = 1 + (k ^ 2 + k) * 4 := by ring
    have e2 : 2 * k + 1 - 1 = 2 * k := by omega
    have e3 : (2 * k) ^ 2 = k ^ 2 * 4 := by ring
    have h1 : (2 * k + 1) ^ 2 / 4 = k ^ 2 + k := by
      first
        | omega
        | (rw [e1, Nat.add_mul_div_right _ _ (by norm_num)]; norm_num)
    have h2 : (2 * k + 1 - 1) ^ 2 / 4 = k ^ 2 := by
      rw [e2]
      first
        | omega
        | (rw [e3]; exact Nat.mul_div_cancel _ (by norm_num))
    have h3 : (2 * k + 1) / 2 = k := by omega
    omega

/-- N3 -/
theorem low_degree_arith (N e d : ℕ) (hN : 4 ≤ N) (he : N ^ 2 / 4 + 1 ≤ e)
    (hd : N * d ≤ 2 * e) : d + (N - 1) ^ 2 / 4 + 1 ≤ e := by
  have h1 := two_mul_sq_div_four_succ_lt N hN
  have h2 := sq_div_four_eq_pred_sq_div_four_add_half N (by omega)
  by_contra hcon
  have hd' : N / 2 + 1 + (e - (N ^ 2 / 4 + 1)) ≤ d := by omega
  have h3 : N * (N / 2 + 1 + (e - (N ^ 2 / 4 + 1))) ≤ N * d := Nat.mul_le_mul le_rfl hd'
  have h4 : 2 * (e - (N ^ 2 / 4 + 1)) ≤ N * (e - (N ^ 2 / 4 + 1)) :=
    Nat.mul_le_mul (by omega) le_rfl
  have h5 : N * (N / 2 + 1 + (e - (N ^ 2 / 4 + 1))) =
      N * (N / 2 + 1) + N * (e - (N ^ 2 / 4 + 1)) := by ring
  omega

/-! ## Graph lemmas (N4–N11) -/

/-- N4 -/
theorem exists_card_mul_degree_le {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ x : V, Fintype.card V * G.degree x ≤ 2 * G.edgeFinset.card := by
  obtain ⟨x, hx⟩ := G.exists_minimal_degree_vertex
  refine ⟨x, ?_⟩
  first
    | (have h1 : Finset.univ.card • G.minDegree ≤ ∑ v, G.degree v :=
          Finset.card_nsmul_le_sum Finset.univ (fun v => G.degree v) G.minDegree
            (fun v _ => G.minDegree_le_degree v)
       rw [G.sum_degrees_eq_twice_card_edges, Finset.card_univ] at h1
       rw [← hx]
       first
         | exact h1
         | simpa [smul_eq_mul, nsmul_eq_mul] using h1
         | (rw [smul_eq_mul] at h1; exact h1)
         | (rw [nsmul_eq_mul, Nat.cast_id] at h1; exact h1))
    | (calc Fintype.card V * G.degree x = ∑ _v : V, G.degree x := by simp
        _ ≤ ∑ v, G.degree v := by
            apply Finset.sum_le_sum
            intro v _
            rw [← hx]
            exact G.minDegree_le_degree v
        _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges)

/-- N5 -/
theorem exists_low_degree_vertex {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (N : ℕ) (hc : Fintype.card V = N) (hN : 4 ≤ N)
    (he : N ^ 2 / 4 + 1 ≤ G.edgeFinset.card) :
    ∃ x : V, G.degree x + (N - 1) ^ 2 / 4 + 1 ≤ G.edgeFinset.card := by
  haveI hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨x, hx⟩ := exists_card_mul_degree_le G
  refine ⟨x, ?_⟩
  rw [hc] at hx
  exact low_degree_arith N G.edgeFinset.card (G.degree x) hN he hx

/-- N6 -/
theorem card_edgeFinset_induce_compl_singleton_eq {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    (G.induce ({x}ᶜ : Set V)).edgeFinset.card = G.edgeFinset.card - G.degree x := by
  first
    | rw [SimpleGraph.card_edgeFinset_induce_compl_singleton,
        SimpleGraph.card_edgeFinset_deleteIncidenceSet]
    | simp [SimpleGraph.card_edgeFinset_induce_compl_singleton,
        SimpleGraph.card_edgeFinset_deleteIncidenceSet]

/-- N7 -/
theorem card_compl_singleton_subtype {V : Type} [Fintype V] [DecidableEq V] (x : V) :
    Fintype.card ({x}ᶜ : Set V) = Fintype.card V - 1 := by
  first
    | rw [Fintype.card_compl_set, Set.card_singleton]
    | (rw [Fintype.card_compl_set]; simp)
    | (have h : Fintype.card ({x}ᶜ : Set V) = (Finset.univ.erase x).card :=
          Fintype.card_of_subtype (Finset.univ.erase x) (fun y => by simp)
       rw [h, Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ])
    | simp

/-- N8 -/
theorem exists_vertex_delete_keeps_dense {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (N : ℕ) (hc : Fintype.card V = N) (hN : 4 ≤ N)
    (he : N ^ 2 / 4 + 1 ≤ G.edgeFinset.card) :
    ∃ x : V, (N - 1) ^ 2 / 4 + 1 ≤ (G.induce ({x}ᶜ : Set V)).edgeFinset.card := by
  obtain ⟨x, hx⟩ := exists_low_degree_vertex G N hc hN he
  refine ⟨x, ?_⟩
  have h6 := card_edgeFinset_induce_compl_singleton_eq G x
  omega

/-- N9 -/
theorem induce_isContained {V : Type} (G : SimpleGraph V) (s : Set V) :
    G.induce s ⊑ G := by
  first
    | exact ⟨SimpleGraph.Copy.induce G s⟩
    | exact (SimpleGraph.Embedding.induce s).isContained
    | exact (SimpleGraph.Copy.induce G s).isContained

/-- N10 -/
theorem ncard_edgeSet_eq_card_edgeFinset {V : Type} (G : SimpleGraph V) [Fintype G.edgeSet] :
    G.edgeSet.ncard = G.edgeFinset.card := by
  first
    | exact Set.ncard_eq_toFinset_card' _
    | (rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset])
    | simp [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card']

/-- N11 -/
theorem exists_fin_copy {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {k : ℕ} (hc : Fintype.card V = k) :
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = G.edgeFinset.card ∧ H ⊑ G := by
  refine ⟨G.overFin hc, ?_, (G.overFinIso hc).isContained'⟩
  first
    | (rw [← ncard_edgeSet_eq_card_edgeFinset, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
       exact Nat.card_congr (G.overFinIso hc).mapEdgeSet.symm)
    | (classical
       rw [ncard_edgeSet_eq_card_edgeFinset]
       exact ((G.overFinIso hc).card_edgeFinset_eq).symm)

/-! ## The induction and the conclusion (N12–ROOT) -/

/-- N12 -/
theorem exists_dense_fin_subgraph (k : ℕ) (hk : 3 ≤ k) :
    ∀ (N : ℕ) (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V = N → k ≤ N → N ^ 2 / 4 + 1 ≤ G.edgeFinset.card →
      ∃ H : SimpleGraph (Fin k), k ^ 2 / 4 + 1 ≤ H.edgeSet.ncard ∧ H ⊑ G := by
  intro N
  induction N with
  | zero =>
    intro V _ _ G _ hc hkN he
    exfalso
    omega
  | succ N ih =>
    intro V _ _ G _ hc hkN he
    rcases Nat.lt_or_ge N k with hlt | hge
    · -- here k = N + 1: transfer G itself to Fin k
      have hkeq : Fintype.card V = k := by omega
      obtain ⟨H, hH1, hH2⟩ := exists_fin_copy G hkeq
      refine ⟨H, ?_, hH2⟩
      have hk' : k = N + 1 := by omega
      first
        | (subst hk'; rw [hH1]; exact he)
        | (rw [hH1, hk']; exact he)
    · -- here k ≤ N: delete a vertex of low degree and use the induction hypothesis
      have hN4 : 4 ≤ N + 1 := by omega
      obtain ⟨x, hx⟩ := exists_vertex_delete_keeps_dense G (N + 1) hc hN4 he
      have hcard : Fintype.card ({x}ᶜ : Set V) = N := by
        have h7 := card_compl_singleton_subtype x
        omega
      have hx' : N ^ 2 / 4 + 1 ≤ (G.induce ({x}ᶜ : Set V)).edgeFinset.card := by
        have e1 : N + 1 - 1 = N := by omega
        first
          | (rw [e1] at hx; exact hx)
          | simpa using hx
      obtain ⟨H, hH1, hH2⟩ := ih ({x}ᶜ : Set V) (G.induce ({x}ᶜ : Set V)) hcard hge hx'
      exact ⟨H, hH1, hH2.trans (induce_isContained G _)⟩

/-- N13 -/
theorem exists_le_ncard_edgeSet_eq {W : Type} [Finite W] (H : SimpleGraph W) (m : ℕ)
    (hm : m ≤ H.edgeSet.ncard) :
    ∃ H' : SimpleGraph W, H'.edgeSet.ncard = m ∧ H' ≤ H := by
  obtain ⟨t, hts, htm⟩ := Set.exists_subset_card_eq hm
  refine ⟨SimpleGraph.fromEdgeSet t, ?_, ?_⟩
  · have hdisj : t \ Sym2.diagSet = t := by
      first
        | exact sdiff_eq_left.mpr (Set.subset_compl_iff_disjoint_right.mp
            (hts.trans H.edgeSet_subset_compl_diagSet))
        | (ext e
           simp only [Set.mem_diff, and_iff_left_iff_imp]
           intro he
           exact H.edgeSet_subset_compl_diagSet (hts he))
    rw [SimpleGraph.edgeSet_fromEdgeSet, hdisj, htm]
  · have h := SimpleGraph.fromEdgeSet_mono hts
    rwa [SimpleGraph.fromEdgeSet_edgeSet] at h

/-- N14 -/
theorem dirac_erdos_exists (n k : ℕ) (hk : 3 ≤ k) (hkn : k ≤ n) (G : SimpleGraph (Fin n))
    (hG : G.edgeSet.ncard = n ^ 2 / 4 + 1) :
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = k ^ 2 / 4 + 1 ∧ H ⊑ G := by
  classical
  have he : n ^ 2 / 4 + 1 ≤ G.edgeFinset.card := by
    rw [← ncard_edgeSet_eq_card_edgeFinset]
    first
      | exact hG.ge
      | omega
  obtain ⟨H, hH1, hH2⟩ :=
    exists_dense_fin_subgraph k hk n (Fin n) G (Fintype.card_fin n) hkn he
  obtain ⟨H', hH'1, hH'2⟩ := exists_le_ncard_edgeSet_eq H (k ^ 2 / 4 + 1) hH1
  exact ⟨H', hH'1, SimpleGraph.IsContained.mono_left hH'2 hH2⟩

/-- N15 -/
theorem forcingNumber_le_of_forall (n k l m : ℕ)
    (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
      ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) :
    forcingNumber n k l ≤ m := by
  first
    | exact Nat.sInf_le h
    | (unfold forcingNumber; exact Nat.sInf_le h)
    | (apply Nat.sInf_le; exact h)
    | (apply Nat.sInf_le; simpa using h)

/--
Dirac and Erdős proved independently that when $l=\lfloor k^2/4\rfloor+1$
$$f(n;k,l)\leq \lfloor n^2/4\rfloor+1.$$

[Er64c, p. 34] states this for every $k \leq n$. We assume $k \geq 3$, since for $k \leq 2$ there
is no graph with $k$ vertices and $\lfloor k^2/4\rfloor+1$ edges.
-/
theorem erdos_766.variants.dirac_erdos (n k : ℕ) (hk : 3 ≤ k) (hkn : k ≤ n) :
    forcingNumber n k (k ^ 2 / 4 + 1) ≤ n ^ 2 / 4 + 1 := by
  apply forcingNumber_le_of_forall
  intro G hG
  exact dirac_erdos_exists n k hk hkn G hG

end Erdos766

end
