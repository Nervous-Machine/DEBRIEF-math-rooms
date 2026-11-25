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

/-! ### Lemmas (blueprint nodes N1–N15) -/

-- N1
theorem two_mul_sq_div_four_succ_lt (N : ℕ) (hN : 4 ≤ N) :
    2 * (N ^ 2 / 4 + 1) < N * (N / 2 + 1) := by
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' N
  · subst hk
    have h2 : 2 * k / 2 = k := Nat.mul_div_cancel_left k (by norm_num)
    have h1 : (2 * k) ^ 2 / 4 = k ^ 2 := by
      have : (2 * k) ^ 2 = 4 * k ^ 2 := by ring
      omega
    rw [h1, h2]
    nlinarith
  · subst hk
    have h2 : (2 * k + 1) / 2 = k := by omega
    have h1 : (2 * k + 1) ^ 2 / 4 = k ^ 2 + k := by
      have : (2 * k + 1) ^ 2 = 4 * (k ^ 2 + k) + 1 := by ring
      omega
    rw [h1, h2]
    nlinarith

-- N2
theorem sq_div_four_eq_pred_sq_div_four_add_half (N : ℕ) (hN : 1 ≤ N) :
    N ^ 2 / 4 = (N - 1) ^ 2 / 4 + N / 2 := by
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' N
  · subst hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have e1 : (2 * (j + 1)) ^ 2 = 4 * (j ^ 2 + 2 * j + 1) := by ring
    have e2 : (2 * (j + 1) - 1) ^ 2 = 4 * (j ^ 2 + j) + 1 := by
      rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega]; ring
    omega
  · subst hk
    have e1 : (2 * k + 1) ^ 2 = 4 * (k ^ 2 + k) + 1 := by ring
    have e2 : (2 * k + 1 - 1) ^ 2 = 4 * k ^ 2 := by
      rw [show 2 * k + 1 - 1 = 2 * k by omega]; ring
    omega

-- helper for N3: the arithmetic with the floors abstracted away
theorem low_degree_arith_aux (N e d q p h : ℕ) (hN : 4 ≤ N) (h1 : 2 * (q + 1) < N * (h + 1))
    (h2 : q = p + h) (he : q + 1 ≤ e) (hd : N * d ≤ 2 * e) : d + p + 1 ≤ e := by
  by_contra hneg
  have hneg' : e ≤ d + p := by omega
  have hA : N * e ≤ N * (d + p) := Nat.mul_le_mul_left N hneg'
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 2 := ⟨N - 2, by omega⟩
  have hB : M * (q + 1) ≤ M * e := Nat.mul_le_mul_left M he
  nlinarith

-- N3
theorem low_degree_arith (N e d : ℕ) (hN : 4 ≤ N) (he : N ^ 2 / 4 + 1 ≤ e)
    (hd : N * d ≤ 2 * e) : d + (N - 1) ^ 2 / 4 + 1 ≤ e :=
  low_degree_arith_aux N e d (N ^ 2 / 4) ((N - 1) ^ 2 / 4) (N / 2) hN
    (two_mul_sq_div_four_succ_lt N hN)
    (sq_div_four_eq_pred_sq_div_four_add_half N (by omega)) he hd

-- N4
theorem exists_card_mul_degree_le {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ x : V, Fintype.card V * G.degree x ≤ 2 * G.edgeFinset.card := by
  obtain ⟨x, hx⟩ := G.exists_minimal_degree_vertex
  refine ⟨x, ?_⟩
  rw [← G.sum_degrees_eq_twice_card_edges, ← hx, ← Finset.card_univ, ← smul_eq_mul]
  exact Finset.card_nsmul_le_sum _ _ _ (fun v _ => G.minDegree_le_degree v)

-- N5
theorem exists_low_degree_vertex {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (N : ℕ) (hc : Fintype.card V = N) (hN : 4 ≤ N)
    (he : N ^ 2 / 4 + 1 ≤ G.edgeFinset.card) :
    ∃ x : V, G.degree x + (N - 1) ^ 2 / 4 + 1 ≤ G.edgeFinset.card := by
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨x, hx⟩ := exists_card_mul_degree_le G
  exact ⟨x, low_degree_arith N _ _ hN he (by rw [← hc]; exact hx)⟩

-- N6
theorem card_edgeFinset_induce_compl_singleton_eq {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    (G.induce ({x}ᶜ : Set V)).edgeFinset.card = G.edgeFinset.card - G.degree x := by
  rw [SimpleGraph.card_edgeFinset_induce_compl_singleton,
    SimpleGraph.card_edgeFinset_deleteIncidenceSet]

-- N7
theorem card_compl_singleton_subtype {V : Type} [Fintype V] [DecidableEq V] (x : V) :
    Fintype.card ({x}ᶜ : Set V) = Fintype.card V - 1 := by
  rw [Fintype.card_compl_set]
  simp

-- N8
theorem exists_vertex_delete_keeps_dense {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (N : ℕ) (hc : Fintype.card V = N) (hN : 4 ≤ N)
    (he : N ^ 2 / 4 + 1 ≤ G.edgeFinset.card) :
    ∃ x : V, (N - 1) ^ 2 / 4 + 1 ≤ (G.induce ({x}ᶜ : Set V)).edgeFinset.card := by
  obtain ⟨x, hx⟩ := exists_low_degree_vertex G N hc hN he
  refine ⟨x, ?_⟩
  rw [card_edgeFinset_induce_compl_singleton_eq]
  omega

-- N9
theorem induce_isContained {V : Type} (G : SimpleGraph V) (s : Set V) :
    G.induce s ⊑ G :=
  ⟨SimpleGraph.Copy.induce G s⟩

-- N10
theorem ncard_edgeSet_eq_card_edgeFinset {V : Type} (G : SimpleGraph V) [Fintype G.edgeSet] :
    G.edgeSet.ncard = G.edgeFinset.card :=
  Set.ncard_eq_toFinset_card' _

-- N11
theorem exists_fin_copy {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {k : ℕ} (hc : Fintype.card V = k) :
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = G.edgeFinset.card ∧ H ⊑ G := by
  classical
  refine ⟨G.overFin hc, ?_, (G.overFinIso hc).isContained'⟩
  rw [ncard_edgeSet_eq_card_edgeFinset]
  exact (G.overFinIso hc).card_edgeFinset_eq.symm

-- N12
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
  | succ n ih =>
    intro V _ _ G _ hc hkN he
    rcases Nat.lt_or_ge k (n + 1) with hlt | hge
    · have hN : 4 ≤ n + 1 := by omega
      obtain ⟨x, hx⟩ := exists_vertex_delete_keeps_dense G (n + 1) hc hN he
      have hc' : Fintype.card ({x}ᶜ : Set V) = n := by
        have := card_compl_singleton_subtype x
        omega
      obtain ⟨H, hH, hHG⟩ :=
        ih ({x}ᶜ : Set V) (G.induce ({x}ᶜ : Set V)) hc' (by omega) hx
      exact ⟨H, hH, hHG.trans (induce_isContained G _)⟩
    · have hkeq : k = n + 1 := by omega
      subst hkeq
      obtain ⟨H, hH, hHG⟩ := exists_fin_copy G hc
      exact ⟨H, by rw [hH]; exact he, hHG⟩

-- N13
theorem exists_le_ncard_edgeSet_eq {W : Type} [Finite W] (H : SimpleGraph W) (m : ℕ)
    (hm : m ≤ H.edgeSet.ncard) :
    ∃ H' : SimpleGraph W, H'.edgeSet.ncard = m ∧ H' ≤ H := by
  obtain ⟨t, hts, htm⟩ := Set.exists_subset_card_eq hm
  refine ⟨SimpleGraph.fromEdgeSet t, ?_, ?_⟩
  · have hdisj : Disjoint t Sym2.diagSet :=
      Set.disjoint_left.mpr fun e het hed => H.edgeSet_subset_compl_diagSet (hts het) hed
    rw [SimpleGraph.edgeSet_fromEdgeSet, sdiff_eq_left.mpr hdisj, htm]
  · calc SimpleGraph.fromEdgeSet t ≤ SimpleGraph.fromEdgeSet H.edgeSet :=
          SimpleGraph.fromEdgeSet_mono hts
      _ = H := SimpleGraph.fromEdgeSet_edgeSet H

-- N14
theorem dirac_erdos_exists (n k : ℕ) (hk : 3 ≤ k) (hkn : k ≤ n) (G : SimpleGraph (Fin n))
    (hG : G.edgeSet.ncard = n ^ 2 / 4 + 1) :
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = k ^ 2 / 4 + 1 ∧ H ⊑ G := by
  classical
  have he : n ^ 2 / 4 + 1 ≤ G.edgeFinset.card := by
    have := ncard_edgeSet_eq_card_edgeFinset G
    omega
  obtain ⟨H₀, hH₀, hH₀G⟩ :=
    exists_dense_fin_subgraph k hk n (Fin n) G (Fintype.card_fin n) hkn he
  obtain ⟨H, hH, hle⟩ := exists_le_ncard_edgeSet_eq H₀ (k ^ 2 / 4 + 1) hH₀
  exact ⟨H, hH, hH₀G.mono_left hle⟩

-- N15
theorem forcingNumber_le_of_forall (n k l m : ℕ)
    (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
      ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) :
    forcingNumber n k l ≤ m :=
  Nat.sInf_le h

/--
Dirac and Erdős proved independently that when $l=\lfloor k^2/4\rfloor+1$
$$f(n;k,l)\leq \lfloor n^2/4\rfloor+1.$$

[Er64c, p. 34] states this for every $k \leq n$. We assume $k \geq 3$, since for $k \leq 2$ there
is no graph with $k$ vertices and $\lfloor k^2/4\rfloor+1$ edges.
-/
theorem erdos_766.variants.dirac_erdos (n k : ℕ) (hk : 3 ≤ k) (hkn : k ≤ n) :
    forcingNumber n k (k ^ 2 / 4 + 1) ≤ n ^ 2 / 4 + 1 := by
  exact forcingNumber_le_of_forall n k _ _ (fun G hG => dirac_erdos_exists n k hk hkn G hG)

end Erdos766

end
