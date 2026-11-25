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

/-!
## Route

Downward induction on the number of vertices. A graph on `n + 1 ≥ 4` vertices with at least
`⌊(n+1)²/4⌋ + 1` edges has a vertex `v` with `(n+1) · deg v ≤ 2 · e` (handshake), and the
arithmetic lemma `step_arith` shows that deleting `v` leaves at least `⌊n²/4⌋ + 1` edges.
At the base `n = k` the whole graph is transported to `Fin k` and edges are trimmed to exactly
`⌊k²/4⌋ + 1`.
-/

open SimpleGraph Finset

/-- The arithmetic heart of the Dirac–Erdős step. -/
lemma step_arith (n d e : ℕ) (hn : 3 ≤ n) (h1 : (n + 1) * d ≤ 2 * e)
    (h2 : (n + 1) ^ 2 / 4 + 1 ≤ e) : n ^ 2 / 4 + 1 + d ≤ e := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · have hm : 2 ≤ m := by omega
    have e1 : (2 * m) ^ 2 / 4 = m ^ 2 := by
      rw [show (2 * m) ^ 2 = 4 * m ^ 2 by ring]; omega
    have e2 : (2 * m + 1) ^ 2 / 4 = m ^ 2 + m := by
      rw [show (2 * m + 1) ^ 2 = 4 * (m ^ 2 + m) + 1 by ring]; omega
    rw [e1]; rw [e2] at h2
    by_contra hc
    push_neg at hc
    have hd : m + 1 ≤ d := by omega
    nlinarith
  · have hm : 1 ≤ m := by omega
    have e1 : (2 * m + 1) ^ 2 / 4 = m ^ 2 + m := by
      rw [show (2 * m + 1) ^ 2 = 4 * (m ^ 2 + m) + 1 by ring]; omega
    have e2 : (2 * m + 1 + 1) ^ 2 / 4 = m ^ 2 + 2 * m + 1 := by
      rw [show (2 * m + 1 + 1) ^ 2 = 4 * (m ^ 2 + 2 * m + 1) by ring]; omega
    rw [e1]; rw [e2] at h2
    by_contra hc
    push_neg at hc
    have hd : m + 2 ≤ d := by omega
    nlinarith [Nat.mul_le_mul_left m hd]

/-- `ncard` of the edge set is the cardinality of `edgeFinset`. -/
lemma ncard_edgeSet_eq_card_edgeFinset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : G.edgeSet.ncard = #G.edgeFinset := by
  rw [← coe_edgeFinset, Set.ncard_coe_finset]

/-- Deleting a vertex deletes exactly its degree many edges. -/
lemma ncard_edgeSet_induce_compl_singleton {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (G.induce {v}ᶜ).edgeSet.ncard + G.degree v = G.edgeSet.ncard := by
  rw [ncard_edgeSet_eq_card_edgeFinset, ncard_edgeSet_eq_card_edgeFinset,
    card_edgeFinset_induce_compl_singleton, card_edgeFinset_deleteIncidenceSet]
  have h : G.degree v ≤ #G.edgeFinset := by
    rw [← card_incidenceFinset_eq_degree]
    exact card_le_card (incidenceFinset_subset _ _)
  omega

/-- Handshake: some vertex has degree at most the average degree. -/
lemma exists_card_mul_degree_le {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ v, Fintype.card V * G.degree v ≤ 2 * G.edgeSet.ncard := by
  obtain ⟨v, hv⟩ := G.exists_minimal_degree_vertex
  refine ⟨v, ?_⟩
  rw [ncard_edgeSet_eq_card_edgeFinset, ← G.sum_degrees_eq_twice_card_edges]
  calc Fintype.card V * G.degree v = ∑ _w : V, G.degree v := by simp
    _ ≤ ∑ w, G.degree w := Finset.sum_le_sum fun w _ => hv ▸ G.minDegree_le_degree w

/-- Trim a graph to exactly `l` edges. -/
lemma exists_le_ncard_edgeSet_eq {W : Type*} [Fintype W] (H : SimpleGraph W) {l : ℕ}
    (hl : l ≤ H.edgeSet.ncard) :
    ∃ H' : SimpleGraph W, H'.edgeSet.ncard = l ∧ H' ≤ H := by
  classical
  rw [ncard_edgeSet_eq_card_edgeFinset] at hl
  obtain ⟨t, ht, hcard⟩ := Finset.exists_subset_card_eq hl
  have ht' : (↑t : Set (Sym2 W)) ⊆ H.edgeSet := by
    intro e he
    exact mem_edgeFinset.mp (ht he)
  have hE : (fromEdgeSet (↑t : Set (Sym2 W))).edgeSet = ↑t := by
    rw [edgeSet_fromEdgeSet, sdiff_eq_left, Set.disjoint_left]
    intro e he hd
    exact H.not_isDiag_of_mem_edgeSet (ht' he) (Sym2.mem_diagSet.mp hd)
  refine ⟨fromEdgeSet ↑t, ?_, ?_⟩
  · rw [hE, Set.ncard_coe_finset, hcard]
  · calc fromEdgeSet (↑t : Set (Sym2 W)) ≤ fromEdgeSet H.edgeSet := fromEdgeSet_mono ht'
      _ = H := fromEdgeSet_edgeSet H

/-- Base case: a graph on `k` vertices with at least `l` edges contains a graph on `Fin k`
with exactly `l` edges. -/
lemma exists_copy_of_card_eq {V : Type} [Fintype V] (G : SimpleGraph V) {k l : ℕ}
    (hV : Fintype.card V = k) (hl : l ≤ G.edgeSet.ncard) :
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G := by
  classical
  let e : Fin k ≃ V := (Fintype.equivFinOfCardEq hV).symm
  have hiso : G.comap e ≃g G := Iso.comap e G
  have hcard : (G.comap e).edgeSet.ncard = G.edgeSet.ncard := by
    rw [ncard_edgeSet_eq_card_edgeFinset, ncard_edgeSet_eq_card_edgeFinset]
    exact hiso.card_edgeFinset_eq
  obtain ⟨H, hH, hle⟩ := exists_le_ncard_edgeSet_eq (G.comap e) (hcard ▸ hl)
  exact ⟨H, hH, (IsContained.of_le hle).trans hiso.isContained⟩

/-- The Dirac–Erdős theorem, in the form used for the induction: every graph on `n ≥ k`
vertices with at least `⌊n²/4⌋ + 1` edges contains a graph on `Fin k` with exactly
`⌊k²/4⌋ + 1` edges. -/
theorem main_induction (k : ℕ) (hk : 3 ≤ k) :
    ∀ n, k ≤ n → ∀ (V : Type) [Fintype V] (G : SimpleGraph V), Fintype.card V = n →
      n ^ 2 / 4 + 1 ≤ G.edgeSet.ncard →
      ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = k ^ 2 / 4 + 1 ∧ H ⊑ G := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    intro V _ G hV hG
    exact exists_copy_of_card_eq G hV hG
  | succ n hkn ih =>
    intro V _ G hV hG
    classical
    have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨v, hv⟩ := exists_card_mul_degree_le G
    have h1 := ncard_edgeSet_induce_compl_singleton G v
    have hcardW : Fintype.card ({v}ᶜ : Set V) = n := by
      rw [Fintype.card_compl_set, hV, Set.card_singleton]
      omega
    rw [hV] at hv
    have harith := step_arith n (G.degree v) G.edgeSet.ncard (by omega) hv hG
    obtain ⟨H, hH, hHG⟩ := ih ({v}ᶜ : Set V) (G.induce {v}ᶜ) hcardW (by omega)
    exact ⟨H, hH, hHG.trans (Copy.induce G {v}ᶜ).isContained⟩

/--
Dirac and Erdős proved independently that when $l=\lfloor k^2/4\rfloor+1$
$$f(n;k,l)\leq \lfloor n^2/4\rfloor+1.$$

[Er64c, p. 34] states this for every $k \leq n$. We assume $k \geq 3$, since for $k \leq 2$ there
is no graph with $k$ vertices and $\lfloor k^2/4\rfloor+1$ edges.
-/
theorem erdos_766.variants.dirac_erdos (n k : ℕ) (hk : 3 ≤ k) (hkn : k ≤ n) :
    forcingNumber n k (k ^ 2 / 4 + 1) ≤ n ^ 2 / 4 + 1 := by
  apply Nat.sInf_le
  intro G hG
  exact main_induction k hk n hkn (Fin n) G (Fintype.card_fin n) hG.ge

end Erdos766

end
