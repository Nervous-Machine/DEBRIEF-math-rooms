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

end Erdos766

end
