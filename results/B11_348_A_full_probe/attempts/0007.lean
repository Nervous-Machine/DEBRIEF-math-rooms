/-
Erdős Problem 348: the statement copied verbatim from google-deepmind/formal-conjectures,
FormalConjectures/ErdosProblems/348.lean at commit f606af16 (Apache-2.0; Copyright 2026 The Formal Conjectures Authors),
with the FormalConjecturesUtil import replaced by Mathlib and the two definitions it uses, `subseqSums'` and
`IsAddCompleteNatSeq'`, copied verbatim with the section variables they sit under (`[AddCommMonoid M]`, `[Preorder M]`) from FormalConjecturesForMathlib/NumberTheory/AdditivelyComplete.lean at the
same commit (Apache-2.0; Copyright 2025 The Formal Conjectures Authors). The answer is Geneson's Theorem 1
(arXiv:2609.25107): the pairs are exactly those with m ≤ 1. The searcher may not alter the definitions or the statement.
References: erdosproblems.com/348.
-/
module

public import Mathlib

@[expose] public section

variable {M : Type*} [AddCommMonoid M]

/-- The set of subset sums of a sequence `ℕ → M`, where repetition is allowed. -/
def subseqSums' (A : ℕ → M) : Set M :=
  {n | ∃ B : Finset ℕ, n = ∑ i ∈ B, A i}

variable [Preorder M]

/-- A sequence `A` is complete if every sufficiently large element of `M` is a sum of
(not necessarily distinct) terms of `A`. -/
def IsAddCompleteNatSeq' (A : ℕ → M) : Prop :=
  ∀ᶠ k in Filter.atTop, k ∈ subseqSums' A

namespace Erdos348

open Erdos348

def erdos_348.answer : Set (ℕ × ℕ) := {(m, n) : ℕ × ℕ | m < n ∧ m ≤ 1}

/-! ## Helper lemmas (searcher) -/

theorem mem_subseqSums'_iff (A : ℕ → ℕ) (x : ℕ) :
    x ∈ subseqSums' A ↔ ∃ B : Finset ℕ, x = ∑ i ∈ B, A i := Iff.rfl

theorem sum_updateFinset_zero (a : ℕ → ℕ) (s B : Finset ℕ) :
    ∑ i ∈ B, Function.updateFinset a s 0 i = ∑ i ∈ B.filter (· ∉ s), a i := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i ∈ s <;> simp [Function.updateFinset, hi]

/-! ## Blueprint rooms -/

-- N01
theorem mem_subseqSums'_updateFinset (a : ℕ → ℕ) (s : Finset ℕ) (x : ℕ) :
    x ∈ subseqSums' (Function.updateFinset a s 0) ↔
      ∃ B : Finset ℕ, Disjoint B s ∧ x = ∑ i ∈ B, a i := by
  rw [mem_subseqSums'_iff]
  constructor
  · rintro ⟨B, rfl⟩
    refine ⟨B.filter (· ∉ s), ?_, sum_updateFinset_zero a s B⟩
    rw [Finset.disjoint_left]
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  · rintro ⟨B, hB, rfl⟩
    refine ⟨B, ?_⟩
    rw [sum_updateFinset_zero, Finset.filter_true_of_mem]
    intro i hi
    exact Finset.disjoint_left.mp hB hi

-- N02
theorem subseqSums'_updateFinset_anti (a : ℕ → ℕ) {s t : Finset ℕ} (hst : s ⊆ t) :
    subseqSums' (Function.updateFinset a t 0) ⊆ subseqSums' (Function.updateFinset a s 0) := by
  intro x hx
  rw [mem_subseqSums'_updateFinset] at hx ⊢
  obtain ⟨B, hB, rfl⟩ := hx
  exact ⟨B, Finset.disjoint_of_subset_right hst hB, rfl⟩

-- N03
theorem complete_updateFinset_anti (a : ℕ → ℕ) {s t : Finset ℕ} (hst : s ⊆ t)
    (ht : IsAddCompleteNatSeq' (Function.updateFinset a t 0)) :
    IsAddCompleteNatSeq' (Function.updateFinset a s 0) := by
  unfold IsAddCompleteNatSeq' at *
  exact ht.mono fun x hx => subseqSums'_updateFinset_anti a hst hx

-- N04
theorem complete_iff_threshold (c : ℕ → ℕ) :
    IsAddCompleteNatSeq' c ↔ ∃ T, 1 ≤ T ∧ ∀ x, T ≤ x → x ∈ subseqSums' c := by
  unfold IsAddCompleteNatSeq'
  rw [Filter.eventually_atTop]
  constructor
  · rintro ⟨T, hT⟩
    exact ⟨T + 1, by omega, fun x hx => hT x (by omega)⟩
  · rintro ⟨T, -, hT⟩
    exact ⟨T, hT⟩

-- N05
theorem updateFinset_insert_of_eq_zero (a : ℕ → ℕ) (D : Finset ℕ) (i : ℕ) (hi : a i = 0) :
    Function.updateFinset a (insert i D) 0 = Function.updateFinset a D 0 := by
  funext k
  by_cases hk : k = i
  · subst hk
    by_cases hD : k ∈ D <;> simp [Function.updateFinset, hD, hi]
  · simp [Function.updateFinset, hk]

-- N06
theorem restore_deleted (a : ℕ → ℕ) (D E : Finset ℕ) (x : ℕ)
    (hx : x ∈ subseqSums' (Function.updateFinset a E 0)) :
    ∃ d ≤ ∑ i ∈ D, a i, ∃ y ∈ subseqSums' (Function.updateFinset a (D ∪ E) 0), x = d + y := by
  rw [mem_subseqSums'_updateFinset] at hx
  obtain ⟨B, hB, rfl⟩ := hx
  refine ⟨∑ i ∈ B.filter (· ∈ D), a i, ?_, ∑ i ∈ B.filter (· ∉ D), a i, ?_, ?_⟩
  · apply Finset.sum_le_sum_of_subset
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  · rw [mem_subseqSums'_updateFinset]
    refine ⟨_, ?_, rfl⟩
    rw [Finset.disjoint_union_right]
    constructor
    · rw [Finset.disjoint_left]
      intro i hi
      exact (Finset.mem_filter.mp hi).2
    · exact Finset.disjoint_of_subset_left (Finset.filter_subset _ _) hB
  · rw [Finset.sum_filter_add_sum_filter_not]

-- N07
theorem not_complete_of_long_gaps (R : Set ℕ) (C : ℕ)
    (hgap : ∀ M, ∃ u, M ≤ u ∧ ∀ x, u ≤ x → x ≤ u + C → x ∉ R) :
    ¬ ∀ᶠ x in Filter.atTop, ∃ d ≤ C, ∃ y ∈ R, x = d + y := by
  intro h
  rw [Filter.eventually_atTop] at h
  obtain ⟨M, hM⟩ := h
  obtain ⟨u, hu, hgap'⟩ := hgap M
  obtain ⟨d, hd, y, hy, hxy⟩ := hM (u + C) (by omega)
  exact hgap' y (by omega) (by omega) hy

-- N08
theorem monotone_bddAbove_eventually_const (b : ℕ → ℕ) (hb : Monotone b)
    (hbdd : BddAbove (Set.range b)) :
    ∃ N c, ∀ k, N ≤ k → b k = c := by
  obtain ⟨N, hN⟩ := Nat.sSup_mem (Set.range_nonempty b) hbdd
  refine ⟨N, b N, fun k hk => le_antisymm ?_ (hb hk)⟩
  rw [hN]
  exact le_csSup hbdd ⟨k, rfl⟩

-- N09
theorem pow_two_mem_subseqSums' (x : ℕ) : x ∈ subseqSums' (fun i : ℕ => 2 ^ i) := by
  rw [mem_subseqSums'_iff]
  refine ⟨x.bitIndices.toFinset, ?_⟩
  rw [List.sum_toFinset _ Nat.bitIndices_nodup, Nat.sum_map_two_pow_bitIndices]

theorem geom_two_sum (j : ℕ) : ∑ i ∈ Finset.range j, 2 ^ i + 1 = 2 ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [Finset.sum_range_succ, pow_succ]; omega

-- N10
theorem pow_two_delete_missing (j x : ℕ) (hx : x % 2 ^ (j + 1) = 2 ^ j) :
    x ∉ subseqSums' (Function.updateFinset (fun i : ℕ => 2 ^ i) {j} 0) := by
  rw [mem_subseqSums'_updateFinset]
  rintro ⟨B, hB, rfl⟩
  have hjB : j ∉ B := fun h => Finset.disjoint_left.mp hB h (Finset.mem_singleton_self j)
  rw [← Finset.sum_filter_add_sum_filter_not B (· < j)] at hx
  have hlow : ∑ i ∈ B.filter (· < j), 2 ^ i < 2 ^ j := by
    have h1 : ∑ i ∈ B.filter (· < j), 2 ^ i ≤ ∑ i ∈ Finset.range j, 2 ^ i := by
      apply Finset.sum_le_sum_of_subset
      intro i hi
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
    have h2 := geom_two_sum j
    omega
  have hhigh : 2 ^ (j + 1) ∣ ∑ i ∈ B.filter (fun i => ¬ i < j), 2 ^ i := by
    apply Finset.dvd_sum
    intro i hi
    obtain ⟨hiB, hij⟩ := Finset.mem_filter.mp hi
    have hne : i ≠ j := fun h => hjB (h ▸ hiB)
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨c, hc⟩ := hhigh
  rw [hc, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by rw [pow_succ]; omega)] at hx
  omega

-- N11
theorem pow_two_delete_incomplete (t : Finset ℕ) (ht : t.Nonempty) :
    ¬ IsAddCompleteNatSeq' (Function.updateFinset (fun i : ℕ => 2 ^ i) t 0) := by
  obtain ⟨j, hj⟩ := ht
  intro hc
  have h1 := complete_updateFinset_anti _ (Finset.singleton_subset_iff.mpr hj) hc
  unfold IsAddCompleteNatSeq' at h1
  rw [Filter.eventually_atTop] at h1
  obtain ⟨M, hM⟩ := h1
  have hpos : 1 ≤ 2 ^ (j + 1) := Nat.one_le_two_pow
  have hlt : 2 ^ j < 2 ^ (j + 1) := by rw [pow_succ]; have := Nat.one_le_two_pow (n := j); omega
  apply pow_two_delete_missing j (2 ^ j + 2 ^ (j + 1) * M)
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  · apply hM
    have := Nat.le_mul_of_pos_left M hpos
    omega

-- N12
theorem fib_prefix_sum (k : ℕ) :
    ∑ i ∈ Finset.range k, Nat.fib (i + 1) + 1 = Nat.fib (k + 2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have h : Nat.fib (k + 3) = Nat.fib (k + 1) + Nat.fib (k + 2) := Nat.fib_add_two
    have e : Nat.fib (k + 1 + 2) = Nat.fib (k + 3) := rfl
    rw [e]
    omega

-- N13
theorem interval_criterion (c : ℕ → ℕ)
    (hc : ∀ k, c k ≤ ∑ i ∈ Finset.range k, c i + 1) :
    ∀ k x, x ≤ ∑ i ∈ Finset.range k, c i → ∃ B ⊆ Finset.range k, ∑ i ∈ B, c i = x := by
  intro k
  induction k with
  | zero =>
    intro x hx
    simp only [Finset.range_zero, Finset.sum_empty, Nat.le_zero] at hx
    exact ⟨∅, Finset.empty_subset _, by simp [hx]⟩
  | succ k ih =>
    intro x hx
    rw [Finset.sum_range_succ] at hx
    by_cases h : x ≤ ∑ i ∈ Finset.range k, c i
    · obtain ⟨B, hB, hs⟩ := ih x h
      exact ⟨B, hB.trans (Finset.range_subset_range.mpr (Nat.le_succ k)), hs⟩
    · have hck := hc k
      obtain ⟨B, hB, hs⟩ := ih (x - c k) (by omega)
      have hk : k ∉ B := fun h => by have := Finset.mem_range.mp (hB h); omega
      refine ⟨insert k B, ?_, ?_⟩
      · intro i hi
        rw [Finset.mem_insert] at hi
        rcases hi with rfl | hi
        · exact Finset.mem_range.mpr (Nat.lt_succ_self _)
        · exact Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp (hB hi)))
      · rw [Finset.sum_insert hk, hs]
        omega

theorem succ_le_fib_add_two (k : ℕ) : k + 1 ≤ Nat.fib (k + 2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h : Nat.fib (k + 3) = Nat.fib (k + 1) + Nat.fib (k + 2) := Nat.fib_add_two
    have hp : 0 < Nat.fib (k + 1) := Nat.fib_pos.mpr (by omega)
    have e : Nat.fib (k + 1 + 2) = Nat.fib (k + 3) := rfl
    rw [e]
    omega

theorem fib_upd_sum (j k : ℕ) :
    ∑ i ∈ Finset.range k, Function.updateFinset (fun i : ℕ => Nat.fib (i + 1)) {j} 0 i
      + (if j < k then Nat.fib (j + 1) else 0) + 1 = Nat.fib (k + 2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have h : Nat.fib (k + 3) = Nat.fib (k + 1) + Nat.fib (k + 2) := Nat.fib_add_two
    have e : Nat.fib (k + 1 + 2) = Nat.fib (k + 3) := rfl
    have hc : Function.updateFinset (fun i : ℕ => Nat.fib (i + 1)) {j} 0 k
        = if k = j then 0 else Nat.fib (k + 1) := by
      by_cases hk : k = j <;> simp [Function.updateFinset, hk]
    rw [hc, e]
    rcases lt_trichotomy j k with hjk | hjk | hjk
    · rw [if_pos hjk] at ih
      rw [if_neg (by omega), if_pos (by omega)]
      omega
    · subst hjk
      rw [if_neg (lt_irrefl _)] at ih
      rw [if_pos rfl, if_pos (by omega)]
      omega
    · rw [if_neg (by omega)] at ih
      rw [if_neg (by omega), if_neg (by omega)]
      omega

-- N14
theorem fib_delete_one_complete (j : ℕ) :
    IsAddCompleteNatSeq' (Function.updateFinset (fun i : ℕ => Nat.fib (i + 1)) {j} 0) := by
  set c := Function.updateFinset (fun i : ℕ => Nat.fib (i + 1)) {j} 0 with hcdef
  have hval : ∀ k, c k = if k = j then 0 else Nat.fib (k + 1) := by
    intro k
    by_cases hk : k = j <;> simp [hcdef, Function.updateFinset, hk]
  have hsum : ∀ k, ∑ i ∈ Finset.range k, c i + (if j < k then Nat.fib (j + 1) else 0) + 1
      = Nat.fib (k + 2) := fun k => fib_upd_sum j k
  have hc : ∀ k, c k ≤ ∑ i ∈ Finset.range k, c i + 1 := by
    intro k
    have h1 := hsum k
    rw [hval k]
    have h2 : Nat.fib (k + 2) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two
    split_ifs with hk
    · omega
    · split_ifs at h1 with hjk
      · have := Nat.fib_mono (show j + 1 ≤ k by omega)
        omega
      · omega
  unfold IsAddCompleteNatSeq'
  refine Filter.Eventually.of_forall fun x => ?_
  have hge : ∀ k, k ≤ ∑ i ∈ Finset.range k, c i + Nat.fib (j + 1) := by
    intro k
    have h1 := hsum k
    have h3 := succ_le_fib_add_two k
    split_ifs at h1 <;> omega
  obtain ⟨B, -, hB⟩ := interval_criterion c hc (x + Nat.fib (j + 1)) x
    (by have := hge (x + Nat.fib (j + 1)); omega)
  exact ⟨B, hB.symm⟩

-- N15
theorem fib_delete_two_missing (i j : ℕ) (hij : i < j) (t d : ℕ) (hd1 : 1 ≤ d)
    (hd : d ≤ Nat.fib (i + 1)) :
    Nat.fib (j + 2 * t + 2) - d ∉
      subseqSums' (Function.updateFinset (fun r : ℕ => Nat.fib (r + 1)) {i, j} 0) := by
  rw [mem_subseqSums'_updateFinset]
  have hfi : Nat.fib (i + 1) ≤ Nat.fib (j + 1) := Nat.fib_mono (by omega)
  have hfj : 0 < Nat.fib (j + 1) := Nat.fib_pos.mpr (by omega)
  have hsingle : ∀ (B : Finset ℕ) r, r ∈ B → Nat.fib (r + 1) ≤ ∑ k ∈ B, Nat.fib (k + 1) :=
    fun B r hr => Finset.single_le_sum (f := fun k => Nat.fib (k + 1))
      (fun _ _ => Nat.zero_le _) hr
  have hZ : ∀ (B : Finset ℕ) (p : ℕ), Disjoint B {i, j} → B ⊆ Finset.range p → j < p →
      ∑ k ∈ B, Nat.fib (k + 1) + Nat.fib (i + 1) + Nat.fib (j + 1) + 1 ≤ Nat.fib (p + 2) := by
    intro B p hB hBp hjp
    have h1 := fib_prefix_sum p
    have h2 : ∑ k ∈ B, Nat.fib (k + 1) + ∑ k ∈ ({i, j} : Finset ℕ), Nat.fib (k + 1)
        ≤ ∑ k ∈ Finset.range p, Nat.fib (k + 1) := by
      rw [← Finset.sum_union hB]
      apply Finset.sum_le_sum_of_subset
      apply Finset.union_subset hBp
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rw [Finset.mem_range]
      omega
    rw [Finset.sum_pair (by omega)] at h2
    omega
  induction t with
  | zero =>
    rintro ⟨B, hB, hsum⟩
    have hsum' : Nat.fib (j + 2) - d = ∑ k ∈ B, Nat.fib (k + 1) := hsum
    have hBr : B ⊆ Finset.range (j + 1) := by
      intro r hr
      rw [Finset.mem_range]
      by_contra hcon
      have h1 := hsingle B r hr
      have h2 := Nat.fib_mono (show j + 2 ≤ r + 1 by omega)
      have h3 : 0 < Nat.fib (j + 2) := Nat.fib_pos.mpr (by omega)
      omega
    have h4 : ∑ k ∈ B, Nat.fib (k + 1) + Nat.fib (i + 1) + Nat.fib (j + 1) + 1
        ≤ Nat.fib (j + 3) := hZ B (j + 1) hB hBr (by omega)
    have h3 : Nat.fib (j + 3) = Nat.fib (j + 1) + Nat.fib (j + 2) := Nat.fib_add_two
    omega
  | succ t ih =>
    rintro ⟨B, hB, hsum⟩
    have hsum' : Nat.fib (j + 2 * t + 4) - d = ∑ k ∈ B, Nat.fib (k + 1) := by
      rw [show j + 2 * t + 4 = j + 2 * (t + 1) + 2 by ring]
      exact hsum
    have hBle : ∀ r ∈ B, r ≤ j + 2 * t + 2 := by
      intro r hr
      by_contra hcon
      have h1 := hsingle B r hr
      have h2 := Nat.fib_mono (show j + 2 * t + 4 ≤ r + 1 by omega)
      have h3 : 0 < Nat.fib (j + 2 * t + 4) := Nat.fib_pos.mpr (by omega)
      omega
    have hq : j + 2 * t + 2 ∈ B := by
      by_contra hq
      have hBr : B ⊆ Finset.range (j + 2 * t + 2) := by
        intro r hr
        rw [Finset.mem_range]
        have := hBle r hr
        have : r ≠ j + 2 * t + 2 := fun h => hq (h ▸ hr)
        omega
      have h4 : ∑ k ∈ B, Nat.fib (k + 1) + Nat.fib (i + 1) + Nat.fib (j + 1) + 1
          ≤ Nat.fib (j + 2 * t + 4) := hZ B (j + 2 * t + 2) hB hBr (by omega)
      omega
    apply ih
    refine ⟨B.erase (j + 2 * t + 2),
      Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hB, ?_⟩
    show Nat.fib (j + 2 * t + 2) - d = ∑ k ∈ B.erase (j + 2 * t + 2), Nat.fib (k + 1)
    have h5 := Finset.sum_erase_add B (fun k => Nat.fib (k + 1)) hq
    have h6 : Nat.fib (j + 2 * t + 4) = Nat.fib (j + 2 * t + 2) + Nat.fib (j + 2 * t + 3) :=
      Nat.fib_add_two
    have h7 : Nat.fib (j + 2 * t + 2 + 1) = Nat.fib (j + 2 * t + 3) := rfl
    simp only [h7] at h5
    omega

-- N16
theorem fib_delete_incomplete (t : Finset ℕ) (ht : 2 ≤ t.card) :
    ¬ IsAddCompleteNatSeq' (Function.updateFinset (fun r : ℕ => Nat.fib (r + 1)) t 0) := by
  intro hc
  have key : ∀ i j, i < j → ({i, j} : Finset ℕ) ⊆ t → False := by
    intro i j hij hsub
    have h1 := complete_updateFinset_anti _ hsub hc
    unfold IsAddCompleteNatSeq' at h1
    rw [Filter.eventually_atTop] at h1
    obtain ⟨M, hM⟩ := h1
    apply fib_delete_two_missing i j hij M 1 le_rfl (Nat.fib_pos.mpr (by omega))
    apply hM
    have := succ_le_fib_add_two (j + 2 * M)
    omega
  obtain ⟨u, hut, hu⟩ := Finset.exists_subset_card_eq ht
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hu
  rcases lt_or_gt_of_ne hxy with h | h
  · exact key x y h hut
  · exact key y x h (by rw [Finset.pair_comm]; exact hut)

-- N17
theorem exists_witness_zero (n : ℕ) (hn : 0 < n) :
    ∃ a : ℕ → ℕ, Monotone a ∧
      (∀ s : Finset ℕ, s.card = 0 → IsAddCompleteNatSeq' (Function.updateFinset a s 0)) ∧
      ∀ t : Finset ℕ, t.card = n → ¬ IsAddCompleteNatSeq' (Function.updateFinset a t 0) := by
  refine ⟨fun i => 2 ^ i, fun x y h => Nat.pow_le_pow_right (by norm_num) h, ?_, ?_⟩
  · intro s hs
    rw [Finset.card_eq_zero] at hs
    subst hs
    rw [Function.updateFinset_empty]
    unfold IsAddCompleteNatSeq'
    exact Filter.Eventually.of_forall pow_two_mem_subseqSums'
  · intro t ht
    exact pow_two_delete_incomplete t (Finset.card_pos.mp (by omega))

-- N18
theorem exists_witness_one (n : ℕ) (hn : 1 < n) :
    ∃ a : ℕ → ℕ, Monotone a ∧
      (∀ s : Finset ℕ, s.card = 1 → IsAddCompleteNatSeq' (Function.updateFinset a s 0)) ∧
      ∀ t : Finset ℕ, t.card = n → ¬ IsAddCompleteNatSeq' (Function.updateFinset a t 0) := by
  refine ⟨fun i => Nat.fib (i + 1), fun x y h => Nat.fib_mono (by omega), ?_, ?_⟩
  · intro s hs
    obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hs
    exact fib_delete_one_complete j
  · intro t ht
    exact fib_delete_incomplete t (by omega)

-- N19
theorem prefix_complement (b : ℕ → ℕ) (j : ℕ) (B : Finset ℕ) (hB : B ⊆ Finset.range j) :
    ∑ i ∈ B, b i ≤ ∑ i ∈ Finset.range j, b i ∧
      ∑ i ∈ Finset.range j \ B, b i = ∑ i ∈ Finset.range j, b i - ∑ i ∈ B, b i := by
  have h := Finset.sum_sdiff (f := b) hB
  refine ⟨Finset.sum_le_sum_of_subset hB, ?_⟩
  omega

-- N20
theorem prefix_extend (b : ℕ → ℕ) (j N : ℕ) (hjN : j ≤ N) (B K : Finset ℕ)
    (hB : B ⊆ Finset.range j) (hK : K ⊆ Finset.Ico j N) :
    B ∪ K ⊆ Finset.range N ∧ ∑ i ∈ B ∪ K, b i = ∑ i ∈ B, b i + ∑ i ∈ K, b i := by
  have hdisj : Disjoint B K := by
    rw [Finset.disjoint_left]
    intro i hi hk
    have := Finset.mem_range.mp (hB hi)
    have := (Finset.mem_Ico.mp (hK hk)).1
    omega
  refine ⟨?_, Finset.sum_union hdisj⟩
  intro i hi
  rw [Finset.mem_union] at hi
  rw [Finset.mem_range]
  rcases hi with hi | hi
  · have := Finset.mem_range.mp (hB hi)
    omega
  · have := (Finset.mem_Ico.mp (hK hi)).2
    omega

-- N21
theorem small_prefix (b : ℕ → ℕ) (T : ℕ) :
    ∃ J, ∀ w, w < T → w ∈ subseqSums' b → ∃ B ⊆ Finset.range J, ∑ i ∈ B, b i = w := by
  induction T with
  | zero => exact ⟨0, fun w hw => absurd hw (Nat.not_lt_zero w)⟩
  | succ T ih =>
    obtain ⟨J, hJ⟩ := ih
    by_cases hT : T ∈ subseqSums' b
    · rw [mem_subseqSums'_iff] at hT
      obtain ⟨B₀, hB₀⟩ := hT
      obtain ⟨n, hn⟩ := Finset.exists_nat_subset_range B₀
      refine ⟨J + n, fun w hw hwm => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hw with hw | rfl
      · obtain ⟨B, hB, hs⟩ := hJ w hw hwm
        refine ⟨B, hB.trans ?_, hs⟩
        intro i hi
        rw [Finset.mem_range] at hi ⊢
        omega
      · refine ⟨B₀, hn.trans ?_, hB₀.symm⟩
        intro i hi
        rw [Finset.mem_range] at hi ⊢
        omega
    · refine ⟨J, fun w hw hwm => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hw with hw | rfl
      · exact hJ w hw hwm
      · exact absurd hwm hT

-- N22
theorem locate_missing (b : ℕ → ℕ) (hb : Monotone b) (T : ℕ)
    (hT : ∀ x, T ≤ x → x ∈ subseqSums' b) (N x : ℕ) (hx1 : T ≤ x)
    (hx2 : x + T ≤ ∑ i ∈ Finset.range N, b i)
    (hmiss : ¬ ∃ B ⊆ Finset.range N, ∑ i ∈ B, b i = x) :
    ∃ j < N, x ≤ ∑ i ∈ Finset.range j, b i ∧ ∑ i ∈ Finset.range j, b i < x + T := by
  classical
  have hex : ∃ j, x ≤ ∑ i ∈ Finset.range j, b i := ⟨N, by omega⟩
  obtain ⟨j, hj, hmin⟩ : ∃ j, x ≤ ∑ i ∈ Finset.range j, b i ∧
      ∀ m < j, ¬ x ≤ ∑ i ∈ Finset.range m, b i :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  have hjN : j ≤ N := by
    by_contra h
    exact hmin N (by omega) (by omega)
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hmiss ⟨∅, Finset.empty_subset _, by simp⟩
  have hj0 : j ≠ 0 := by
    intro h
    rw [h] at hj
    simp at hj
    omega
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hprev : ¬ x ≤ ∑ i ∈ Finset.range j', b i := hmin j' (by omega)
  have hSj : ∑ i ∈ Finset.range (j' + 1), b i = ∑ i ∈ Finset.range j', b i + b j' :=
    Finset.sum_range_succ _ _
  by_cases hlt : ∑ i ∈ Finset.range (j' + 1), b i < x + T
  · refine ⟨j' + 1, ?_, hj, hlt⟩
    rcases Nat.lt_or_eq_of_le hjN with h | h
    · exact h
    · exfalso
      rw [h] at hlt
      omega
  · exfalso
    push Not at hlt
    obtain ⟨B', hB'⟩ := (mem_subseqSums'_iff b _).mp
      (hT (∑ i ∈ Finset.range (j' + 1), b i - x) (by omega))
    have hB'r : B' ⊆ Finset.range j' := by
      intro i hi
      rw [Finset.mem_range]
      by_contra hc
      push Not at hc
      have h1 : b i ≤ ∑ k ∈ B', b k := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
      have h2 := hb hc
      omega
    have hB'j : B' ⊆ Finset.range (j' + 1) :=
      hB'r.trans (Finset.range_subset_range.mpr (by omega))
    obtain ⟨_, hc⟩ := prefix_complement b (j' + 1) B' hB'j
    apply hmiss
    refine ⟨Finset.range (j' + 1) \ B',
      Finset.sdiff_subset.trans (Finset.range_subset_range.mpr hjN), ?_⟩
    rw [hc]
    omega

-- N23
theorem missing_ge_next (b : ℕ → ℕ) (hb : Monotone b) (N x : ℕ) (hx : x ∈ subseqSums' b)
    (hmiss : ¬ ∃ B ⊆ Finset.range N, ∑ i ∈ B, b i = x) : b N ≤ x := by
  rw [mem_subseqSums'_iff] at hx
  obtain ⟨B, hB⟩ := hx
  by_contra hlt
  push Not at hlt
  apply hmiss
  refine ⟨B, ?_, hB.symm⟩
  intro i hi
  rw [Finset.mem_range]
  by_contra hiN
  push Not at hiN
  have h1 := hb hiN
  have h2 : b i ≤ ∑ k ∈ B, b k := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
  omega

-- N24
theorem initial_state (b : ℕ → ℕ) (hb : Monotone b) (hunb : ¬ BddAbove (Set.range b))
    (T : ℕ) (hT : ∀ x, T ≤ x → x ∈ subseqSums' b) (L : ℕ) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∀ x, T ≤ x → x + T ≤ ∑ i ∈ Finset.range N, b i →
      (¬ ∃ B ⊆ Finset.range N, ∑ i ∈ B, b i = x) →
      ∃ j u, L ≤ j ∧ j < N ∧ u ∉ subseqSums' b ∧ u ≤ ∑ i ∈ Finset.range j, b i ∧
        ¬ ∃ B ⊆ Finset.range N, ∑ i ∈ B, b i = ∑ i ∈ Finset.range j, b i - u := by
  obtain ⟨J, hJ⟩ := small_prefix b T
  rw [not_bddAbove_iff] at hunb
  obtain ⟨_, ⟨N₀, rfl⟩, hN₀⟩ := hunb (∑ i ∈ Finset.range (J + L), b i)
  refine ⟨N₀, fun N hN x hx1 hx2 hmiss => ?_⟩
  obtain ⟨j, hjN, hxj, hjx⟩ := locate_missing b hb T hT N x hx1 hx2 hmiss
  have hbN := missing_ge_next b hb N x (hT x hx1) hmiss
  have hbN0 := hb hN
  have hjL : J + L ≤ j := by
    by_contra h
    push Not at h
    have : ∑ i ∈ Finset.range j, b i ≤ ∑ i ∈ Finset.range (J + L), b i :=
      Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr h.le)
    omega
  refine ⟨j, ∑ i ∈ Finset.range j, b i - x, by omega, hjN, ?_, by omega, ?_⟩
  · intro hu
    obtain ⟨B, hB, hBs⟩ := hJ _ (by omega) hu
    apply hmiss
    have hBj : B ⊆ Finset.range j := hB.trans (Finset.range_subset_range.mpr (by omega))
    obtain ⟨_, hc⟩ := prefix_complement b j B hBj
    refine ⟨Finset.range j \ B,
      Finset.sdiff_subset.trans (Finset.range_subset_range.mpr hjN.le), ?_⟩
    rw [hc, hBs]
    omega
  · rw [show ∑ i ∈ Finset.range j, b i - (∑ i ∈ Finset.range j, b i - x) = x by omega]
    exact hmiss

-- N25
theorem normalize_state (b : ℕ → ℕ) (hb : Monotone b) (hpos : ∀ i, 0 < b i)
    (hunb : ¬ BddAbove (Set.range b)) (T : ℕ) (hT : ∀ x, T ≤ x → x ∈ subseqSums' b) (L : ℕ) :
    ∃ J₀, ∀ (j N : ℕ) (E : Finset ℕ), J₀ ≤ j →
      (j < N ∧ E.Nonempty ∧ (∀ e ∈ E, e ∉ subseqSums' b ∧ e ≤ ∑ i ∈ Finset.range j, b i ∧
        ¬ ∃ B ⊆ Finset.range N, ∑ i ∈ B, b i = ∑ i ∈ Finset.range j, b i - e)) →
      ∃ j' N', L ≤ j' ∧
        (j' < N' ∧ E.Nonempty ∧ (∀ e ∈ E, e ∉ subseqSums' b ∧ e ≤ ∑ i ∈ Finset.range j', b i ∧
          ¬ ∃ B ⊆ Finset.range N', ∑ i ∈ B, b i = ∑ i ∈ Finset.range j', b i - e)) ∧
        (0 < j' ∧ ((∀ r ∈ Finset.Ico j' N', b r = b j') → b (j' - 1) < b j')) ∧
        ((∀ r ∈ Finset.Ico j N, b r = b j) ↔ (∀ r ∈ Finset.Ico j' N', b r = b j')) := by
  classical
  rw [not_bddAbove_iff] at hunb
  obtain ⟨_, ⟨J₀, rfl⟩, hJ₀⟩ := hunb (b (L + T))
  refine ⟨J₀, fun j N E hjJ hst => ?_⟩
  have hbj : b (L + T) < b j := lt_of_lt_of_le hJ₀ (hb hjJ)
  have hLj : L + T < j := by
    by_contra h
    push Not at h
    have := hb h
    omega
  by_cases hconst : ∀ r ∈ Finset.Ico j N, b r = b j
  · have hex : ∃ i, b i = b j := ⟨j, rfl⟩
    obtain ⟨j', hj'1, hj'min⟩ : ∃ j', b j' = b j ∧ ∀ m < j', b m ≠ b j :=
      ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
    have hj'2 : j' ≤ j := by
      by_contra h
      exact hj'min j (by omega) rfl
    have hLj' : L + T < j' := by
      by_contra h
      push Not at h
      have := hb h
      omega
    obtain ⟨hjN, hne, hE⟩ := hst
    have hall : ∀ r, j' ≤ r → r < N → b r = b j := by
      intro r h1 h2
      by_cases hrj : r ≤ j
      · have := hb hrj
        have := hb h1
        omega
      · exact hconst r (Finset.mem_Ico.mpr ⟨by omega, h2⟩)
    refine ⟨j', j' + (N - j), by omega, ⟨by omega, hne, ?_⟩, ⟨by omega, fun _ => ?_⟩, ?_⟩
    · intro e he
      obtain ⟨he1, he2, he3⟩ := hE e he
      have heT : e < T := by
        by_contra h
        push Not at h
        exact he1 (hT e h)
      have hSj' : j' ≤ ∑ i ∈ Finset.range j', b i := range_le_sum b hpos j'
      refine ⟨he1, by omega, ?_⟩
      rintro ⟨B, hB, hBs⟩
      apply he3
      obtain ⟨hsub, hsum⟩ := prefix_extend b (j' + (N - j)) N (by omega) B
        (Finset.Ico (j' + (N - j)) N) hB (Finset.Subset.refl _)
      refine ⟨B ∪ Finset.Ico (j' + (N - j)) N, hsub, ?_⟩
      rw [hsum, hBs]
      have h1 : ∑ i ∈ Finset.Ico (j' + (N - j)) N, b i = (j - j') * b j := by
        rw [Finset.sum_congr rfl (fun r hr => hall r (by have := (Finset.mem_Ico.mp hr).1; omega)
          (Finset.mem_Ico.mp hr).2)]
        rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]
        congr 1
        omega
      have h2 : ∑ i ∈ Finset.range j, b i = ∑ i ∈ Finset.range j', b i + (j - j') * b j := by
        rw [← Finset.sum_range_add_sum_Ico b hj'2]
        congr 1
        rw [Finset.sum_congr rfl (fun r hr => hall r (Finset.mem_Ico.mp hr).1
          (by have := (Finset.mem_Ico.mp hr).2; omega))]
        rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]
      rw [h1, h2]
      omega
    · have hne' : b (j' - 1) ≠ b j := hj'min (j' - 1) (by omega)
      have := hb (show j' - 1 ≤ j' by omega)
      omega
    · constructor
      · intro _ r hr
        rw [Finset.mem_Ico] at hr
        rw [hj'1]
        exact hall r hr.1 (by omega)
      · intro _
        exact hconst
  · obtain ⟨hjN, hne, hE⟩ := hst
    exact ⟨j, N, by omega, ⟨hjN, hne, hE⟩, ⟨by omega, fun h => absurd h hconst⟩, Iff.rfl⟩

-- N26
theorem gap_bound (b : ℕ → ℕ) (hb : Monotone b) (T : ℕ)
    (hT : ∀ x, T ≤ x → x ∈ subseqSums' b) (j N : ℕ) (E : Finset ℕ)
    (hst : j < N ∧ E.Nonempty ∧ (∀ e ∈ E, e ∉ subseqSums' b ∧ e ≤ ∑ i ∈ Finset.range j, b i ∧
      ¬ ∃ B ⊆ Finset.range N, ∑ i ∈ B, b i = ∑ i ∈ Finset.range j, b i - e))
    (hTj : T ≤ b j) (k : ℕ) (hjk : j ≤ k) (hlt : b j < b k)
    (hblock : ∀ r ∈ Finset.Ico j k, b r = b j) :
    ∀ e ∈ E, b k - b j ≤ e := by
  obtain ⟨hjN, -, hE⟩ := hst
  intro e he
  obtain ⟨he1, he2, he3⟩ := hE e he
  by_contra hlt
  push Not at hlt
  have hy := hT (b j + e) (by omega)
  rw [mem_subseqSums'_iff] at hy
  obtain ⟨B, hB⟩ := hy
  have hBk : ∀ i ∈ B, i < k := by
    intro i hi
    by_contra hik
    push Not at hik
    have h1 : b i ≤ ∑ r ∈ B, b r := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
    have h2 := hb hik
    omega
  by_cases hblk : ∃ r ∈ B, j ≤ r
  · obtain ⟨r, hrB, hjr⟩ := hblk
    have hbr : b r = b j := hblock r (Finset.mem_Ico.mpr ⟨hjr, hBk r hrB⟩)
    apply he1
    rw [mem_subseqSums'_iff]
    refine ⟨B.erase r, ?_⟩
    have := Finset.sum_erase_add B b hrB
    omega
  · push Not at hblk
    have hBj : B ⊆ Finset.range (j + 1) :=
      fun i hi => Finset.mem_range.mpr (by have := hblk i hi; omega)
    obtain ⟨_, hc⟩ := prefix_complement b (j + 1) B hBj
    apply he3
    refine ⟨Finset.range (j + 1) \ B,
      Finset.sdiff_subset.trans (Finset.range_subset_range.mpr (by omega)), ?_⟩
    rw [hc, ← hB, Finset.sum_range_succ]
    omega

-- N27
theorem recut (b : ℕ → ℕ) (hb : Monotone b) (hunb : ¬ BddAbove (Set.range b)) (T : ℕ)
    (hT1 : 1 ≤ T) (hT : ∀ x, T ≤ x → x ∈ subseqSums' b) (L : ℕ) :
    ∃ M₀, ∀ (j : ℕ) (R : Finset ℕ), R.Nonempty →
      (∀ x ∈ R, M₀ ≤ x ∧ x + T ≤ ∑ i ∈ Finset.range j, b i ∧
        ¬ ∃ B ⊆ Finset.range j, ∑ i ∈ B, b i = x) →
      (∀ x ∈ R, ∀ y ∈ R, x ≤ y + 2 * T) →
      ∃ (l : ℕ) (E' : Finset ℕ), L ≤ l ∧
        (l < j ∧ E'.Nonempty ∧ (∀ e ∈ E', e ∉ subseqSums' b ∧ e ≤ ∑ i ∈ Finset.range l, b i ∧
          ¬ ∃ B ⊆ Finset.range j, ∑ i ∈ B, b i = ∑ i ∈ Finset.range l, b i - e)) ∧
        E'.card = R.card ∧
        (∀ x ∈ R, ∃ e ∈ E', x + e = ∑ i ∈ Finset.range l, b i) ∧
        (∀ e ∈ E', ∑ i ∈ Finset.range l, b i - e ∈ R) := by
  classical
  obtain ⟨J, hJ⟩ := small_prefix b (3 * T)
  refine ⟨∑ i ∈ Finset.range (L + J + 1), b i + T, fun j R hR hRx hRd => ?_⟩
  have hxmR : R.max' hR ∈ R := R.max'_mem hR
  have hle : ∀ x ∈ R, x ≤ R.max' hR := fun x hx => R.le_max' x hx
  obtain ⟨hxm1, hxm2, hxm3⟩ := hRx _ hxmR
  obtain ⟨l, hlj, hxl, hlx⟩ := locate_missing b hb T hT j _ (by omega) hxm2 hxm3
  have hLl : L + J + 1 ≤ l := by
    by_contra h
    push Not at h
    have : ∑ i ∈ Finset.range l, b i ≤ ∑ i ∈ Finset.range (L + J + 1), b i :=
      Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr h.le)
    omega
  have hkey : ∀ x ∈ R, ∑ i ∈ Finset.range l, b i - x ∉ subseqSums' b := by
    intro x hx hmem
    have h1 := hRd _ hxmR x hx
    have h2 := hle x hx
    obtain ⟨B, hB, hBs⟩ := hJ _ (by omega) hmem
    have hBl : B ⊆ Finset.range l := hB.trans (Finset.range_subset_range.mpr (by omega))
    obtain ⟨_, hc⟩ := prefix_complement b l B hBl
    apply (hRx x hx).2.2
    refine ⟨Finset.range l \ B,
      Finset.sdiff_subset.trans (Finset.range_subset_range.mpr hlj.le), ?_⟩
    rw [hc, hBs]
    omega
  refine ⟨l, R.image (fun x => ∑ i ∈ Finset.range l, b i - x), by omega,
    ⟨hlj, hR.image _, ?_⟩, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
    have := hle x hx
    refine ⟨hkey x hx, by omega, ?_⟩
    rw [show ∑ i ∈ Finset.range l, b i - (∑ i ∈ Finset.range l, b i - x) = x by omega]
    exact (hRx x hx).2.2
  · apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    have := hle x hx
    have := hle y hy
    simp only at hxy
    omega
  · intro x hx
    exact ⟨_, Finset.mem_image_of_mem _ hx, by have := hle x hx; omega⟩
  · intro e he
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
    rw [show ∑ i ∈ Finset.range l, b i - (∑ i ∈ Finset.range l, b i - x) = x by
      have := hle x hx; omega]
    exact hx

-- N28
theorem distinct_transition (b : ℕ → ℕ) (hb : Monotone b) (hpos : ∀ i, 0 < b i)
    (hunb : ¬ BddAbove (Set.range b)) (T : ℕ) (hT1 : 1 ≤ T)
    (hT : ∀ x, T ≤ x → x ∈ subseqSums' b)
    (hδ : Filter.Tendsto (fun k => (∑ i ∈ Finset.range k, (b i : ℤ)) - (b k : ℤ))
      Filter.atTop Filter.atTop) (L : ℕ) :
    ∃ J₀, ∀ (j N : ℕ) (E : Finset ℕ), J₀ ≤ j →
      (j < N ∧ E.Nonempty ∧ (∀ e ∈ E, e ∉ subseqSums' b ∧ e ≤ ∑ i ∈ Finset.range j, b i ∧
        ¬ ∃ B ⊆ Finset.range N, ∑ i ∈ B, b i = ∑ i ∈ Finset.range j, b i - e)) →
      (∃ r ∈ Finset.Ico j N, b r ≠ b j) →
      ∃ (l : ℕ) (E' : Finset ℕ), L ≤ l ∧
        (l < j ∧ E'.Nonempty ∧ (∀ e ∈ E', e ∉ subseqSums' b ∧ e ≤ ∑ i ∈ Finset.range l, b i ∧
          ¬ ∃ B ⊆ Finset.range j, ∑ i ∈ B, b i = ∑ i ∈ Finset.range l, b i - e)) ∧
        E.card < E'.card := by
  sorry

-- N29
theorem constant_transition (b : ℕ → ℕ) (hb : Monotone b) (hpos : ∀ i, 0 < b i)
    (hunb : ¬ BddAbove (Set.range b)) (T : ℕ) (hT1 : 1 ≤ T)
    (hT : ∀ x, T ≤ x → x ∈ subseqSums' b)
    (hδ : Filter.Tendsto (fun k => (∑ i ∈ Finset.range k, (b i : ℤ)) - (b k : ℤ))
      Filter.atTop Filter.atTop) (L : ℕ) :
    ∃ J₀, ∀ (j N : ℕ) (E : Finset ℕ), J₀ ≤ j →
      (j < N ∧ E.Nonempty ∧ (∀ e ∈ E, e ∉ subseqSums' b ∧ e ≤ ∑ i ∈ Finset.range j, b i ∧
        ¬ ∃ B ⊆ Finset.range N, ∑ i ∈ B, b i = ∑ i ∈ Finset.range j, b i - e)) →
      0 < j → (∀ r ∈ Finset.Ico j N, b r = b j) → b (j - 1) < b j →
      ∃ (l : ℕ) (E' : Finset ℕ), L ≤ l ∧
        (l < j ∧ E'.Nonempty ∧ (∀ e ∈ E', e ∉ subseqSums' b ∧ e ≤ ∑ i ∈ Finset.range l, b i ∧
          ¬ ∃ B ⊆ Finset.range j, ∑ i ∈ B, b i = ∑ i ∈ Finset.range l, b i - e)) ∧
        E'.card = E.card ∧
        ((∃ r ∈ Finset.Ico l j, b r ≠ b l) ∨ ∀ e' ∈ E', ∃ e ∈ E, e < e') := by
  sorry

-- N30
theorem potential_step (b : ℕ → ℕ) (hb : Monotone b) (hpos : ∀ i, 0 < b i)
    (hunb : ¬ BddAbove (Set.range b)) (T : ℕ) (hT1 : 1 ≤ T)
    (hT : ∀ x, T ≤ x → x ∈ subseqSums' b)
    (hδ : Filter.Tendsto (fun k => (∑ i ∈ Finset.range k, (b i : ℤ)) - (b k : ℤ))
      Filter.atTop Filter.atTop) (t : ℕ)
    (ht : ∀ L, ∃ (j N : ℕ) (E : Finset ℕ), L ≤ j ∧
      (j < N ∧ E.Nonempty ∧ (∀ e ∈ E, e ∉ subseqSums' b ∧ e ≤ ∑ i ∈ Finset.range j, b i ∧
        ¬ ∃ B ⊆ Finset.range N, ∑ i ∈ B, b i = ∑ i ∈ Finset.range j, b i - e)) ∧
      (0 < j ∧ ((∀ r ∈ Finset.Ico j N, b r = b j) → b (j - 1) < b j)) ∧
      ((∀ r ∈ Finset.Ico j N, b r = b j) → ∀ e ∈ E, t ≤ (T + 1) * E.card + e) ∧
      ((∃ r ∈ Finset.Ico j N, b r ≠ b j) → t ≤ (T + 1) * (E.card + 1))) :
    ∀ L, ∃ (j N : ℕ) (E : Finset ℕ), L ≤ j ∧
      (j < N ∧ E.Nonempty ∧ (∀ e ∈ E, e ∉ subseqSums' b ∧ e ≤ ∑ i ∈ Finset.range j, b i ∧
        ¬ ∃ B ⊆ Finset.range N, ∑ i ∈ B, b i = ∑ i ∈ Finset.range j, b i - e)) ∧
      (0 < j ∧ ((∀ r ∈ Finset.Ico j N, b r = b j) → b (j - 1) < b j)) ∧
      ((∀ r ∈ Finset.Ico j N, b r = b j) → ∀ e ∈ E, t + 1 ≤ (T + 1) * E.card + e) ∧
      ((∃ r ∈ Finset.Ico j N, b r ≠ b j) → t + 1 ≤ (T + 1) * (E.card + 1)) := by
  sorry

-- N31
theorem potential_bound (b : ℕ → ℕ) (T : ℕ) (hT : ∀ x, T ≤ x → x ∈ subseqSums' b)
    (j N : ℕ) (E : Finset ℕ)
    (hst : j < N ∧ E.Nonempty ∧ (∀ e ∈ E, e ∉ subseqSums' b ∧ e ≤ ∑ i ∈ Finset.range j, b i ∧
      ¬ ∃ B ⊆ Finset.range N, ∑ i ∈ B, b i = ∑ i ∈ Finset.range j, b i - e)) :
    ¬ (((∀ r ∈ Finset.Ico j N, b r = b j) → ∀ e ∈ E, (T + 1) * (T + 1) ≤ (T + 1) * E.card + e) ∧
      ((∃ r ∈ Finset.Ico j N, b r ≠ b j) → (T + 1) * (T + 1) ≤ (T + 1) * (E.card + 1))) := by
  obtain ⟨hjN, hne, hE⟩ := hst
  have hlab : ∀ e ∈ E, 1 ≤ e ∧ e < T := by
    intro e he
    have h := (hE e he).1
    constructor
    · by_contra h0
      push Not at h0
      apply h
      rw [mem_subseqSums'_iff]
      exact ⟨∅, by simp; omega⟩
    · by_contra h0
      push Not at h0
      exact h (hT e h0)
  have hsub : E ⊆ Finset.Ico 1 T := fun e he => Finset.mem_Ico.mpr (hlab e he)
  have hcard : E.card + 1 ≤ T := by
    have := Finset.card_le_card hsub
    simp only [Nat.card_Ico] at this
    obtain ⟨e, he⟩ := hne
    have := hlab e he
    omega
  rintro ⟨h1, h2⟩
  obtain ⟨e, he⟩ := hne
  have hl := hlab e he
  have hm := Nat.mul_le_mul_left (T + 1) hcard
  by_cases hc : ∀ r ∈ Finset.Ico j N, b r = b j
  · have := h1 hc e he
    nlinarith
  · push Not at hc
    have := h2 hc
    nlinarith

-- N32
theorem central_unbounded (b : ℕ → ℕ) (hb : Monotone b) (hpos : ∀ i, 0 < b i)
    (hunb : ¬ BddAbove (Set.range b)) (T : ℕ) (hT1 : 1 ≤ T)
    (hT : ∀ x, T ≤ x → x ∈ subseqSums' b)
    (hδ : Filter.Tendsto (fun k => (∑ i ∈ Finset.range k, (b i : ℤ)) - (b k : ℤ))
      Filter.atTop Filter.atTop) :
    ∀ᶠ N in Filter.atTop, ∀ x, T ≤ x → x + T ≤ ∑ i ∈ Finset.range N, b i →
      ∃ B ⊆ Finset.range N, ∑ i ∈ B, b i = x := by
  sorry

theorem range_le_sum (b : ℕ → ℕ) (hpos : ∀ i, 0 < b i) (k : ℕ) :
    k ≤ ∑ i ∈ Finset.range k, b i := by
  have h : ∑ i ∈ Finset.range k, 1 ≤ ∑ i ∈ Finset.range k, b i :=
    Finset.sum_le_sum fun i _ => hpos i
  simpa using h

-- N33
theorem central_bounded (b : ℕ → ℕ) (hb : Monotone b) (hpos : ∀ i, 0 < b i)
    (hbdd : BddAbove (Set.range b)) (T : ℕ) (hT : ∀ x, T ≤ x → x ∈ subseqSums' b) :
    ∀ᶠ N in Filter.atTop, ∀ x, T ≤ x → x + T ≤ ∑ i ∈ Finset.range N, b i →
      ∃ B ⊆ Finset.range N, ∑ i ∈ B, b i = x := by
  obtain ⟨N0, c, hc⟩ := monotone_bddAbove_eventually_const b hb hbdd
  have hcpos : 0 < c := by
    have := hpos N0
    rw [hc N0 le_rfl] at this
    exact this
  have hswap : ∀ N, N0 ≤ N → ∀ y, y ∈ subseqSums' b → y ≤ (N - N0) * c →
      ∃ B ⊆ Finset.range N, ∑ i ∈ B, b i = y := by
    intro N hN y hy hyle
    rw [mem_subseqSums'_iff] at hy
    obtain ⟨B, rfl⟩ := hy
    have h2 : ∑ i ∈ B.filter (fun i => ¬ i < N0), b i
        = (B.filter (fun i => ¬ i < N0)).card * c := by
      rw [Finset.sum_congr rfl (fun i hi => hc i (by have := (Finset.mem_filter.mp hi).2; omega))]
      simp
    have hsplit := Finset.sum_filter_add_sum_filter_not B (· < N0) b
    have hm : (B.filter (fun i => ¬ i < N0)).card ≤ N - N0 := by
      by_contra h
      have h' : N - N0 + 1 ≤ (B.filter (fun i => ¬ i < N0)).card := by omega
      have : (N - N0 + 1) * c ≤ (B.filter (fun i => ¬ i < N0)).card * c :=
        Nat.mul_le_mul_right c h'
      rw [Nat.add_mul, one_mul] at this
      omega
    refine ⟨B.filter (· < N0) ∪ Finset.Ico N0 (N0 + (B.filter (fun i => ¬ i < N0)).card), ?_, ?_⟩
    · intro i hi
      rw [Finset.mem_union] at hi
      rw [Finset.mem_range]
      rcases hi with hi | hi
      · have := (Finset.mem_filter.mp hi).2
        omega
      · have := Finset.mem_Ico.mp hi
        omega
    · have hdisj : Disjoint (B.filter (· < N0))
          (Finset.Ico N0 (N0 + (B.filter (fun i => ¬ i < N0)).card)) := by
        rw [Finset.disjoint_left]
        intro i h1 h3
        have := (Finset.mem_filter.mp h1).2
        have := (Finset.mem_Ico.mp h3).1
        omega
      rw [Finset.sum_union hdisj]
      have h3 : ∑ i ∈ Finset.Ico N0 (N0 + (B.filter (fun i => ¬ i < N0)).card), b i
          = (B.filter (fun i => ¬ i < N0)).card * c := by
        rw [Finset.sum_congr rfl (fun i hi => hc i (Finset.mem_Ico.mp hi).1)]
        simp
      omega
  have hS : ∀ N, N0 ≤ N →
      ∑ i ∈ Finset.range N, b i = ∑ i ∈ Finset.range N0, b i + (N - N0) * c := by
    intro N hN
    rw [← Finset.sum_range_add_sum_Ico b hN]
    rw [Finset.sum_congr rfl (fun i hi => hc i (Finset.mem_Ico.mp hi).1)]
    simp
  rw [Filter.eventually_atTop]
  refine ⟨N0 + ∑ i ∈ Finset.range N0, b i + 1, fun N hN x hx1 hx2 => ?_⟩
  have hSN := hS N (by omega)
  have hNc : N - N0 ≤ (N - N0) * c := Nat.le_mul_of_pos_right _ hcpos
  by_cases hxle : x ≤ (N - N0) * c
  · exact hswap N (by omega) x (hT x hx1) hxle
  · obtain ⟨B, hB, hBs⟩ := hswap N (by omega) (∑ i ∈ Finset.range N, b i - x)
      (hT _ (by omega)) (by omega)
    obtain ⟨_, hc2⟩ := prefix_complement b N B hB
    refine ⟨Finset.range N \ B, Finset.sdiff_subset, ?_⟩
    rw [hc2, hBs]
    omega

-- N34
theorem central_interval (b : ℕ → ℕ) (hb : Monotone b) (hpos : ∀ i, 0 < b i) (T : ℕ)
    (hT1 : 1 ≤ T) (hT : ∀ x, T ≤ x → x ∈ subseqSums' b)
    (hδ : Filter.Tendsto (fun k => (∑ i ∈ Finset.range k, (b i : ℤ)) - (b k : ℤ))
      Filter.atTop Filter.atTop) :
    ∀ᶠ N in Filter.atTop, ∀ x, T ≤ x → x + T ≤ ∑ i ∈ Finset.range N, b i →
      ∃ B ⊆ Finset.range N, ∑ i ∈ B, b i = x := by
  by_cases hbdd : BddAbove (Set.range b)
  · exact central_bounded b hb hpos hbdd T hT
  · exact central_unbounded b hb hpos hbdd T hT1 hT hδ

-- N35
theorem slack_tendsto (b : ℕ → ℕ) (hb : Monotone b) (hpos : ∀ i, 0 < b i) (C : ℕ)
    (hdel : ∀ i, ∀ᶠ x in Filter.atTop,
      ∃ d ≤ C, ∃ y ∈ subseqSums' (Function.updateFinset b {i} 0), x = d + y) :
    Filter.Tendsto (fun k => (∑ i ∈ Finset.range k, (b i : ℤ)) - (b k : ℤ))
      Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro K
  have hcast : ∀ k, ((∑ i ∈ Finset.range k, b i : ℕ) : ℤ) = ∑ i ∈ Finset.range k, (b i : ℤ) :=
    fun k => Nat.cast_sum _ _
  by_cases hbdd : BddAbove (Set.range b)
  · obtain ⟨c, hc⟩ := hbdd
    refine ⟨K.toNat + c, fun k hk => ?_⟩
    have h1 := range_le_sum b hpos k
    have h2 : b k ≤ c := hc ⟨k, rfl⟩
    rw [← hcast k]
    have := Int.self_le_toNat K
    omega
  · rw [not_bddAbove_iff] at hbdd
    by_contra hcon
    push Not at hcon
    obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hbdd (K.toNat + C + 1)
    have hdi := hdel i
    rw [Filter.eventually_atTop] at hdi
    obtain ⟨M, hM⟩ := hdi
    obtain ⟨_, ⟨N1, rfl⟩, hN1⟩ := hbdd M
    obtain ⟨k, hk, hfk⟩ := hcon (N1 + i + 1)
    rw [← hcast k] at hfk
    have hbk : b N1 ≤ b k := hb (by omega)
    obtain ⟨d, hd, y, hy, hxy⟩ := hM (b k - 1) (by omega)
    rw [mem_subseqSums'_updateFinset] at hy
    obtain ⟨B, hB, rfl⟩ := hy
    have hiB : i ∉ B := fun h => Finset.disjoint_left.mp hB h (Finset.mem_singleton_self i)
    by_cases hBk : B ⊆ Finset.range k
    · have hsub : insert i B ⊆ Finset.range k :=
        Finset.insert_subset (Finset.mem_range.mpr (by omega)) hBk
      have h1 := Finset.sum_le_sum_of_subset (f := b) hsub
      rw [Finset.sum_insert hiB] at h1
      have := Int.self_le_toNat K
      omega
    · rw [Finset.not_subset] at hBk
      obtain ⟨r, hrB, hrk⟩ := hBk
      rw [Finset.mem_range] at hrk
      have h1 : b r ≤ ∑ i ∈ B, b i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hrB
      have h2 := hb (show k ≤ r by omega)
      omega

-- N36
theorem not_bddAbove_of_deletion_minimal (b : ℕ → ℕ) (hb : Monotone b)
    (hcomp : IsAddCompleteNatSeq' b)
    (hmin : ∀ i, ¬ IsAddCompleteNatSeq' (Function.updateFinset b {i} 0)) :
    ¬ BddAbove (Set.range b) := by
  intro hbdd
  obtain ⟨N, c, hc⟩ := monotone_bddAbove_eventually_const b hb hbdd
  apply hmin N
  unfold IsAddCompleteNatSeq' at hcomp ⊢
  refine hcomp.mono fun x hx => ?_
  rw [mem_subseqSums'_iff] at hx
  rw [mem_subseqSums'_updateFinset]
  obtain ⟨B, rfl⟩ := hx
  by_cases hN : N ∈ B
  · obtain ⟨m, hm⟩ := Finset.exists_nat_subset_range B
    have hm'B : m + N + 1 ∉ B := fun h => by
      have := Finset.mem_range.mp (hm h)
      omega
    refine ⟨insert (m + N + 1) (B.erase N), ?_, ?_⟩
    · rw [Finset.disjoint_singleton_right]
      intro h
      rw [Finset.mem_insert] at h
      rcases h with h | h
      · omega
      · exact Finset.notMem_erase N B h
    · rw [Finset.sum_insert (fun h => hm'B (Finset.mem_of_mem_erase h)), hc (m + N + 1) (by omega)]
      rw [← Finset.add_sum_erase B b hN, hc N le_rfl]
  · exact ⟨B, Finset.disjoint_singleton_right.mpr hN, rfl⟩

-- N37
theorem tail_gaps (b : ℕ → ℕ) (hpos : ∀ i, 0 < b i) (T k : ℕ)
    (hk2T : 2 * T ≤ ∑ i ∈ Finset.range k, b i)
    (hcent : ∀ x, T ≤ x → x + T ≤ ∑ i ∈ Finset.range k, b i →
      ∃ B ⊆ Finset.range k, ∑ i ∈ B, b i = x)
    (j : ℕ) (hkj : k ≤ j)
    (hminj : ¬ IsAddCompleteNatSeq' (Function.updateFinset b {j} 0)) (M : ℕ) :
    ∃ q, M ≤ q ∧ (∃ B : Finset ℕ, (∀ i ∈ B, k ≤ i ∧ i ≠ j) ∧ ∑ i ∈ B, b i = q) ∧
      ∀ y, (∃ B : Finset ℕ, (∀ i ∈ B, k ≤ i ∧ i ≠ j) ∧ ∑ i ∈ B, b i = y) →
        y ≤ q ∨ q + (∑ i ∈ Finset.range k, b i - 2 * T + 1) < y := by
  classical
  by_contra hcon
  push Not at hcon
  apply hminj
  have hQ0 : ∃ B : Finset ℕ, (∀ i ∈ B, k ≤ i ∧ i ≠ j) ∧ M ≤ ∑ i ∈ B, b i := by
    refine ⟨Finset.Ico (j + 1) (j + 1 + M), ?_, ?_⟩
    · intro i hi
      rw [Finset.mem_Ico] at hi
      omega
    · have h1 : ∑ i ∈ Finset.Ico (j + 1) (j + 1 + M), 1
          ≤ ∑ i ∈ Finset.Ico (j + 1) (j + 1 + M), b i :=
        Finset.sum_le_sum fun i _ => hpos i
      simpa using h1
  obtain ⟨B0, hB0, hB0M⟩ := hQ0
  unfold IsAddCompleteNatSeq'
  rw [Filter.eventually_atTop]
  refine ⟨∑ i ∈ B0, b i + T, fun x hx => ?_⟩
  let P : ℕ → Prop := fun q => M ≤ q ∧
    ∃ B : Finset ℕ, (∀ i ∈ B, k ≤ i ∧ i ≠ j) ∧ ∑ i ∈ B, b i = q
  have hP0 : P (∑ i ∈ B0, b i) := ⟨hB0M, B0, hB0, rfl⟩
  have hq := Nat.findGreatest_spec (P := P) (show ∑ i ∈ B0, b i ≤ x - T by omega) hP0
  have hqle := Nat.findGreatest_le (P := P) (x - T)
  have hqmax : ∀ y, y ≤ x - T → P y → y ≤ Nat.findGreatest P (x - T) :=
    fun y hy hPy => Nat.le_findGreatest hy hPy
  obtain ⟨hMq, Bq, hBq, hBqs⟩ := hq
  obtain ⟨y, hy1, hy2, hy3⟩ := hcon (Nat.findGreatest P (x - T)) hMq ⟨Bq, hBq, hBqs⟩
  have hyx : x - T < y := by
    by_contra hle
    push Not at hle
    have := hqmax y hle ⟨by omega, hy1⟩
    omega
  obtain ⟨Bp, hBp, hBps⟩ := hcent (x - Nat.findGreatest P (x - T)) (by omega) (by omega)
  rw [mem_subseqSums'_updateFinset]
  have hdisj : Disjoint Bp Bq := by
    rw [Finset.disjoint_left]
    intro r h1 h2
    have := Finset.mem_range.mp (hBp h1)
    have := (hBq r h2).1
    omega
  refine ⟨Bp ∪ Bq, ?_, ?_⟩
  · rw [Finset.disjoint_union_left]
    constructor
    · rw [Finset.disjoint_singleton_right]
      intro h
      have := Finset.mem_range.mp (hBp h)
      omega
    · rw [Finset.disjoint_singleton_right]
      intro h
      exact (hBq j h).2 rfl
  · rw [Finset.sum_union hdisj, hBps, hBqs]
    omega

-- N38
theorem pair_split (b : ℕ → ℕ) (i k j : ℕ) (hik : i < k) (hkj : k ≤ j) (x : ℕ)
    (hx : x ∈ subseqSums' (Function.updateFinset b {i, j} 0)) :
    ∃ f y, x = f + y ∧ f + b i ≤ ∑ r ∈ Finset.range k, b r ∧
      ∃ B : Finset ℕ, (∀ r ∈ B, k ≤ r ∧ r ≠ j) ∧ ∑ r ∈ B, b r = y := by
  rw [mem_subseqSums'_updateFinset] at hx
  obtain ⟨B, hB, rfl⟩ := hx
  have hiB : i ∉ B := fun h => Finset.disjoint_left.mp hB h (by simp)
  have hjB : j ∉ B := fun h => Finset.disjoint_left.mp hB h (by simp)
  refine ⟨∑ r ∈ B.filter (· < k), b r, ∑ r ∈ B.filter (fun r => ¬ r < k), b r,
    (Finset.sum_filter_add_sum_filter_not B (· < k) b).symm, ?_,
    B.filter (fun r => ¬ r < k), ?_, rfl⟩
  · have hsub : insert i (B.filter (· < k)) ⊆ Finset.range k := by
      intro r hr
      rw [Finset.mem_insert] at hr
      rw [Finset.mem_range]
      rcases hr with rfl | hr
      · exact hik
      · exact (Finset.mem_filter.mp hr).2
    have hni : i ∉ B.filter (· < k) := fun h => hiB (Finset.mem_filter.mp h).1
    have := Finset.sum_le_sum_of_subset (f := b) hsub
    rw [Finset.sum_insert hni] at this
    omega
  · intro r hr
    obtain ⟨hrB, hrk⟩ := Finset.mem_filter.mp hr
    exact ⟨by omega, fun h => hjB (h ▸ hrB)⟩

-- N39
theorem gap_pair (b : ℕ → ℕ) (hb : Monotone b) (hpos : ∀ i, 0 < b i)
    (hcomp : IsAddCompleteNatSeq' b)
    (hmin : ∀ i, ¬ IsAddCompleteNatSeq' (Function.updateFinset b {i} 0))
    (T : ℕ) (hT1 : 1 ≤ T)
    (hcent : ∀ᶠ k in Filter.atTop, ∀ x, T ≤ x → x + T ≤ ∑ i ∈ Finset.range k, b i →
      ∃ B ⊆ Finset.range k, ∑ i ∈ B, b i = x) (C : ℕ) :
    ∃ i j, i ≠ j ∧ ∀ M, ∃ u, M ≤ u ∧ ∀ x, u ≤ x → x ≤ u + C →
      x ∉ subseqSums' (Function.updateFinset b {i, j} 0) := by
  have hunb := not_bddAbove_of_deletion_minimal b hb hcomp hmin
  rw [not_bddAbove_iff] at hunb
  obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hunb (2 * T + C)
  rw [Filter.eventually_atTop] at hcent
  obtain ⟨K, hK⟩ := hcent
  have hk2T : 2 * T ≤ ∑ r ∈ Finset.range (K + i + 1 + 2 * T), b r :=
    le_trans (by omega) (range_le_sum b hpos _)
  have hbi : b i ≤ ∑ r ∈ Finset.range (K + i + 1 + 2 * T), b r :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
  refine ⟨i, K + i + 1 + 2 * T, by omega, fun M => ?_⟩
  obtain ⟨q, hMq, hQq, hgap⟩ := tail_gaps b hpos T (K + i + 1 + 2 * T) hk2T
    (hK _ (by omega)) (K + i + 1 + 2 * T) le_rfl (hmin _) M
  refine ⟨q + (∑ r ∈ Finset.range (K + i + 1 + 2 * T), b r - b i) + 1, by omega,
    fun x hx1 hx2 hx => ?_⟩
  obtain ⟨f, y, hxy, hf, By, hBy, hBys⟩ :=
    pair_split b i (K + i + 1 + 2 * T) (K + i + 1 + 2 * T) (by omega) le_rfl x hx
  rcases hgap y ⟨By, hBy, hBys⟩ with h | h
  · omega
  · omega

-- N40
theorem positive_core_gap (b : ℕ → ℕ) (hb : Monotone b) (hpos : ∀ i, 0 < b i)
    (hcomp : IsAddCompleteNatSeq' b)
    (hmin : ∀ i, ¬ IsAddCompleteNatSeq' (Function.updateFinset b {i} 0)) (C : ℕ)
    (hdel : ∀ i, ∀ᶠ x in Filter.atTop,
      ∃ d ≤ C, ∃ y ∈ subseqSums' (Function.updateFinset b {i} 0), x = d + y) :
    ∃ i j, i ≠ j ∧ ∀ M, ∃ u, M ≤ u ∧ ∀ x, u ≤ x → x ≤ u + C →
      x ∉ subseqSums' (Function.updateFinset b {i, j} 0) := by
  obtain ⟨T, hT1, hT⟩ := (complete_iff_threshold b).mp hcomp
  have hδ := slack_tendsto b hb hpos C hdel
  exact gap_pair b hb hpos hcomp hmin T hT1 (central_interval b hb hpos T hT1 hT hδ) C

-- N41
theorem exists_enum_compl (D : Finset ℕ) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ Set.range e = {i | i ∉ D} := by
  have hinf : (Set.ofPred fun i => i ∉ D).Infinite := by
    have h := (D.finite_toSet).infinite_compl
    exact h
  exact ⟨Nat.nth (fun i => i ∉ D), Nat.nth_strictMono hinf, Nat.range_nth_of_infinite hinf⟩

-- N42
theorem subseqSums'_reindex (a : ℕ → ℕ) (D : Finset ℕ) (e : ℕ → ℕ) (he : StrictMono e)
    (hr : Set.range e = {i | i ∉ D}) (E : Finset ℕ) :
    subseqSums' (Function.updateFinset (fun k => a (e k)) E 0) =
      subseqSums' (Function.updateFinset a (D ∪ E.image e) 0) := by
  classical
  ext x
  rw [mem_subseqSums'_updateFinset, mem_subseqSums'_updateFinset]
  have hinj := he.injective
  constructor
  · rintro ⟨B, hB, hx⟩
    refine ⟨B.image e, ?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro i hi hi2
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hi
      rcases Finset.mem_union.mp hi2 with h | h
      · have : e k ∈ Set.range e := ⟨k, rfl⟩
        rw [hr] at this
        exact this h
      · obtain ⟨k', hk', hkk⟩ := Finset.mem_image.mp h
        have := hinj hkk
        subst this
        exact Finset.disjoint_left.mp hB hk hk'
    · rw [Finset.sum_image (fun x _ y _ h => hinj h)]
      exact hx
  · rintro ⟨B', hB', hx⟩
    have hBr : ∀ i ∈ B', i ∈ Set.range e := by
      intro i hi
      rw [hr]
      exact fun h => Finset.disjoint_left.mp hB' hi (Finset.mem_union_left _ h)
    refine ⟨B'.preimage e hinj.injOn, ?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro k hk hkE
      rw [Finset.mem_preimage] at hk
      exact Finset.disjoint_left.mp hB' hk
        (Finset.mem_union_right _ (Finset.mem_image_of_mem e hkE))
    · have h := Finset.sum_image (f := a) (s := B'.preimage e hinj.injOn) (g := e)
        (fun x _ y _ h => hinj h)
      rw [Finset.image_preimage, Finset.filter_true_of_mem hBr] at h
      rw [hx, h]

-- N43
theorem complete_of_pairs (a : ℕ → ℕ)
    (h2 : ∀ s : Finset ℕ, s.card = 2 → IsAddCompleteNatSeq' (Function.updateFinset a s 0))
    (D : Finset ℕ) (hD : D.card ≤ 2) :
    IsAddCompleteNatSeq' (Function.updateFinset a D 0) := by
  obtain ⟨s, hDs, hs⟩ := Infinite.exists_superset_card_eq D 2 hD
  exact complete_updateFinset_anti a hDs (h2 s hs)

-- N44
theorem extend_deletion (a : ℕ → ℕ) (ha : Monotone a)
    (h2 : ∀ s : Finset ℕ, s.card = 2 → IsAddCompleteNatSeq' (Function.updateFinset a s 0))
    (D : Finset ℕ) (hD : IsAddCompleteNatSeq' (Function.updateFinset a D 0)) :
    ∃ i, i ∉ D ∧ IsAddCompleteNatSeq' (Function.updateFinset a (insert i D) 0) := by
  obtain ⟨e, he, hr⟩ := exists_enum_compl D
  have heD : ∀ k, e k ∉ D := by
    intro k
    have : e k ∈ Set.range e := ⟨k, rfl⟩
    rw [hr] at this
    exact this
  by_contra hcon
  push Not at hcon
  have hpos : ∀ k, 0 < a (e k) := by
    intro k
    by_contra h0
    push Not at h0
    apply hcon (e k) (heD k)
    rw [updateFinset_insert_of_eq_zero a D (e k) (by omega)]
    exact hD
  have hbmono : Monotone (fun k => a (e k)) := ha.comp he.monotone
  have hre : ∀ E : Finset ℕ, subseqSums' (Function.updateFinset (fun k => a (e k)) E 0) =
      subseqSums' (Function.updateFinset a (D ∪ E.image e) 0) :=
    fun E => subseqSums'_reindex a D e he hr E
  have hbcomp : IsAddCompleteNatSeq' (fun k => a (e k)) := by
    have h := hre ∅
    rw [Function.updateFinset_empty, Finset.image_empty, Finset.union_empty] at h
    unfold IsAddCompleteNatSeq' at hD ⊢
    rw [h]
    exact hD
  have hbmin : ∀ i, ¬ IsAddCompleteNatSeq' (Function.updateFinset (fun k => a (e k)) {i} 0) := by
    intro i hc
    apply hcon (e i) (heD i)
    unfold IsAddCompleteNatSeq' at hc ⊢
    rw [hre {i}, Finset.image_singleton, Finset.union_comm, ← Finset.insert_eq] at hc
    exact hc
  have hdel : ∀ i, ∀ᶠ x in Filter.atTop, ∃ d ≤ ∑ k ∈ D, a k,
      ∃ y ∈ subseqSums' (Function.updateFinset (fun k => a (e k)) {i} 0), x = d + y := by
    intro i
    have hc1 := complete_of_pairs a h2 {e i} (by simp)
    unfold IsAddCompleteNatSeq' at hc1
    refine hc1.mono fun x hx => ?_
    obtain ⟨d, hd, y, hy, hxy⟩ := restore_deleted a D {e i} x hx
    refine ⟨d, hd, y, ?_, hxy⟩
    rw [hre {i}, Finset.image_singleton]
    exact hy
  obtain ⟨i, j, hij, hgap⟩ := positive_core_gap _ hbmono hpos hbcomp hbmin _ hdel
  have hc2 := h2 {e i, e j} (Finset.card_pair (fun h => hij (he.injective h)))
  apply not_complete_of_long_gaps
    (subseqSums' (Function.updateFinset (fun k => a (e k)) {i, j} 0)) (∑ k ∈ D, a k) hgap
  unfold IsAddCompleteNatSeq' at hc2
  refine hc2.mono fun x hx => ?_
  obtain ⟨d, hd, y, hy, hxy⟩ := restore_deleted a D {e i, e j} x hx
  refine ⟨d, hd, y, ?_, hxy⟩
  rw [hre {i, j}, Finset.image_insert, Finset.image_singleton]
  exact hy

-- N45
theorem exists_complete_deletion (a : ℕ → ℕ) (ha : Monotone a)
    (h2 : ∀ s : Finset ℕ, s.card = 2 → IsAddCompleteNatSeq' (Function.updateFinset a s 0))
    (r : ℕ) : ∃ D : Finset ℕ, D.card = r ∧ IsAddCompleteNatSeq' (Function.updateFinset a D 0) := by
  induction r with
  | zero => exact ⟨∅, Finset.card_empty, complete_of_pairs a h2 ∅ (by simp)⟩
  | succ r ih =>
    obtain ⟨D, hDc, hD⟩ := ih
    obtain ⟨i, hi, hc⟩ := extend_deletion a ha h2 D hD
    exact ⟨insert i D, by rw [Finset.card_insert_of_notMem hi, hDc], hc⟩

-- N46
theorem exclusion_of_two_le (m n : ℕ) (hm : 2 ≤ m) (a : ℕ → ℕ) (ha : Monotone a)
    (hs : ∀ s : Finset ℕ, s.card = m → IsAddCompleteNatSeq' (Function.updateFinset a s 0)) :
    ∃ t : Finset ℕ, t.card = n ∧ IsAddCompleteNatSeq' (Function.updateFinset a t 0) := by
  have h2 : ∀ s : Finset ℕ, s.card = 2 → IsAddCompleteNatSeq' (Function.updateFinset a s 0) := by
    intro s hs2
    obtain ⟨u, hsu, hu⟩ := Infinite.exists_superset_card_eq s m (by omega)
    exact complete_updateFinset_anti a hsu (hs u hu)
  exact exists_complete_deletion a ha h2 n

/--
For what values of $0 \leq m < n$ is there a complete sequence
$A = \{a_1 \leq a_2 \leq \cdots\}$ of integers such that
 1. $A$ remains complete after removing any $m$ elements, but
 2. $A$ is not complete after removing any $n$ elements.

Geneson [Ge26, Theorem 1] proved that the pairs are exactly those with $m \leq 1$.
Completeness allows finitely many exceptions, and deletions remove indexed occurrences.
-/
theorem erdos_348 :
    { (m, n) | (m) (n) (_ : m < n) (a : ℕ → ℕ) (_ : Monotone a)
      (_ : ∀ s, s.card = m → IsAddCompleteNatSeq' (Function.updateFinset a s 0))
        (_ : ∀ t, t.card = n → ¬IsAddCompleteNatSeq' (Function.updateFinset a t 0)) } =
    erdos_348.answer := by
  ext ⟨m, n⟩
  constructor
  · rintro ⟨m', n', hmn, a, ha, hs, ht, heq⟩
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    refine ⟨hmn, ?_⟩
    by_contra hm
    push Not at hm
    obtain ⟨t, htc, htcomp⟩ := exclusion_of_two_le m' n' hm a ha hs
    exact ht t htc htcomp
  · rintro ⟨hmn, hm⟩
    have hw : ∃ a : ℕ → ℕ, Monotone a ∧
        (∀ s : Finset ℕ, s.card = m → IsAddCompleteNatSeq' (Function.updateFinset a s 0)) ∧
        ∀ t : Finset ℕ, t.card = n → ¬ IsAddCompleteNatSeq' (Function.updateFinset a t 0) := by
      interval_cases m
      · exact exists_witness_zero n hmn
      · exact exists_witness_one n hmn
    obtain ⟨a, ha, hs, ht⟩ := hw
    exact ⟨m, n, hmn, a, ha, hs, ht, rfl⟩

end Erdos348
