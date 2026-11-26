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

namespace Erdos569

open SimpleGraph

/-- A Ramsey upper bound follows from the pointwise statement on `Fin n`. -/
theorem graphRamsey_le_of_forall {α β : Type*} [Fintype α] [Fintype β]
    (G : SimpleGraph α) (H : SimpleGraph β) (n : ℕ)
    (h : ∀ C : SimpleGraph (Fin n), G.IsContained C ∨ H.IsContained Cᶜ) :
    graphRamsey G H ≤ n :=
  Nat.sInf_le h

/-- A graph with no isolated vertices and no edges has no vertices at all. -/
theorem isEmpty_of_ncard_edgeSet_eq_zero {W : Type} [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (h0 : ∀ v, 0 < H.degree v) (hm : H.edgeSet.ncard = 0) : IsEmpty W := by
  have hbot : H = ⊥ := edgeSet_eq_empty.mp ((Set.ncard_eq_zero).mp hm)
  refine ⟨fun v => ?_⟩
  obtain ⟨w, hw⟩ := (H.degree_pos_iff_exists_adj v).mp (h0 v)
  rw [hbot] at hw
  exact hw

/-- The cycle on `k` vertices sits inside the complete graph on `n ≥ k` vertices. -/
theorem cycleGraph_isContained_top {k n : ℕ} (hkn : k ≤ n) :
    (cycleGraph k).IsContained (⊤ : SimpleGraph (Fin n)) :=
  isContained_top_iff.mpr ⟨Fin.castLEEmb hkn⟩

/-- A graph with exactly one edge and no isolated vertices is a single edge, so it is contained in any
graph having an edge. -/
theorem isContained_of_ncard_edgeSet_eq_one {W V : Type*} [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (h0 : ∀ v, 0 < H.degree v) (hm : H.edgeSet.ncard = 1)
    (G : SimpleGraph V) (a b : V) (hab : G.Adj a b) : H.IsContained G := by
  classical
  obtain ⟨e, he⟩ := Set.ncard_eq_one.mp hm
  induction e using Sym2.ind with
  | _ u v =>
  have huv' : s(u, v) ∈ H.edgeSet := by rw [he]; exact Set.mem_singleton _
  have huv : H.Adj u v := (mem_edgeSet H).mp huv'
  have hne : u ≠ v := huv.ne
  have hne' : v ≠ u := hne.symm
  -- every vertex is an endpoint of the unique edge
  have hmem : ∀ w, w = u ∨ w = v := by
    intro w
    obtain ⟨x, hx⟩ := (H.degree_pos_iff_exists_adj w).mp (h0 w)
    have hwx : s(w, x) ∈ H.edgeSet := (mem_edgeSet H).mpr hx
    rw [he, Set.mem_singleton_iff, Sym2.eq_iff] at hwx
    rcases hwx with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact Or.inl h1
    · exact Or.inr h1
  refine ⟨⟨⟨fun w => if w = u then a else b, ?_⟩, ?_⟩⟩
  · intro w w' hww'
    have hwx : s(w, w') ∈ H.edgeSet := (mem_edgeSet H).mpr hww'
    rw [he, Set.mem_singleton_iff, Sym2.eq_iff] at hwx
    rcases hwx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simpa [hne'] using hab
    · simpa [hne'] using hab.symm
  · intro w w' h
    rcases hmem w with hw | hw <;> rcases hmem w' with hw' | hw' <;> rw [hw, hw'] at h ⊢ <;>
      simp [hne', hab.ne, hab.ne.symm] at h

/-- The case `m = 1` of the core: `H` is a single edge, and `n ≥ k` vertices suffice. -/
theorem core_one (k n : ℕ) (hkn : k ≤ n) (W : Type) [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (h0 : ∀ v, 0 < H.degree v) (hm : H.edgeSet.ncard = 1)
    (C : SimpleGraph (Fin n)) : (cycleGraph k).IsContained C ∨ H.IsContained Cᶜ := by
  by_cases hC : Cᶜ = ⊥
  · left
    rw [compl_eq_bot.mp hC]
    exact cycleGraph_isContained_top hkn
  · right
    obtain ⟨a, b, hab⟩ := ne_bot_iff_exists_adj.mp hC
    exact isContained_of_ncard_edgeSet_eq_one H h0 hm Cᶜ a b hab

/-! ### Two embedding tools for a vertex-by-vertex construction of a blue copy of `H`

These are the generic steps any inductive proof of the core would use: restricting a colouring to fewer
vertices, and extending a blue copy of `H - u` by a new vertex for `u`. They are proved here but are not yet
assembled into a proof of the open core, because the step that would drive them (finding the new vertex from
`C_k`-freeness of the red graph) is the content of the paper and is not available. -/

/-- A blue copy of `H` in the colouring restricted along an injection `e` is a blue copy of `H`. -/
theorem isContained_compl_of_comap {V V' W : Type*} (H : SimpleGraph W) (C : SimpleGraph V')
    (e : V ↪ V') (h : H.IsContained (C.comap e)ᶜ) : H.IsContained Cᶜ := by
  have hle : (C.comap e)ᶜ ≤ Cᶜ.comap e := by
    intro a b hab
    rw [compl_adj, comap_adj] at hab
    rw [comap_adj, compl_adj]
    exact ⟨fun h' => hab.1 (e.injective h'), hab.2⟩
  exact (h.mono_right hle).trans ⟨(Embedding.comap e Cᶜ).toCopy⟩

/-- Extending a copy of `H - u` by a vertex `x` adjacent to the images of the neighbours of `u`. -/
theorem isContained_of_extend {W V : Type*} [DecidableEq W] (H : SimpleGraph W) (u : W)
    (G : SimpleGraph V) (f : Copy (H.induce ({u}ᶜ : Set W)) G) (x : V) (hx : ∀ w, f w ≠ x)
    (hadj : ∀ w : ({u}ᶜ : Set W), H.Adj u w → G.Adj x (f w)) : H.IsContained G := by
  have hmem : ∀ w : W, w ≠ u → w ∈ ({u}ᶜ : Set W) := fun w hw => by simpa using hw
  refine ⟨⟨⟨fun w => if h : w = u then x else f ⟨w, hmem w h⟩, ?_⟩, ?_⟩⟩
  · intro a b hab
    by_cases ha : a = u <;> by_cases hb : b = u
    · subst ha hb
      exact (hab.ne rfl).elim
    · rw [dite_eq_left ha, dite_eq_right hb]
      subst ha
      exact hadj ⟨b, hmem b hb⟩ hab
    · rw [dite_eq_right ha, dite_eq_left hb]
      subst hb
      exact (hadj ⟨a, hmem a ha⟩ hab.symm).symm
    · rw [dite_eq_right ha, dite_eq_right hb]
      exact f.toHom.map_adj (induce_adj.mpr hab)
  · intro a b h
    simp only [RelHom.coeFn_mk] at h
    by_cases ha : a = u <;> by_cases hb : b = u
    · rw [ha, hb]
    · rw [dite_eq_left ha, dite_eq_right hb] at h
      exact (hx _ h.symm).elim
    · rw [dite_eq_right ha, dite_eq_left hb] at h
      exact (hx _ h).elim
    · rw [dite_eq_right ha, dite_eq_right hb] at h
      exact congrArg Subtype.val (f.injective h)

/-- A red clique on at least `k` vertices contains a red `C_k`. -/
theorem cycleGraph_isContained_of_isClique {V : Type*} [Fintype V] (C : SimpleGraph V) (s : Finset V)
    (hs : C.IsClique (s : Set V)) (k : ℕ) (hk : k ≤ s.card) : (cycleGraph k).IsContained C := by
  classical
  have htop : C.induce (s : Set V) = ⊤ := induce_eq_top.mpr hs
  have h1 : (cycleGraph k).IsContained (⊤ : SimpleGraph (s : Set V)) :=
    isContained_top_iff.mpr (Function.Embedding.nonempty_of_card_le (by simpa using hk))
  rw [← htop] at h1
  exact h1.trans ⟨(Embedding.comap (Function.Embedding.subtype _) C).toCopy⟩

/-- Greedy red clique: if every vertex has at most `Δ` blue neighbours (non-neighbours in `C`), then every
vertex set `s` contains a red clique `t` with `#s ≤ (Δ + 1) * #t`. -/
theorem exists_isClique_of_compl_degree_le {V : Type*} [Fintype V] [DecidableEq V] (C : SimpleGraph V)
    [DecidableRel C.Adj] (Δ : ℕ) (hΔ : ∀ v, Cᶜ.degree v ≤ Δ) (n : ℕ) :
    ∀ s : Finset V, s.card ≤ n → ∃ t ⊆ s, C.IsClique (t : Set V) ∧ s.card ≤ (Δ + 1) * t.card := by
  induction n with
  | zero =>
    intro s hs
    exact ⟨∅, Finset.empty_subset _, by simp, by rw [Finset.card_empty, Nat.mul_zero]; exact hs⟩
  | succ n ih =>
    intro s hs
    rcases s.eq_empty_or_nonempty with h | ⟨v, hv⟩
    · exact ⟨∅, Finset.empty_subset _, by simp, by rw [h, Finset.card_empty]; exact Nat.zero_le _⟩
    · set s' := s.filter (fun w => C.Adj v w) with hs'
      have hsub : s' ⊆ s := Finset.filter_subset _ _
      have hv' : v ∉ s' := by
        rw [hs', Finset.mem_filter]
        exact fun h => h.2.ne rfl
      have hdiff : s \ s' ⊆ insert v (Cᶜ.neighborFinset v) := by
        intro w hw
        rw [Finset.mem_sdiff] at hw
        rw [Finset.mem_insert, mem_neighborFinset, compl_adj]
        by_cases hwv : w = v
        · exact Or.inl hwv
        · refine Or.inr ⟨fun h => hwv h.symm, fun hadj => hw.2 ?_⟩
          rw [hs', Finset.mem_filter]
          exact ⟨hw.1, hadj⟩
      have h1 : (s \ s').card ≤ Δ + 1 := by
        calc (s \ s').card ≤ (insert v (Cᶜ.neighborFinset v)).card := Finset.card_le_card hdiff
          _ ≤ (Cᶜ.neighborFinset v).card + 1 := Finset.card_insert_le _ _
          _ = Cᶜ.degree v + 1 := by rw [card_neighborFinset_eq_degree]
          _ ≤ Δ + 1 := Nat.add_le_add_right (hΔ v) 1
      have h2 := Finset.card_sdiff_add_card_eq_card hsub
      have hs'n : s'.card ≤ n := by
        have : s'.card < s.card :=
          Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨v, hv, fun h => h.ne rfl⟩)
        omega
      obtain ⟨t, hts, ht, hcard'⟩ := ih s' hs'n
      have hvt : v ∉ t := fun h => hv' (hts h)
      refine ⟨insert v t, Finset.insert_subset hv (hts.trans hsub), ?_, ?_⟩
      · rw [Finset.coe_insert]
        refine ht.insert fun b hb _ => ?_
        have hb' := hts hb
        rw [hs', Finset.mem_filter] at hb'
        exact hb'.2
      · rw [Finset.card_insert_of_notMem hvt, Nat.mul_succ]
        omega

/-- A star `H` with centre `v₀` (every edge contains `v₀`) is contained in any graph having a vertex `x`
of degree at least `#(univ.erase v₀)`, the number of other vertices of `H`. -/
theorem star_isContained_of_le_degree {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V]
    [DecidableEq V] (H : SimpleGraph W) (v₀ : W) (hstar : ∀ a b, H.Adj a b → a = v₀ ∨ b = v₀)
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V)
    (hx : (Finset.univ.erase v₀).card ≤ G.degree x) : H.IsContained G := by
  have hcard : Fintype.card (Finset.univ.erase v₀) ≤ Fintype.card (G.neighborFinset x) := by
    rw [Fintype.card_coe, Fintype.card_coe, card_neighborFinset_eq_degree]
    exact hx
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  have key : ∃ fn : ({v₀}ᶜ : Set W) → V, Function.Injective fn ∧ ∀ w, G.Adj x (fn w) := by
    refine ⟨fun w => (e ⟨w.1, Finset.mem_erase.mpr ⟨w.2, Finset.mem_univ _⟩⟩).1, ?_, ?_⟩
    · intro a b h
      have h' := e.injective (Subtype.ext h)
      exact Subtype.ext (Subtype.mk.inj h')
    · intro w
      have h := (e ⟨w.1, Finset.mem_erase.mpr ⟨w.2, Finset.mem_univ _⟩⟩).2
      rwa [mem_neighborFinset] at h
  obtain ⟨fn, hinj, hfn⟩ := key
  refine isContained_of_extend H v₀ G ⟨⟨fn, ?_⟩, hinj⟩ x (fun w => (hfn w).ne.symm) (fun w _ => hfn w)
  intro a b hab
  exfalso
  rcases hstar a.1 b.1 hab with h | h
  · exact a.2 h
  · exact b.2 h

/-- The star case of the core: if every edge of `H` contains one vertex `v₀`, the bound holds. Either
some vertex has blue degree at least `#W - 1` (then the star embeds in blue), or all blue degrees are at
most `#W - 2 ≤ m - 1`, and the greedy lemma gives a red clique on `k` vertices. -/
theorem core_star (k : ℕ) (hk : 3 ≤ k) (m : ℕ) (W : Type) [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (h0 : ∀ v, 0 < H.degree v) (hm : H.edgeSet.ncard = m)
    (v₀ : W) (hstar : ∀ a b, H.Adj a b → a = v₀ ∨ b = v₀)
    (C : SimpleGraph (Fin ((k - 1) * m + 1))) :
    (cycleGraph k).IsContained C ∨ H.IsContained Cᶜ := by
  classical
  have hadj : ∀ w, w ≠ v₀ → H.Adj v₀ w := by
    intro w hw
    obtain ⟨z, hz⟩ := (H.degree_pos_iff_exists_adj w).mp (h0 w)
    rcases hstar w z hz with h | h
    · exact absurd h hw
    · rw [h] at hz
      exact hz.symm
  have htm : (Finset.univ.erase v₀).card ≤ m := by
    rw [← hm, ← Set.ncard_coe_finset]
    refine Set.ncard_le_ncard_of_injOn (fun w => s(v₀, w)) ?_ ?_
    · intro w hw
      rw [Finset.mem_coe, Finset.mem_erase] at hw
      exact (mem_edgeSet H).mpr (hadj w hw.1)
    · intro w hw w' hw' h
      rw [Finset.mem_coe, Finset.mem_erase] at hw hw'
      rcases Sym2.eq_iff.mp h with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact h2
      · exact absurd h1.symm hw'.1
  by_cases hdeg : ∃ x, (Finset.univ.erase v₀).card ≤ Cᶜ.degree x
  · obtain ⟨x, hx⟩ := hdeg
    exact Or.inr (star_isContained_of_le_degree H v₀ hstar Cᶜ x hx)
  · left
    push Not at hdeg
    set t := (Finset.univ.erase v₀).card with ht
    have ht1 : 1 ≤ t := by
      have := hdeg ⟨0, Nat.succ_pos _⟩
      omega
    have hΔ : ∀ x, Cᶜ.degree x ≤ t - 1 := fun x => by have := hdeg x; omega
    obtain ⟨T, -, hT, hcard⟩ :=
      exists_isClique_of_compl_degree_le C (t - 1) hΔ _ Finset.univ le_rfl
    refine cycleGraph_isContained_of_isClique C T hT k ?_
    rw [Finset.card_univ, Fintype.card_fin, Nat.sub_add_cancel ht1] at hcard
    by_contra hlt
    push Not at hlt
    have h3 : t * T.card ≤ m * (k - 1) := Nat.mul_le_mul htm (by omega)
    rw [Nat.mul_comm m] at h3
    omega

/-- If every vertex of the colouring on `(k - 1) * m + 1` vertices has blue degree at most `m - 1`
(with `m ≥ 1`), the greedy lemma gives a red clique on `k` vertices, hence a red `C_k`. This disposes of
every colouring except those with a vertex of blue degree at least `m`. -/
theorem cycleGraph_isContained_of_compl_degree_lt (k m : ℕ) (hm1 : 1 ≤ m)
    (C : SimpleGraph (Fin ((k - 1) * m + 1))) [DecidableRel C.Adj] (hdeg : ∀ x, Cᶜ.degree x < m) :
    (cycleGraph k).IsContained C := by
  classical
  have hΔ : ∀ x, Cᶜ.degree x ≤ m - 1 := fun x => by have := hdeg x; omega
  obtain ⟨T, -, hT, hcard⟩ :=
    exists_isClique_of_compl_degree_le C (m - 1) hΔ _ Finset.univ le_rfl
  refine cycleGraph_isContained_of_isClique C T hT k ?_
  rw [Finset.card_univ, Fintype.card_fin, Nat.sub_add_cancel hm1] at hcard
  by_contra hlt
  push Not at hlt
  have h3 : m * T.card ≤ m * (k - 1) := Nat.mul_le_mul_left m (by omega)
  rw [Nat.mul_comm m (k - 1)] at h3
  omega

/-- A graph with exactly two edges, no isolated vertices and not a star consists of two disjoint edges;
it is contained in any graph having two disjoint edges `pq`, `rt`. -/
theorem isContained_of_ncard_edgeSet_eq_two {W V : Type*} [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (h0 : ∀ v, 0 < H.degree v) (hm : H.edgeSet.ncard = 2)
    (hns : ¬ ∃ v₀, ∀ a b, H.Adj a b → a = v₀ ∨ b = v₀)
    (G : SimpleGraph V) (p q r t : V) (hpq : G.Adj p q) (hrt : G.Adj r t)
    (hpr : p ≠ r) (hpt : p ≠ t) (hqr : q ≠ r) (hqt : q ≠ t) : H.IsContained G := by
  classical
  obtain ⟨e₁, e₂, hne, he⟩ := Set.ncard_eq_two.mp hm
  induction e₁ using Sym2.ind with
  | _ a b =>
  induction e₂ using Sym2.ind with
  | _ c d =>
  have hedge : ∀ x y, H.Adj x y →
      (x = a ∧ y = b ∨ x = b ∧ y = a) ∨ (x = c ∧ y = d ∨ x = d ∧ y = c) := by
    intro x y hxy
    have hx : s(x, y) ∈ H.edgeSet := (mem_edgeSet H).mpr hxy
    rw [he, Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.eq_iff, Sym2.eq_iff] at hx
    exact hx
  have hab : H.Adj a b := (mem_edgeSet H).mp (by rw [he]; exact Set.mem_insert _ _)
  have hcd : H.Adj c d :=
    (mem_edgeSet H).mp (by rw [he]; exact Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hmem : ∀ w, w = a ∨ w = b ∨ w = c ∨ w = d := by
    intro w
    obtain ⟨z, hz⟩ := (H.degree_pos_iff_exists_adj w).mp (h0 w)
    rcases hedge w z hz with (⟨h1, _⟩ | ⟨h1, _⟩) | (⟨h1, _⟩ | ⟨h1, _⟩)
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inr (Or.inr h1))
  have hnotstar : ∀ v, (∀ x y, H.Adj x y → x = v ∨ y = v) → False := fun v h => hns ⟨v, h⟩
  have hac : a ≠ c := by
    intro heq
    apply hnotstar a
    intro x y hxy
    rcases hedge x y hxy with (⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
      first
      | exact Or.inl h1
      | exact Or.inr h2
      | exact Or.inl (h1.trans heq.symm)
      | exact Or.inr (h2.trans heq.symm)
  have had : a ≠ d := by
    intro heq
    apply hnotstar a
    intro x y hxy
    rcases hedge x y hxy with (⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
      first
      | exact Or.inl h1
      | exact Or.inr h2
      | exact Or.inl (h1.trans heq.symm)
      | exact Or.inr (h2.trans heq.symm)
  have hbc : b ≠ c := by
    intro heq
    apply hnotstar b
    intro x y hxy
    rcases hedge x y hxy with (⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
      first
      | exact Or.inl h1
      | exact Or.inr h2
      | exact Or.inl (h1.trans heq.symm)
      | exact Or.inr (h2.trans heq.symm)
  have hbd : b ≠ d := by
    intro heq
    apply hnotstar b
    intro x y hxy
    rcases hedge x y hxy with (⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
      first
      | exact Or.inl h1
      | exact Or.inr h2
      | exact Or.inl (h1.trans heq.symm)
      | exact Or.inr (h2.trans heq.symm)
  have hba : b ≠ a := hab.ne.symm
  have hca : c ≠ a := hac.symm
  have hcb : c ≠ b := hbc.symm
  have hda : d ≠ a := had.symm
  have hdb : d ≠ b := hbd.symm
  have hdc : d ≠ c := hcd.ne.symm
  refine ⟨⟨⟨fun w => if w = a then p else if w = b then q else if w = c then r else t, ?_⟩, ?_⟩⟩
  · intro x y hxy
    rcases hedge x y hxy with (⟨hx, hy⟩ | ⟨hx, hy⟩) | (⟨hx, hy⟩ | ⟨hx, hy⟩) <;> rw [hx, hy] <;>
      simp [hba, hca, hcb, hda, hdb, hdc, hpq, hpq.symm, hrt, hrt.symm]
  · intro x y h
    simp only [RelHom.coeFn_mk] at h
    rcases hmem x with hx | hx | hx | hx <;> rcases hmem y with hy | hy | hy | hy <;>
      rw [hx, hy] at h ⊢ <;>
      simp [hba, hca, hcb, hda, hdb, hdc, hpq.ne, hpq.ne.symm, hrt.ne, hrt.ne.symm, hpr, hpr.symm,
        hpt, hpt.symm, hqr, hqr.symm, hqt, hqt.symm] at h

/-- The case `m = 2`, `H` not a star (so `H` is two disjoint edges): either blue has two disjoint edges,
or every two blue edges meet, and then deleting the ends of one blue edge leaves a red clique on
`2k - 3 ≥ k` vertices. -/
theorem core_two_nonstar (k : ℕ) (hk : 3 ≤ k) (W : Type) [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (h0 : ∀ v, 0 < H.degree v) (hm : H.edgeSet.ncard = 2)
    (hns : ¬ ∃ v₀, ∀ a b, H.Adj a b → a = v₀ ∨ b = v₀)
    (C : SimpleGraph (Fin ((k - 1) * 2 + 1))) :
    (cycleGraph k).IsContained C ∨ H.IsContained Cᶜ := by
  classical
  by_cases hD : ∃ p q r t : Fin ((k - 1) * 2 + 1),
      Cᶜ.Adj p q ∧ Cᶜ.Adj r t ∧ p ≠ r ∧ p ≠ t ∧ q ≠ r ∧ q ≠ t
  · obtain ⟨p, q, r, t, hpq, hrt, hpr, hpt, hqr, hqt⟩ := hD
    exact Or.inr (isContained_of_ncard_edgeSet_eq_two H h0 hm hns Cᶜ p q r t hpq hrt hpr hpt hqr hqt)
  · left
    push Not at hD
    by_cases hC : Cᶜ = ⊥
    · rw [compl_eq_bot.mp hC]
      exact cycleGraph_isContained_top (by omega)
    · obtain ⟨q, r, hqr⟩ := ne_bot_iff_exists_adj.mp hC
      refine cycleGraph_isContained_of_isClique C ((Finset.univ.erase q).erase r) ?_ k ?_
      · intro y hy z hz hyz
        rw [Finset.mem_coe, Finset.mem_erase, Finset.mem_erase] at hy hz
        by_contra hred
        have hblue : Cᶜ.Adj y z := by
          rw [compl_adj]
          exact ⟨hyz, hred⟩
        exact hz.1 (hD q r y z hqr hblue hy.2.1.symm hz.2.1.symm hy.1.symm).symm
      · rw [Finset.card_erase_of_mem, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
          Fintype.card_fin]
        · omega
        · exact Finset.mem_erase.mpr ⟨hqr.ne.symm, Finset.mem_univ _⟩

/-! ### Infrastructure for an inductive proof of the core (added in arm B5_C108) -/

/-- Monotonicity in the number of vertices: a pointwise Ramsey statement on `Fin n` gives one on `Fin n'` for
`n ≤ n'`, by restricting the colouring to the first `n` vertices. -/
theorem core_mono {α : Type*} [Fintype α] (G : SimpleGraph α) {W : Type*} (H : SimpleGraph W) {n n' : ℕ}
    (hnn : n ≤ n') (h : ∀ C : SimpleGraph (Fin n), G.IsContained C ∨ H.IsContained Cᶜ)
    (C : SimpleGraph (Fin n')) : G.IsContained C ∨ H.IsContained Cᶜ := by
  rcases h (C.comap (Fin.castLEEmb hnn)) with h1 | h1
  · exact Or.inl (h1.trans ⟨(Embedding.comap (Fin.castLEEmb hnn) C).toCopy⟩)
  · exact Or.inr (isContained_compl_of_comap H C _ h1)

/-- Restriction of a colouring along any injection `e : Fin n ↪ V`: a red `G` or blue `H` in the restricted
colouring gives one in the original. -/
theorem core_comap {α : Type*} [Fintype α] (G : SimpleGraph α) {W V : Type*} (H : SimpleGraph W) {n : ℕ}
    (h : ∀ C : SimpleGraph (Fin n), G.IsContained C ∨ H.IsContained Cᶜ)
    (C : SimpleGraph V) (e : Fin n ↪ V) : G.IsContained C ∨ H.IsContained Cᶜ := by
  rcases h (C.comap e) with h1 | h1
  · exact Or.inl (h1.trans ⟨(Embedding.comap e C).toCopy⟩)
  · exact Or.inr (isContained_compl_of_comap H C _ h1)

/-- A blue copy of `H` found inside the restriction to the first `n` vertices, kept as a copy into `Cᶜ`
together with the information that its image lies in a given set. -/
theorem exists_embedding_into_finset {V : Type*} [DecidableEq V] (s : Finset V) (n : ℕ) (hn : n ≤ s.card) :
    ∃ e : Fin n ↪ V, ∀ i, e i ∈ s := by
  classical
  have h1 : Fintype.card (Fin n) ≤ Fintype.card s := by simpa using hn
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le h1
  exact ⟨e.trans (Function.Embedding.subtype _), fun i => (e i).2⟩

/-- The number of edges of `H - u` is the number of edges of `H` minus the degree of `u`. -/
theorem ncard_edgeSet_induce_compl_singleton {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (u : W) :
    (H.induce ({u}ᶜ : Set W)).edgeSet.ncard = H.edgeSet.ncard - H.degree u := by
  rw [← coe_edgeFinset, Set.ncard_coe_finset, ← coe_edgeFinset, Set.ncard_coe_finset,
    card_edgeFinset_induce_compl_singleton, card_edgeFinset_deleteIncidenceSet]

/-- A finite nonempty graph has a vertex of minimum degree. -/
theorem exists_min_degree {W : Type*} [Fintype W] [Nonempty W] (H : SimpleGraph W) [DecidableRel H.Adj] :
    ∃ u, ∀ w, H.degree u ≤ H.degree w := by
  obtain ⟨u, -, hu⟩ := Finset.exists_min_image Finset.univ (fun w => H.degree w) Finset.univ_nonempty
  exact ⟨u, fun w => hu w (Finset.mem_univ w)⟩

/-- A finite nonempty graph has a vertex of maximum degree. -/
theorem exists_max_degree {W : Type*} [Fintype W] [Nonempty W] (H : SimpleGraph W) [DecidableRel H.Adj] :
    ∃ u, ∀ w, H.degree w ≤ H.degree u := by
  obtain ⟨u, -, hu⟩ := Finset.exists_max_image Finset.univ (fun w => H.degree w) Finset.univ_nonempty
  exact ⟨u, fun w => hu w (Finset.mem_univ w)⟩

/-- The degree of a vertex `w ≠ u` in `H - u` is its degree in `H` minus one if `w ~ u`, else unchanged. -/
theorem degree_induce_compl_singleton {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (u : W) (w : ({u}ᶜ : Set W)) :
    (H.induce ({u}ᶜ : Set W)).degree w + (if H.Adj u w then 1 else 0) = H.degree w := by
  classical
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  have hmap := map_neighborFinset_induce (G := H) (s := ({u}ᶜ : Set W)) w
  have hcard : ((H.induce ({u}ᶜ : Set W)).neighborFinset w).card =
      (H.neighborFinset w ∩ ({u}ᶜ : Set W).toFinset).card := by
    rw [← hmap, Finset.card_map]
  have hsplit : H.neighborFinset w = (H.neighborFinset w ∩ ({u}ᶜ : Set W).toFinset) ∪
      (H.neighborFinset w).filter (· = u) := by
    ext z
    simp only [Finset.mem_union, Finset.mem_inter, Set.mem_toFinset, Set.mem_compl_iff,
      Set.mem_singleton_iff, Finset.mem_filter]
    tauto
  have hdisj : Disjoint (H.neighborFinset w ∩ ({u}ᶜ : Set W).toFinset)
      ((H.neighborFinset w).filter (· = u)) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    simp only [Finset.mem_inter, Set.mem_toFinset, Set.mem_compl_iff, Set.mem_singleton_iff] at hz
    simp only [Finset.mem_filter] at hz'
    exact hz.2 hz'.2
  have h2 := congrArg Finset.card hsplit
  rw [Finset.card_union_of_disjoint hdisj] at h2
  have hfilt : ((H.neighborFinset w).filter (· = u)).card = if H.Adj u w then 1 else 0 := by
    split_ifs with h
    · rw [Finset.card_eq_one]
      refine ⟨u, ?_⟩
      ext z
      simp only [Finset.mem_filter, mem_neighborFinset, Finset.mem_singleton]
      constructor
      · exact fun hz => hz.2
      · intro hz
        subst hz
        exact ⟨h.symm, rfl⟩
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro z hz hzu
      subst hzu
      exact h ((mem_neighborFinset _ _ _).mp hz).symm
  rw [hcard, h2, hfilt]

/-- If every neighbour of `u` has degree at least two, `H - u` has no isolated vertices. -/
theorem degree_pos_induce_compl_singleton {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (h0 : ∀ v, 0 < H.degree v) (u : W) (hu : ∀ w, H.Adj u w → 2 ≤ H.degree w)
    (w : ({u}ᶜ : Set W)) : 0 < (H.induce ({u}ᶜ : Set W)).degree w := by
  have h := degree_induce_compl_singleton H u w
  by_cases hadj : H.Adj u w
  · have := hu w hadj
    rw [ite_eq_left hadj] at h
    omega
  · have := h0 w
    rw [ite_eq_right hadj] at h
    omega

/-- A graph with at least one edge has a vertex. -/
theorem nonempty_of_ncard_edgeSet_pos {W : Type*} (H : SimpleGraph W) (h : 0 < H.edgeSet.ncard) : Nonempty W := by
  by_contra hW
  rw [not_nonempty_iff] at hW
  have : H.edgeSet = ∅ := by
    ext e
    induction e using Sym2.ind with
    | _ a b => exact ⟨fun _ => (IsEmpty.false a).elim, fun h => h.elim⟩
  rw [this, Set.ncard_empty] at h
  omega

/-- In a graph with `m` edges that is not a star, every vertex has degree less than `m`. -/
theorem degree_lt_ncard_of_not_star {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (m : ℕ) (hm : H.edgeSet.ncard = m)
    (hns : ¬ ∃ v₀, ∀ a b, H.Adj a b → a = v₀ ∨ b = v₀) (v : W) : H.degree v < m := by
  have hcard : H.edgeFinset.card = m := by rw [← hm, ← coe_edgeFinset, Set.ncard_coe_finset]
  have hle : H.degree v ≤ m := by
    rw [← hcard, ← card_incidenceFinset_eq_degree]
    exact Finset.card_le_card (H.incidenceFinset_subset v)
  refine lt_of_le_of_ne hle fun heq => hns ⟨v, fun a b hab => ?_⟩
  have hsub : H.incidenceFinset v = H.edgeFinset := by
    apply Finset.eq_of_subset_of_card_le (H.incidenceFinset_subset v)
    rw [card_incidenceFinset_eq_degree, heq, hcard]
  have hab' : s(a, b) ∈ H.incidenceFinset v := by
    rw [hsub, mem_edgeFinset]
    exact hab
  rw [mem_incidenceFinset, mk'_mem_incidenceSet_iff] at hab'
  rcases hab'.2 with h | h
  · exact Or.inl h.symm
  · exact Or.inr h.symm

/-- **Large-degree step.** Let `v` be a vertex of `H` all of whose neighbours have degree at least two, so that
`H - v` has `m - deg v` edges and no isolated vertices. If the pointwise Ramsey statement holds for `H - v` on
`(k-1)(m - deg v) + 1` vertices, and some vertex `x` has blue degree at least that, then the colouring has a red
`C_k` or a blue `H`: embed `H - v` in the blue neighbourhood of `x` and send `v` to `x`. -/
theorem step_large_degree (k m : ℕ) (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (v : W)
    (ih : ∀ C' : SimpleGraph (Fin ((k - 1) * (m - H.degree v) + 1)),
      (cycleGraph k).IsContained C' ∨ (H.induce ({v}ᶜ : Set W)).IsContained C'ᶜ)
    {n : ℕ} (C : SimpleGraph (Fin n)) [DecidableRel C.Adj] (x : Fin n)
    (hx : (k - 1) * (m - H.degree v) + 1 ≤ Cᶜ.degree x) :
    (cycleGraph k).IsContained C ∨ H.IsContained Cᶜ := by
  classical
  have hroom : (k - 1) * (m - H.degree v) + 1 ≤ (Cᶜ.neighborFinset x).card := by
    rw [card_neighborFinset_eq_degree]; exact hx
  obtain ⟨e, he⟩ := exists_embedding_into_finset (Cᶜ.neighborFinset x) _ hroom
  rcases ih (C.comap e) with h1 | h1
  · exact Or.inl (h1.trans ⟨(Embedding.comap e C).toCopy⟩)
  · right
    obtain ⟨f⟩ := h1
    have hle : (C.comap e)ᶜ ≤ Cᶜ.comap e := by
      intro a b hab
      rw [compl_adj, comap_adj] at hab
      rw [comap_adj, compl_adj]
      exact ⟨fun h' => hab.1 (e.injective h'), hab.2⟩
    let g : Copy (H.induce ({v}ᶜ : Set W)) Cᶜ :=
      (Embedding.comap e Cᶜ).toCopy.comp ((Copy.ofLE _ _ hle).comp f)
    have hg : ∀ w, g w = e (f w) := fun w => rfl
    have hblue : ∀ w, Cᶜ.Adj x (g w) := by
      intro w
      rw [hg]
      exact (mem_neighborFinset _ _ _).mp (he (f w))
    exact isContained_of_extend H v Cᶜ g x (fun w h => (hblue w).ne h.symm) (fun w _ => hblue w)

/-- Extending a copy of `H - a - b`, where `ab` is an isolated edge of `H`, by a blue edge `xy` outside the copy. -/
theorem isContained_of_extend_edge {W V : Type*} [DecidableEq W] (H : SimpleGraph W) (a b : W)
    (hab : H.Adj a b) (ha : ∀ w, H.Adj a w → w = b) (hb : ∀ w, H.Adj b w → w = a)
    (G : SimpleGraph V) (f : Copy (H.induce ({a, b}ᶜ : Set W)) G) (x y : V) (hxy : G.Adj x y)
    (hx : ∀ w, f w ≠ x) (hy : ∀ w, f w ≠ y) : H.IsContained G := by
  have hmem : ∀ w : W, w ≠ a → w ≠ b → w ∈ ({a, b}ᶜ : Set W) := fun w h1 h2 => by
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨h1, h2⟩
  have hne : a ≠ b := hab.ne
  refine ⟨⟨⟨fun w => if h : w = a then x else if h' : w = b then y else f ⟨w, hmem w h h'⟩, ?_⟩, ?_⟩⟩
  · intro p q hpq
    by_cases hp : p = a <;> by_cases hq : q = a
    · subst hp hq; exact (hpq.ne rfl).elim
    · subst hp
      have : q = b := ha q hpq
      subst this
      simp only [dite_true, hne.symm, dite_false]
      exact hxy
    · subst hq
      have : p = b := ha p hpq.symm
      subst this
      simp only [dite_true, hne.symm, dite_false]
      exact hxy.symm
    · by_cases hp' : p = b <;> by_cases hq' : q = b
      · subst hp' hq'; exact (hpq.ne rfl).elim
      · subst hp'
        exact absurd (hb q hpq) hq
      · subst hq'
        exact absurd (hb p hpq.symm) hp
      · rw [dif_neg hp, dif_neg hp', dif_neg hq, dif_neg hq']
        exact f.toHom.map_adj (induce_adj.mpr hpq)
  · intro p q h
    simp only [RelHom.coeFn_mk] at h
    by_cases hp : p = a <;> by_cases hq : q = a
    · rw [hp, hq]
    · rw [dif_pos hp, dif_neg hq] at h
      by_cases hq' : q = b
      · rw [dif_pos hq'] at h
        exact (hxy.ne h).elim
      · rw [dif_neg hq'] at h
        exact (hx _ h.symm).elim
    · rw [dif_neg hp, dif_pos hq] at h
      by_cases hp' : p = b
      · rw [dif_pos hp'] at h
        exact (hxy.ne h.symm).elim
      · rw [dif_neg hp'] at h
        exact (hx _ h).elim
    · rw [dif_neg hp, dif_neg hq] at h
      by_cases hp' : p = b <;> by_cases hq' : q = b
      · rw [hp', hq']
      · rw [dif_pos hp', dif_neg hq'] at h
        exact (hy _ h.symm).elim
      · rw [dif_neg hp', dif_pos hq'] at h
        exact (hy _ h).elim
      · rw [dif_neg hp', dif_neg hq'] at h
        exact congrArg Subtype.val (f.injective h)

/-- Removing an isolated edge `ab` from `H` removes exactly one edge. -/
theorem ncard_edgeSet_induce_compl_pair {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (a b : W) (hab : H.Adj a b) (ha : ∀ w, H.Adj a w → w = b)
    (hb : ∀ w, H.Adj b w → w = a) :
    (H.induce ({a, b}ᶜ : Set W)).edgeSet.ncard = H.edgeSet.ncard - 1 := by
  classical
  have hsupp : (H.deleteEdges {s(a, b)}).support ⊆ ({a, b}ᶜ : Set W) := by
    intro w hw
    rw [mem_support] at hw
    obtain ⟨z, hz⟩ := hw
    rw [deleteEdges_adj, Set.mem_singleton_iff] at hz
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · rintro rfl
      exact hz.2 (by rw [ha z hz.1])
    · rintro rfl
      exact hz.2 (by rw [hb z hz.1, Sym2.eq_swap])
  have hind : (H.deleteEdges {s(a, b)}).induce ({a, b}ᶜ : Set W) = H.induce ({a, b}ᶜ : Set W) := by
    ext ⟨u, hu⟩ ⟨v, hv⟩
    simp only [comap_adj, Function.Embedding.coe_subtype, deleteEdges_adj, Set.mem_singleton_iff]
    constructor
    · exact fun h => h.1
    · intro h
      refine ⟨h, fun heq => ?_⟩
      rw [Sym2.eq_iff] at heq
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hu
      rcases heq with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact hu.1 h1
      · exact hu.2 h1
  have h1 := card_edgeFinset_induce_of_support_subset hsupp
  rw [hind] at h1
  have h2 : (H.deleteEdges {s(a, b)}).edgeSet.ncard = H.edgeSet.ncard - 1 := by
    rw [edgeSet_deleteEdges]
    exact Set.ncard_diff_singleton_of_mem ((mem_edgeSet H).mpr hab)
  rw [← coe_edgeFinset, Set.ncard_coe_finset, h1, ← Set.ncard_coe_finset, coe_edgeFinset, h2]

/-- Removing an isolated edge `ab` from a graph without isolated vertices leaves no isolated vertices. -/
theorem degree_pos_induce_compl_pair {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (h0 : ∀ v, 0 < H.degree v) (a b : W) (ha : ∀ w, H.Adj a w → w = b)
    (hb : ∀ w, H.Adj b w → w = a) (w : ({a, b}ᶜ : Set W)) : 0 < (H.induce ({a, b}ᶜ : Set W)).degree w := by
  classical
  have hw := w.2
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hw
  obtain ⟨z, hz⟩ := (H.degree_pos_iff_exists_adj w).mp (h0 w)
  have hza : z ≠ a := fun h => hw.2 (by subst h; exact ha _ hz.symm)
  have hzb : z ≠ b := fun h => hw.1 (by subst h; exact hb _ hz.symm)
  rw [degree_pos_iff_exists_adj]
  refine ⟨⟨z, ?_⟩, ?_⟩
  · simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hza, hzb⟩
  · exact induce_adj.mpr hz

/-- The complement of a pair in `Fin n` has `n - 2` elements. -/
theorem card_compl_pair {n : ℕ} (x y : Fin n) (hxy : x ≠ y) :
    (Finset.univ.filter (fun z : Fin n => z ≠ x ∧ z ≠ y)).card = n - 2 := by
  have : Finset.univ.filter (fun z : Fin n => z ≠ x ∧ z ≠ y) = (Finset.univ.erase x).erase y := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    tauto
  rw [this, Finset.card_erase_of_mem, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin]
  · omega
  · exact Finset.mem_erase.mpr ⟨hxy.symm, Finset.mem_univ _⟩

/-- **Isolated-edge step.** If `ab` is an isolated edge of `H` and the pointwise statement holds for `H - a - b`
on `(k-1)(m-1)+1` vertices, then it holds for `H` on `(k-1)m+1` vertices: take any blue edge `xy` (if blue
has no edge, red is complete) and embed `H - a - b` among the other vertices. -/
theorem step_isolated_edge (k : ℕ) (hk : 3 ≤ k) (m : ℕ) (hm1 : 1 ≤ m) (W : Type) [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (a b : W) (hab : H.Adj a b)
    (ha : ∀ w, H.Adj a w → w = b) (hb : ∀ w, H.Adj b w → w = a)
    (ih : ∀ C' : SimpleGraph (Fin ((k - 1) * (m - 1) + 1)),
      (cycleGraph k).IsContained C' ∨ (H.induce ({a, b}ᶜ : Set W)).IsContained C'ᶜ)
    (C : SimpleGraph (Fin ((k - 1) * m + 1))) [DecidableRel C.Adj] :
    (cycleGraph k).IsContained C ∨ H.IsContained Cᶜ := by
  classical
  by_cases hC : Cᶜ = ⊥
  · left
    rw [compl_eq_bot.mp hC]
    exact cycleGraph_isContained_top (by nlinarith)
  obtain ⟨x, y, hxy⟩ := ne_bot_iff_exists_adj.mp hC
  have hroom : (k - 1) * (m - 1) + 1 ≤ (Finset.univ.filter (fun z => z ≠ x ∧ z ≠ y)).card := by
    rw [card_compl_pair x y hxy.ne]
    have : (k - 1) * m = (k - 1) * (m - 1) + (k - 1) := by
      rw [← Nat.mul_succ, Nat.sub_add_cancel hm1]
    omega
  obtain ⟨e, he⟩ := exists_embedding_into_finset _ _ hroom
  rcases ih (C.comap e) with h1 | h1
  · exact Or.inl (h1.trans ⟨(Embedding.comap e C).toCopy⟩)
  · right
    obtain ⟨f⟩ := h1
    have hle : (C.comap e)ᶜ ≤ Cᶜ.comap e := by
      intro p q hpq
      rw [compl_adj, comap_adj] at hpq
      rw [comap_adj, compl_adj]
      exact ⟨fun h' => hpq.1 (e.injective h'), hpq.2⟩
    let g : Copy (H.induce ({a, b}ᶜ : Set W)) Cᶜ :=
      (Embedding.comap e Cᶜ).toCopy.comp ((Copy.ofLE _ _ hle).comp f)
    have hg : ∀ w, g w = e (f w) := fun w => rfl
    refine isContained_of_extend_edge H a b hab ha hb Cᶜ g x y hxy ?_ ?_
    · intro w
      rw [hg]
      have := he (f w)
      rw [Finset.mem_filter] at this
      exact this.2.1
    · intro w
      rw [hg]
      have := he (f w)
      rw [Finset.mem_filter] at this
      exact this.2.2


/-- The combinatorial core of Cambie–Freschi, Theorem 3, for `H` with at least three edges and not a star:
every 2-coloring of the complete graph on `(k - 1) * m + 1` vertices has a red `C_k` or a blue `H`.
This is the content of the paper; left open. By `cycleGraph_isContained_of_compl_degree_lt` one may
assume a vertex `x` of blue degree at least `m`. -/
theorem core_ge_three_nonstar (k : ℕ) (hk : 3 ≤ k) (m : ℕ) (hm3 : 3 ≤ m) (W : Type) [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (h0 : ∀ v, 0 < H.degree v) (hm : H.edgeSet.ncard = m)
    (hns : ¬ ∃ v₀, ∀ a b, H.Adj a b → a = v₀ ∨ b = v₀)
    (C : SimpleGraph (Fin ((k - 1) * m + 1))) [DecidableRel C.Adj] (hx : ∃ x, m ≤ Cᶜ.degree x) :
    (cycleGraph k).IsContained C ∨ H.IsContained Cᶜ := by
  classical
  -- Route C (attempts 3-): strong induction on the number of edges `m'`, generalising `H`. Small cases and stars
  -- are the proved lemmas; the step deletes a vertex `v` of maximum degree and uses `step_large_degree` when
  -- the blue neighbourhood of `x` is big enough. The remaining cases are the open content.
  suffices key : ∀ m', m' ≤ m → ∀ (W' : Type) [Fintype W'] (H' : SimpleGraph W') [DecidableRel H'.Adj],
      (∀ v, 0 < H'.degree v) → H'.edgeSet.ncard = m' → 1 ≤ m' →
      ∀ C' : SimpleGraph (Fin ((k - 1) * m' + 1)), (cycleGraph k).IsContained C' ∨ H'.IsContained C'ᶜ by
    exact key m le_rfl W H h0 hm (by omega) C
  intro m'
  induction m' using Nat.strong_induction_on with
  | _ m' ih =>
  intro hm'm W' _ H' _ h0' hm' hm1' C'
  by_cases hstar : ∃ v₀, ∀ a b, H'.Adj a b → a = v₀ ∨ b = v₀
  · obtain ⟨v₀, hv₀⟩ := hstar
    exact core_star k hk m' W' H' h0' hm' v₀ hv₀ C'
  rcases Nat.lt_or_ge m' 2 with h1 | h1
  · have : m' = 1 := by omega
    subst this
    exact core_one k _ (by omega) W' H' h0' hm' C'
  rcases Nat.lt_or_ge m' 3 with h2 | h2
  · have : m' = 2 := by omega
    subst this
    exact core_two_nonstar k hk W' H' h0' hm' hstar C'
  by_cases hx' : ∃ x, m' ≤ C'ᶜ.degree x
  swap
  · push Not at hx'
    exact Or.inl (cycleGraph_isContained_of_compl_degree_lt k m' (by omega) C' hx')
  obtain ⟨x, hx⟩ := hx'
  have hW' : Nonempty W' := nonempty_of_ncard_edgeSet_pos H' (by omega)
  -- an isolated edge of `H'`: the isolated-edge step
  by_cases hiso : ∃ a b, H'.Adj a b ∧ (∀ w, H'.Adj a w → w = b) ∧ (∀ w, H'.Adj b w → w = a)
  · obtain ⟨a, b, hab, ha, hb⟩ := hiso
    have hmab : (H'.induce ({a, b}ᶜ : Set W')).edgeSet.ncard = m' - 1 := by
      rw [ncard_edgeSet_induce_compl_pair H' a b hab ha hb, hm']
    exact step_isolated_edge k hk m' (by omega) W' H' a b hab ha hb
      (ih (m' - 1) (by omega) (by omega) _ _ (degree_pos_induce_compl_pair H' h0' a b ha hb) hmab (by omega)) C'
  obtain ⟨v, hv⟩ := exists_max_degree H'
  have hvlt : H'.degree v < m' := degree_lt_ncard_of_not_star H' m' hm' hstar v
  have hvpos : 0 < H'.degree v := h0' v
  by_cases hleaf : ∀ w, H'.Adj v w → 2 ≤ H'.degree w
  · have hmv : (H'.induce ({v}ᶜ : Set W')).edgeSet.ncard = m' - H'.degree v := by
      rw [ncard_edgeSet_induce_compl_singleton, hm']
    have ih' := ih (m' - H'.degree v) (by omega) (by omega) _ (H'.induce ({v}ᶜ : Set W'))
      (degree_pos_induce_compl_singleton H' h0' v hleaf) hmv (by omega)
    by_cases hroom : (k - 1) * (m' - H'.degree v) + 1 ≤ C'ᶜ.degree x
    · exact step_large_degree k m' W' H' v ih' C' x hroom
    · -- open: maximum degree too small for the blue neighbourhood of `x`
      exact absurd hroom (by omega)
  · -- open: `v` has a neighbour of degree one
    exact absurd hleaf (by omega)

/-- The combinatorial core for `H` with at least one edge. -/
theorem core (k : ℕ) (hk : 3 ≤ k) (m : ℕ) (hm1 : 1 ≤ m) (W : Type) [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (h0 : ∀ v, 0 < H.degree v) (hm : H.edgeSet.ncard = m)
    (C : SimpleGraph (Fin ((k - 1) * m + 1))) :
    (cycleGraph k).IsContained C ∨ H.IsContained Cᶜ := by
  classical
  rcases Nat.lt_or_ge m 2 with h | h
  · have hm1' : m = 1 := by omega
    subst hm1'
    exact core_one k ((k - 1) * 1 + 1) (by omega) W H h0 hm C
  · by_cases hstar : ∃ v₀, ∀ a b, H.Adj a b → a = v₀ ∨ b = v₀
    · obtain ⟨v₀, hv₀⟩ := hstar
      exact core_star k hk m W H h0 hm v₀ hv₀ C
    · rcases Nat.lt_or_ge m 3 with h2 | h2
      · have hm2 : m = 2 := by omega
        subst hm2
        exact core_two_nonstar k hk W H h0 hm hstar C
      · by_cases hx : ∃ x, m ≤ Cᶜ.degree x
        · exact core_ge_three_nonstar k hk m h2 W H h0 hm hstar C hx
        · push Not at hx
          exact Or.inl (cycleGraph_isContained_of_compl_degree_lt k m hm1 C hx)

/-!
Theorem 3 of Cambie and Freschi, "A general bound on R(C_k, H)", arXiv:2606.11174v1 (9 June 2026), which settles
Erdős Problem 569 (Erdős, Faudree, Rousseau and Schelp 1993; problem 34 in Chung–Graham): for every graph H with m
edges and no isolated vertices and every k ≥ 3, R(C_k, H) ≤ (k − 1)m + 1.

Stated here by the registrar of the rooms experiment on 2026-11-26 in the definitions of
FormalConjectures/ErdosProblems/569.lean (the quantification over `m`, `W`, `H`, the no-isolated-vertex condition
`∀ v, 0 < H.degree v` and `H.edgeSet.ncard = m` are that file's), with the cycle of length `k` as
`SimpleGraph.cycleGraph k`. Nobody else has read this statement against the paper.
-/

/-- **Cambie–Freschi (2026), Theorem 3.** For every `k ≥ 3` and every graph `H` with `m` edges and no isolated
vertices, `R(C_k, H) ≤ (k - 1) * m + 1`. -/
theorem cambie_freschi (k : ℕ) (hk : 3 ≤ k) (m : ℕ) (W : Type) [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (h0 : ∀ v, 0 < H.degree v) (hm : H.edgeSet.ncard = m) :
    SimpleGraph.graphRamsey (SimpleGraph.cycleGraph k) H ≤ (k - 1) * m + 1 := by
  apply graphRamsey_le_of_forall
  intro C
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h
    have := isEmpty_of_ncard_edgeSet_eq_zero H h0 hm
    exact Or.inr IsContained.of_isEmpty
  · exact core k hk m h W H h0 hm C

end Erdos569
