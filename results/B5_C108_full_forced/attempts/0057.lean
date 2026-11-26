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
      · rw [dite_eq_right hp, dite_eq_right hp', dite_eq_right hq, dite_eq_right hq']
        exact f.toHom.map_adj (induce_adj.mpr hpq)
  · intro p q h
    simp only [RelHom.coeFn_mk] at h
    by_cases hp : p = a <;> by_cases hq : q = a
    · rw [hp, hq]
    · rw [dite_eq_left hp, dite_eq_right hq] at h
      by_cases hq' : q = b
      · rw [dite_eq_left hq'] at h
        exact (hxy.ne h).elim
      · rw [dite_eq_right hq'] at h
        exact (hx _ h.symm).elim
    · rw [dite_eq_right hp, dite_eq_left hq] at h
      by_cases hp' : p = b
      · rw [dite_eq_left hp'] at h
        exact (hxy.ne h.symm).elim
      · rw [dite_eq_right hp'] at h
        exact (hx _ h).elim
    · rw [dite_eq_right hp, dite_eq_right hq] at h
      by_cases hp' : p = b <;> by_cases hq' : q = b
      · rw [hp', hq']
      · rw [dite_eq_left hp', dite_eq_right hq'] at h
        exact (hy _ h.symm).elim
      · rw [dite_eq_right hp', dite_eq_left hq'] at h
        exact (hy _ h).elim
      · rw [dite_eq_right hp', dite_eq_right hq'] at h
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
  have h1' : ((H.deleteEdges {s(a, b)}).induce ({a, b}ᶜ : Set W)).edgeSet.ncard =
      (H.deleteEdges {s(a, b)}).edgeSet.ncard := by
    rw [← coe_edgeFinset, Set.ncard_coe_finset, ← coe_edgeFinset, Set.ncard_coe_finset]
    exact h1
  rw [hind] at h1'
  have h2 : (H.deleteEdges {s(a, b)}).edgeSet.ncard = H.edgeSet.ncard - 1 := by
    rw [edgeSet_deleteEdges]
    exact Set.ncard_sdiff_singleton_of_mem ((mem_edgeSet H).mpr hab)
  rw [h1', h2]

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
    have : k - 1 ≤ (k - 1) * m := Nat.le_mul_of_pos_right _ hm1
    exact cycleGraph_isContained_top (by omega)
  obtain ⟨x, y, hxy⟩ := ne_bot_iff_exists_adj.mp hC
  have hroom : (k - 1) * (m - 1) + 1 ≤ (Finset.univ.filter (fun z => z ≠ x ∧ z ≠ y)).card := by
    rw [card_compl_pair x y hxy.ne]
    have : (k - 1) * m = (k - 1) * (m - 1) + (k - 1) := by
      rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hm1]
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

/-- The vertex set of `H` minus `v` and minus the degree-one neighbours of `v`. -/
abbrev leafFree {W : Type*} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj] (v : W) : Set W :=
  {w | w ≠ v ∧ ¬ (H.Adj v w ∧ H.degree w = 1)}

theorem mem_leafFree {W : Type*} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj] (v w : W) :
    w ∈ leafFree H v ↔ w ≠ v ∧ ¬ (H.Adj v w ∧ H.degree w = 1) := Iff.rfl

/-- A neighbour `z` of a vertex `w ≠ v` is never a degree-one neighbour of `v`. -/
theorem not_leaf_of_adj {W : Type*} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj] (v w z : W)
    (hwv : w ≠ v) (hwz : H.Adj w z) : ¬ (H.Adj v z ∧ H.degree z = 1) := by
  classical
  rintro ⟨hvz, hz1⟩
  have h2 : 2 ≤ H.degree z := by
    rw [← card_neighborFinset_eq_degree]
    have : ({v, w} : Finset W) ⊆ H.neighborFinset z := by
      intro y hy
      rw [Finset.mem_insert, Finset.mem_singleton] at hy
      rw [mem_neighborFinset]
      rcases hy with rfl | rfl
      · exact hvz.symm
      · exact hwz.symm
    have hc : ({v, w} : Finset W).card = 2 := Finset.card_pair (Ne.symm hwv)
    rw [← hc]
    exact Finset.card_le_card this
  omega

/-- The support of `H` with the edges at `v` deleted lies in `leafFree H v`. -/
theorem support_deleteIncidenceSet_subset_leafFree {W : Type*} [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (v : W) : (H.deleteIncidenceSet v).support ⊆ leafFree H v := by
  classical
  intro w hw
  rw [mem_support] at hw
  obtain ⟨z, hz⟩ := hw
  rw [deleteIncidenceSet_adj] at hz
  rw [mem_leafFree]
  refine ⟨hz.2.1, ?_⟩
  rintro ⟨hvw, hw1⟩
  have h2 : 2 ≤ H.degree w := by
    rw [← card_neighborFinset_eq_degree]
    have : ({v, z} : Finset W) ⊆ H.neighborFinset w := by
      intro y hy
      rw [Finset.mem_insert, Finset.mem_singleton] at hy
      rw [mem_neighborFinset]
      rcases hy with rfl | rfl
      · exact hvw.symm
      · exact hz.1
    have hc : ({v, z} : Finset W).card = 2 := Finset.card_pair (Ne.symm hz.2.2)
    rw [← hc]
    exact Finset.card_le_card this
  omega

/-- `H` restricted to `leafFree H v` has `m - deg v` edges. -/
theorem ncard_edgeSet_induce_leafFree {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (v : W) :
    (H.induce (leafFree H v)).edgeSet.ncard = H.edgeSet.ncard - H.degree v := by
  classical
  have hv : v ∉ leafFree H v := fun h => (mem_leafFree H v v).mp h |>.1 rfl
  have h1 := card_edgeFinset_induce_of_support_subset (support_deleteIncidenceSet_subset_leafFree H v)
  have h1' : ((H.deleteIncidenceSet v).induce (leafFree H v)).edgeSet.ncard =
      (H.deleteIncidenceSet v).edgeSet.ncard := by
    rw [← coe_edgeFinset, Set.ncard_coe_finset, ← coe_edgeFinset, Set.ncard_coe_finset]
    exact h1
  rw [induce_deleteIncidenceSet_of_notMem H hv] at h1'
  rw [h1', ← coe_edgeFinset, Set.ncard_coe_finset, card_edgeFinset_deleteIncidenceSet,
    ← coe_edgeFinset, Set.ncard_coe_finset]

/-- `H` restricted to `leafFree H v` has no isolated vertices. -/
theorem degree_pos_induce_leafFree {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (h0 : ∀ v, 0 < H.degree v) (v : W) (w : leafFree H v) :
    0 < (H.induce (leafFree H v)).degree w := by
  obtain ⟨hwv, hwl⟩ := (mem_leafFree H v w).mp w.2
  rw [degree_pos_iff_exists_adj]
  by_cases hvw : H.Adj v w
  · -- `w` has degree at least two, so a neighbour other than `v`
    have hdeg : H.degree w ≠ 1 := fun h => hwl ⟨hvw, h⟩
    have h2 : 2 ≤ H.degree w := by have := h0 w; omega
    obtain ⟨z, hz, hzv⟩ : ∃ z, H.Adj w z ∧ z ≠ v := by
      by_contra hcon
      push Not at hcon
      have : H.neighborFinset w ⊆ {v} := by
        intro y hy
        rw [mem_neighborFinset] at hy
        rw [Finset.mem_singleton]
        exact hcon y hy
      have := Finset.card_le_card this
      rw [card_neighborFinset_eq_degree, Finset.card_singleton] at this
      omega
    refine ⟨⟨z, (mem_leafFree H v z).mpr ⟨hzv, not_leaf_of_adj H v w z hwv hz⟩⟩, ?_⟩
    exact induce_adj.mpr hz
  · obtain ⟨z, hz⟩ := (H.degree_pos_iff_exists_adj w).mp (h0 w)
    have hzv : z ≠ v := fun h => hvw (by subst h; exact hz.symm)
    refine ⟨⟨z, (mem_leafFree H v z).mpr ⟨hzv, not_leaf_of_adj H v w z hwv hz⟩⟩, ?_⟩
    exact induce_adj.mpr hz


/-- Extending a copy of `H` restricted to `leafFree H v` by `x` for `v` and by further neighbours of `x` for the
degree-one neighbours of `v`; possible as soon as `x` has degree at least `#W - 1`. -/
theorem isContained_of_extend_leaves {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
    (H : SimpleGraph W) [DecidableRel H.Adj] (v : W) (G : SimpleGraph V) [DecidableRel G.Adj] (x : V)
    (f : Copy (H.induce (leafFree H v)) G) (hf : ∀ w, G.Adj x (f w))
    (hx : Fintype.card W - 1 ≤ G.degree x) : H.IsContained G := by
  set L : Finset W := Finset.univ.filter (fun w => H.Adj v w ∧ H.degree w = 1) with hL
  set A : Finset V := G.neighborFinset x \ Finset.univ.image (fun w : leafFree H v => f w) with hA
  have hinj : Function.Injective (fun w : leafFree H v => f w) := fun a b h => f.injective h
  have himg : (Finset.univ.image (fun w : leafFree H v => f w)).card = Fintype.card (leafFree H v) := by
    have := Finset.card_image_of_injective (Finset.univ : Finset (leafFree H v)) hinj
    rw [Finset.card_univ] at this
    exact this
  have hpart : (Finset.univ : Finset W) = (leafFree H v).toFinset ∪ (L ∪ {v}) := by
    ext w
    simp only [Finset.mem_univ, true_iff, Finset.mem_union, Set.mem_toFinset, mem_leafFree, hL,
      Finset.mem_filter, Finset.mem_singleton]
    tauto
  have hd1 : Disjoint (leafFree H v).toFinset (L ∪ {v}) := by
    rw [Finset.disjoint_left]
    intro w hw hw'
    rw [Set.mem_toFinset, mem_leafFree] at hw
    rw [Finset.mem_union, hL, Finset.mem_filter, Finset.mem_singleton] at hw'
    rcases hw' with ⟨-, h⟩ | h
    · exact hw.2 h
    · exact hw.1 h
  have hd2 : Disjoint L {v} := by
    rw [Finset.disjoint_singleton_right, hL, Finset.mem_filter]
    rintro ⟨-, h, -⟩
    exact h.ne rfl
  have hsplit : Fintype.card W = Fintype.card (leafFree H v) + L.card + 1 := by
    rw [← Finset.card_univ, hpart, Finset.card_union_of_disjoint hd1, Finset.card_union_of_disjoint hd2,
      Finset.card_singleton, Set.toFinset_card]
    ring
  have hsub : (Finset.univ.image (fun w : leafFree H v => f w)) ⊆ G.neighborFinset x := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨w, -, rfl⟩ := hy
    rw [mem_neighborFinset]
    exact hf w
  have hAcard : L.card ≤ A.card := by
    rw [hA, Finset.card_sdiff_of_subset hsub, card_neighborFinset_eq_degree, himg]
    omega
  obtain ⟨g⟩ : Nonempty (L ↪ A) := Function.Embedding.nonempty_of_card_le (by simpa using hAcard)
  have hmemL : ∀ w, w ≠ v → w ∉ leafFree H v → w ∈ L := fun w h1 h2 => by
    rw [hL, Finset.mem_filter]
    rw [mem_leafFree] at h2
    push Not at h2
    exact ⟨Finset.mem_univ _, h2 h1⟩
  have hgA : ∀ w, (g w).1 ∈ G.neighborFinset x \ Finset.univ.image (fun w : leafFree H v => f w) :=
    fun w => (g w).2
  have hgx : ∀ w, G.Adj x (g w).1 := fun w => by
    have := hgA w
    rw [Finset.mem_sdiff, mem_neighborFinset] at this
    exact this.1
  have hgf : ∀ w (w' : leafFree H v), (g w).1 ≠ f w' := fun w w' h => by
    have := hgA w
    rw [Finset.mem_sdiff] at this
    exact this.2 (Finset.mem_image.mpr ⟨w', Finset.mem_univ _, h.symm⟩)
  have hLne : ∀ w ∈ L, w ≠ v := fun w hw => by
    rw [hL, Finset.mem_filter] at hw
    exact hw.2.1.ne.symm
  have hLnotadj : ∀ p, p ≠ v → ∀ q ∈ L, ¬ H.Adj p q := fun p hp q hq hpq => by
    rw [hL, Finset.mem_filter] at hq
    exact not_leaf_of_adj H v p q hp hpq hq.2
  refine ⟨⟨⟨fun w => if h : w = v then x else if h' : w ∈ leafFree H v then f ⟨w, h'⟩
    else (g ⟨w, hmemL w h h'⟩).1, ?_⟩, ?_⟩⟩
  · intro p q hpq
    by_cases hp : p = v <;> by_cases hq : q = v
    · subst hp hq
      exact (hpq.ne rfl).elim
    · rw [dite_eq_left hp, dite_eq_right hq]
      by_cases hq' : q ∈ leafFree H v
      · rw [dite_eq_left hq']
        exact hf _
      · rw [dite_eq_right hq']
        exact hgx _
    · rw [dite_eq_right hp, dite_eq_left hq]
      by_cases hp' : p ∈ leafFree H v
      · rw [dite_eq_left hp']
        exact (hf _).symm
      · rw [dite_eq_right hp']
        exact (hgx _).symm
    · rw [dite_eq_right hp, dite_eq_right hq]
      by_cases hp' : p ∈ leafFree H v <;> by_cases hq' : q ∈ leafFree H v
      · rw [dite_eq_left hp', dite_eq_left hq']
        exact f.toHom.map_adj (induce_adj.mpr hpq)
      · exact (hLnotadj p hp q (hmemL q hq hq') hpq).elim
      · exact (hLnotadj q hq p (hmemL p hp hp') hpq.symm).elim
      · exact (hLnotadj p hp q (hmemL q hq hq') hpq).elim
  · intro p q h
    simp only [RelHom.coeFn_mk] at h
    by_cases hp : p = v <;> by_cases hq : q = v
    · rw [hp, hq]
    · rw [dite_eq_left hp, dite_eq_right hq] at h
      by_cases hq' : q ∈ leafFree H v
      · rw [dite_eq_left hq'] at h
        exact ((hf _).ne h).elim
      · rw [dite_eq_right hq'] at h
        exact ((hgx _).ne h).elim
    · rw [dite_eq_right hp, dite_eq_left hq] at h
      by_cases hp' : p ∈ leafFree H v
      · rw [dite_eq_left hp'] at h
        exact ((hf _).ne h.symm).elim
      · rw [dite_eq_right hp'] at h
        exact ((hgx _).ne h.symm).elim
    · rw [dite_eq_right hp, dite_eq_right hq] at h
      by_cases hp' : p ∈ leafFree H v <;> by_cases hq' : q ∈ leafFree H v
      · rw [dite_eq_left hp', dite_eq_left hq'] at h
        exact congrArg Subtype.val (f.injective h)
      · rw [dite_eq_left hp', dite_eq_right hq'] at h
        exact (hgf _ _ h.symm).elim
      · rw [dite_eq_right hp', dite_eq_left hq'] at h
        exact (hgf _ _ h).elim
      · rw [dite_eq_right hp', dite_eq_right hq'] at h
        exact congrArg Subtype.val (g.injective (Subtype.ext h))


/-- **Vertex-with-leaves step.** Delete a vertex `v` together with its degree-one neighbours; if the pointwise
statement holds for what remains (`m - deg v` edges) and some vertex `x` has blue degree at least both
`(k-1)(m - deg v) + 1` and `#W - 1`, the colouring has a red `C_k` or a blue `H`. -/
theorem step_leaves (k m : ℕ) (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (v : W)
    (ih : ∀ C' : SimpleGraph (Fin ((k - 1) * (m - H.degree v) + 1)),
      (cycleGraph k).IsContained C' ∨ (H.induce (leafFree H v)).IsContained C'ᶜ)
    {n : ℕ} (C : SimpleGraph (Fin n)) [DecidableRel C.Adj] (x : Fin n)
    (hx : (k - 1) * (m - H.degree v) + 1 ≤ Cᶜ.degree x) (hx' : Fintype.card W - 1 ≤ Cᶜ.degree x) :
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
    let g : Copy (H.induce (leafFree H v)) Cᶜ :=
      (Embedding.comap e Cᶜ).toCopy.comp ((Copy.ofLE _ _ hle).comp f)
    have hg : ∀ w, g w = e (f w) := fun w => rfl
    have hblue : ∀ w, Cᶜ.Adj x (g w) := by
      intro w
      rw [hg]
      exact (mem_neighborFinset _ _ _).mp (he (f w))
    exact isContained_of_extend_leaves H v Cᶜ x g hblue hx'

/-- **Reduction.** The pointwise statement for all `H` with at least one edge follows from the *residue*: the
case of an `H'` with `m' ≥ 3` edges, not a star, without isolated edges, under the induction hypothesis for fewer
edges, for a colouring whose vertex `x` of maximum blue degree has blue degree `≥ m'` but, for every vertex `v`
of `H'`, blue degree below `(k-1)(m' - deg v) + 1`, or below `#W' - 1` while `v` has a degree-one neighbour.
Everything else is handled by the proved lemmas. -/
theorem core_of_residue (k : ℕ) (hk : 3 ≤ k)
    (hres : ∀ (m' : ℕ) (W' : Type) [Fintype W'] (H' : SimpleGraph W') [DecidableRel H'.Adj],
      (∀ v, 0 < H'.degree v) → H'.edgeSet.ncard = m' → 3 ≤ m' →
      (¬ ∃ v₀, ∀ a b, H'.Adj a b → a = v₀ ∨ b = v₀) →
      (¬ ∃ a b, H'.Adj a b ∧ (∀ w, H'.Adj a w → w = b) ∧ (∀ w, H'.Adj b w → w = a)) →
      (∀ m'' < m', ∀ (W'' : Type) [Fintype W''] (H'' : SimpleGraph W'') [DecidableRel H''.Adj],
        (∀ v, 0 < H''.degree v) → H''.edgeSet.ncard = m'' → 1 ≤ m'' →
        ∀ C'' : SimpleGraph (Fin ((k - 1) * m'' + 1)),
          (cycleGraph k).IsContained C'' ∨ H''.IsContained C''ᶜ) →
      ∀ (C' : SimpleGraph (Fin ((k - 1) * m' + 1))) [DecidableRel C'.Adj] (x : Fin ((k - 1) * m' + 1)),
        (∀ y, C'ᶜ.degree y ≤ C'ᶜ.degree x) → m' ≤ C'ᶜ.degree x →
        (∀ v, C'ᶜ.degree x < (k - 1) * (m' - H'.degree v) + 1 ∨
          ((∃ w, H'.Adj v w ∧ H'.degree w = 1) ∧ C'ᶜ.degree x < Fintype.card W' - 1)) →
        (cycleGraph k).IsContained C' ∨ H'.IsContained C'ᶜ)
    (m : ℕ) (hm1 : 1 ≤ m) (W : Type) [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (h0 : ∀ v, 0 < H.degree v) (hm : H.edgeSet.ncard = m) (C : SimpleGraph (Fin ((k - 1) * m + 1))) :
    (cycleGraph k).IsContained C ∨ H.IsContained Cᶜ := by
  classical
  suffices key : ∀ m', m' ≤ m → ∀ (W' : Type) [Fintype W'] (H' : SimpleGraph W') [DecidableRel H'.Adj],
      (∀ v, 0 < H'.degree v) → H'.edgeSet.ncard = m' → 1 ≤ m' →
      ∀ C' : SimpleGraph (Fin ((k - 1) * m' + 1)), (cycleGraph k).IsContained C' ∨ H'.IsContained C'ᶜ by
    exact key m le_rfl W H h0 hm hm1 C
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
  have hW' : Nonempty W' := nonempty_of_ncard_edgeSet_pos H' (by omega)
  -- an isolated edge of `H'`: the isolated-edge step
  by_cases hiso : ∃ a b, H'.Adj a b ∧ (∀ w, H'.Adj a w → w = b) ∧ (∀ w, H'.Adj b w → w = a)
  · obtain ⟨a, b, hab, ha, hb⟩ := hiso
    have hmab : (H'.induce ({a, b}ᶜ : Set W')).edgeSet.ncard = m' - 1 := by
      rw [ncard_edgeSet_induce_compl_pair H' a b hab ha hb, hm']
    exact step_isolated_edge k hk m' (by omega) W' H' a b hab ha hb
      (ih (m' - 1) (by omega) (by omega) _ _ (degree_pos_induce_compl_pair H' h0' a b ha hb) hmab
        (by omega)) C'
  -- a vertex of maximum blue degree
  obtain ⟨x, hxmax⟩ := exists_max_degree C'ᶜ
  by_cases hx : m' ≤ C'ᶜ.degree x
  swap
  · have hlt : ∀ y, C'ᶜ.degree y < m' := fun y => lt_of_le_of_lt (hxmax y) (by omega)
    exact Or.inl (cycleGraph_isContained_of_compl_degree_lt k m' (by omega) C' hlt)
  by_cases hall : ∀ v, C'ᶜ.degree x < (k - 1) * (m' - H'.degree v) + 1 ∨
      ((∃ w, H'.Adj v w ∧ H'.degree w = 1) ∧ C'ᶜ.degree x < Fintype.card W' - 1)
  · exact hres m' W' H' h0' hm' h2 hstar hiso (fun m'' hlt => ih m'' hlt (by omega)) C' x hxmax hx hall
  · push Not at hall
    obtain ⟨v, hv1, hv2⟩ := hall
    have hvlt : H'.degree v < m' := degree_lt_ncard_of_not_star H' m' hm' hstar v
    have hvpos : 0 < H'.degree v := h0' v
    by_cases hleaf : ∃ w, H'.Adj v w ∧ H'.degree w = 1
    · have hmv : (H'.induce (leafFree H' v)).edgeSet.ncard = m' - H'.degree v := by
        rw [ncard_edgeSet_induce_leafFree, hm']
      have ih' := ih (m' - H'.degree v) (by omega) (by omega) _ (H'.induce (leafFree H' v))
        (degree_pos_induce_leafFree H' h0' v) hmv (by omega)
      exact step_leaves k m' W' H' v ih' C' x hv1 (hv2 hleaf)
    · have hleaf' : ∀ w, H'.Adj v w → 2 ≤ H'.degree w := by
        intro w hw
        have h1 := h0' w
        have h2 : H'.degree w ≠ 1 := fun h => hleaf ⟨w, hw, h⟩
        omega
      have hmv : (H'.induce ({v}ᶜ : Set W')).edgeSet.ncard = m' - H'.degree v := by
        rw [ncard_edgeSet_induce_compl_singleton, hm']
      have ih' := ih (m' - H'.degree v) (by omega) (by omega) _ (H'.induce ({v}ᶜ : Set W'))
        (degree_pos_induce_compl_singleton H' h0' v hleaf') hmv (by omega)
      exact step_large_degree k m' W' H' v ih' C' x hv1

/-- A blue clique on at least `#W` vertices contains a blue copy of any `H` on `W`. -/
theorem isContained_of_isClique_card_le {W V : Type*} [Fintype W] [Fintype V] (H : SimpleGraph W)
    (G : SimpleGraph V) (s : Finset V) (hs : G.IsClique (s : Set V)) (hcard : Fintype.card W ≤ s.card) :
    H.IsContained G := by
  classical
  have htop : G.induce (s : Set V) = ⊤ := induce_eq_top.mpr hs
  have h1 : H.IsContained (⊤ : SimpleGraph (s : Set V)) :=
    isContained_top_iff.mpr (Function.Embedding.nonempty_of_card_le (by simpa using hcard))
  rw [← htop] at h1
  exact h1.trans ⟨(Embedding.comap (Function.Embedding.subtype _) G).toCopy⟩

/-! ### Route F: reduction to connected `H` -/

/-- Copies of `H` on a union of components `S` and on its complement, with disjoint images, combine to a copy of
`H`. -/
theorem isContained_of_union {W V : Type*} (H : SimpleGraph W) (S : Set W) [DecidablePred (· ∈ S)]
    (hS : ∀ a b, H.Adj a b → (a ∈ S ↔ b ∈ S)) (G : SimpleGraph V)
    (f₁ : Copy (H.induce S) G) (f₂ : Copy (H.induce Sᶜ) G) (hdisj : ∀ a b, f₁ a ≠ f₂ b) :
    H.IsContained G := by
  refine ⟨⟨⟨fun w => if h : w ∈ S then f₁ ⟨w, h⟩ else f₂ ⟨w, h⟩, ?_⟩, ?_⟩⟩
  · intro p q hpq
    by_cases hp : p ∈ S <;> by_cases hq : q ∈ S
    · rw [dite_eq_left hp, dite_eq_left hq]
      exact f₁.toHom.map_adj (induce_adj.mpr hpq)
    · exact absurd ((hS p q hpq).mp hp) hq
    · exact absurd ((hS p q hpq).mpr hq) hp
    · rw [dite_eq_right hp, dite_eq_right hq]
      exact f₂.toHom.map_adj (induce_adj.mpr hpq)
  · intro p q h
    simp only [RelHom.coeFn_mk] at h
    by_cases hp : p ∈ S <;> by_cases hq : q ∈ S
    · rw [dite_eq_left hp, dite_eq_left hq] at h
      exact congrArg Subtype.val (f₁.injective h)
    · rw [dite_eq_left hp, dite_eq_right hq] at h
      exact (hdisj _ _ h).elim
    · rw [dite_eq_right hp, dite_eq_left hq] at h
      exact (hdisj _ _ h.symm).elim
    · rw [dite_eq_right hp, dite_eq_right hq] at h
      exact congrArg Subtype.val (f₂.injective h)

/-- If `S` is a union of components of `H`, the edges of `H` split into those inside `S` and those inside `Sᶜ`. -/
theorem ncard_edgeSet_induce_add_compl {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (S : Set W) [DecidablePred (· ∈ S)]
    (hS : ∀ a b, H.Adj a b → (a ∈ S ↔ b ∈ S)) :
    (H.induce S).edgeSet.ncard + (H.induce Sᶜ).edgeSet.ncard = H.edgeSet.ncard := by
  classical
  have h1 := congrArg Finset.card (map_edgeFinset_induce (G := H) (s := S))
  have h2 := congrArg Finset.card (map_edgeFinset_induce (G := H) (s := Sᶜ))
  rw [Finset.card_map] at h1 h2
  have hunion : H.edgeFinset =
      (H.edgeFinset ∩ S.toFinset.sym2) ∪ (H.edgeFinset ∩ Sᶜ.toFinset.sym2) := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mk_mem_sym2_iff, Set.mem_toFinset,
      Set.mem_compl_iff]
    constructor
    · intro h
      have hadj : H.Adj a b := (mem_edgeSet H).mp (mem_edgeFinset.mp h)
      by_cases ha : a ∈ S
      · exact Or.inl ⟨h, ha, (hS a b hadj).mp ha⟩
      · exact Or.inr ⟨h, ha, fun hb => ha ((hS a b hadj).mpr hb)⟩
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
  have hdisj : Disjoint (H.edgeFinset ∩ S.toFinset.sym2) (H.edgeFinset ∩ Sᶜ.toFinset.sym2) := by
    rw [Finset.disjoint_left]
    intro e he he'
    induction e using Sym2.ind with
    | _ a b =>
    simp only [Finset.mem_inter, Finset.mk_mem_sym2_iff, Set.mem_toFinset, Set.mem_compl_iff] at he he'
    exact he'.2.1 he.2.1
  rw [← coe_edgeFinset, Set.ncard_coe_finset, ← coe_edgeFinset, Set.ncard_coe_finset,
    ← coe_edgeFinset, Set.ncard_coe_finset, h1, h2, ← Finset.card_union_of_disjoint hdisj, ← hunion]

/-- A union of components of a graph without isolated vertices has no isolated vertices. -/
theorem degree_pos_induce_closed {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (h0 : ∀ v, 0 < H.degree v) (S : Set W) [DecidablePred (· ∈ S)]
    (hS : ∀ a b, H.Adj a b → (a ∈ S ↔ b ∈ S)) (w : S) : 0 < (H.induce S).degree w := by
  obtain ⟨z, hz⟩ := (H.degree_pos_iff_exists_adj w).mp (h0 w)
  rw [degree_pos_iff_exists_adj]
  exact ⟨⟨z, (hS w z hz).mp w.2⟩, induce_adj.mpr hz⟩

/-- A graph without isolated vertices has at most twice as many vertices as edges. -/
theorem card_le_two_mul_ncard_edgeSet {W : Type*} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (h0 : ∀ v, 0 < H.degree v) : Fintype.card W ≤ 2 * H.edgeSet.ncard := by
  classical
  have h1 : ∑ _v : W, 1 ≤ ∑ v : W, H.degree v := Finset.sum_le_sum (fun v _ => h0 v)
  rw [sum_degrees_eq_twice_card_edges] at h1
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at h1
  rw [← coe_edgeFinset, Set.ncard_coe_finset]
  exact h1

/-- A graph without isolated vertices restricted to a nonempty union of components has an edge. -/
theorem one_le_ncard_edgeSet_induce_closed {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (h0 : ∀ v, 0 < H.degree v) (S : Set W) [DecidablePred (· ∈ S)]
    (hS : ∀ a b, H.Adj a b → (a ∈ S ↔ b ∈ S)) (a : W) (ha : a ∈ S) :
    1 ≤ (H.induce S).edgeSet.ncard := by
  have hdeg := degree_pos_induce_closed H h0 S hS ⟨a, ha⟩
  by_contra hcon
  have hz : (H.induce S).edgeSet.ncard = 0 := by omega
  have hbot : H.induce S = ⊥ := edgeSet_eq_empty.mp ((Set.ncard_eq_zero).mp hz)
  obtain ⟨z, hz⟩ := (degree_pos_iff_exists_adj _ _).mp hdeg
  have hz' : (H.induce S).Adj ⟨a, ha⟩ z := hz
  rw [hbot] at hz'
  exact hz'

/-- **Disconnected step.** If `S` is a proper nonempty union of components of `H` and the pointwise statement
holds for all graphs with fewer edges, it holds for `H`: embed `H[S]` first, then `H[Sᶜ]` in the remaining
`n - #S ≥ (k-1)m₂ + 1` vertices (as `#S ≤ 2m₁ ≤ (k-1)m₁`). -/
theorem step_disconnected (k : ℕ) (hk : 3 ≤ k) (m : ℕ) (W : Type) [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (h0 : ∀ v, 0 < H.degree v) (hm : H.edgeSet.ncard = m)
    (S : Set W) [DecidablePred (· ∈ S)] (hS : ∀ a b, H.Adj a b → (a ∈ S ↔ b ∈ S))
    (ha : ∃ a, a ∈ S) (hb : ∃ b, b ∉ S)
    (ih : ∀ m'' < m, ∀ (W'' : Type) [Fintype W''] (H'' : SimpleGraph W'') [DecidableRel H''.Adj],
      (∀ v, 0 < H''.degree v) → H''.edgeSet.ncard = m'' → 1 ≤ m'' →
      ∀ C'' : SimpleGraph (Fin ((k - 1) * m'' + 1)),
        (cycleGraph k).IsContained C'' ∨ H''.IsContained C''ᶜ)
    (C : SimpleGraph (Fin ((k - 1) * m + 1))) : (cycleGraph k).IsContained C ∨ H.IsContained Cᶜ := by
  classical
  have hS' : ∀ a b, H.Adj a b → (a ∈ Sᶜ ↔ b ∈ Sᶜ) := fun a b hab => by
    rw [Set.mem_compl_iff, Set.mem_compl_iff]
    exact not_congr (hS a b hab)
  obtain ⟨m₁, hm₁⟩ : ∃ m₁, (H.induce S).edgeSet.ncard = m₁ := ⟨_, rfl⟩
  obtain ⟨m₂, hm₂⟩ : ∃ m₂, (H.induce Sᶜ).edgeSet.ncard = m₂ := ⟨_, rfl⟩
  have hsum : m₁ + m₂ = m := by rw [← hm₁, ← hm₂, ncard_edgeSet_induce_add_compl H S hS, hm]
  have h0₁ := degree_pos_induce_closed H h0 S hS
  have h0₂ := degree_pos_induce_closed H h0 Sᶜ hS'
  obtain ⟨a, haS⟩ := ha
  obtain ⟨b, hbS⟩ := hb
  have hm₁pos : 1 ≤ m₁ := hm₁ ▸ one_le_ncard_edgeSet_induce_closed H h0 S hS a haS
  have hm₂pos : 1 ≤ m₂ := hm₂ ▸ one_le_ncard_edgeSet_induce_closed H h0 Sᶜ hS' b hbS
  have hcard₁ : Fintype.card S ≤ 2 * m₁ := hm₁ ▸ card_le_two_mul_ncard_edgeSet _ h0₁
  -- first component union
  have hle₁ : (k - 1) * m₁ + 1 ≤ (k - 1) * m + 1 := by
    have := Nat.mul_le_mul_left (k - 1) (show m₁ ≤ m by omega)
    omega
  have ih₁ := ih m₁ (by omega) S (H.induce S) h0₁ hm₁ hm₁pos
  rcases ih₁ (C.comap (Fin.castLEEmb hle₁)) with h1 | h1
  · exact Or.inl (h1.trans ⟨(Embedding.comap _ C).toCopy⟩)
  obtain ⟨f₁⟩ := h1
  have hle₁' : (C.comap (Fin.castLEEmb hle₁))ᶜ ≤ Cᶜ.comap (Fin.castLEEmb hle₁) := by
    intro p q hpq
    rw [compl_adj, comap_adj] at hpq
    rw [comap_adj, compl_adj]
    exact ⟨fun h' => hpq.1 ((Fin.castLEEmb hle₁).injective h'), hpq.2⟩
  let g₁ : Copy (H.induce S) Cᶜ :=
    (Embedding.comap (Fin.castLEEmb hle₁) Cᶜ).toCopy.comp ((Copy.ofLE _ _ hle₁').comp f₁)
  have hg₁inj : Function.Injective (fun w : S => g₁ w) := fun p q h => g₁.injective h
  -- the vertices not used by the first copy
  have hAcard : (k - 1) * m₂ + 1 ≤
      (Finset.univ \ Finset.univ.image (fun w : S => g₁ w)).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      Finset.card_image_of_injective _ hg₁inj, Finset.card_univ]
    have h2 : 2 * m₁ ≤ (k - 1) * m₁ := Nat.mul_le_mul_right _ (by omega)
    have h3 : (k - 1) * m = (k - 1) * m₁ + (k - 1) * m₂ := by rw [← hsum, Nat.mul_add]
    omega
  obtain ⟨e₂, he₂⟩ := exists_embedding_into_finset _ _ hAcard
  have ih₂ := ih m₂ (by omega) (Sᶜ : Set W) (H.induce (Sᶜ : Set W)) h0₂ hm₂ hm₂pos
  rcases ih₂ (C.comap e₂) with h2 | h2
  · exact Or.inl (h2.trans ⟨(Embedding.comap e₂ C).toCopy⟩)
  obtain ⟨f₂⟩ := h2
  have hle₂' : (C.comap e₂)ᶜ ≤ Cᶜ.comap e₂ := by
    intro p q hpq
    rw [compl_adj, comap_adj] at hpq
    rw [comap_adj, compl_adj]
    exact ⟨fun h' => hpq.1 (e₂.injective h'), hpq.2⟩
  let g₂ : Copy (H.induce Sᶜ) Cᶜ :=
    (Embedding.comap e₂ Cᶜ).toCopy.comp ((Copy.ofLE _ _ hle₂').comp f₂)
  have hg₂ : ∀ w, g₂ w = e₂ (f₂ w) := fun w => rfl
  right
  refine isContained_of_union H S hS Cᶜ g₁ g₂ ?_
  intro p q hpq
  have hmem := he₂ (f₂ q)
  rw [Finset.mem_sdiff] at hmem
  exact hmem.2 (Finset.mem_image.mpr ⟨p, Finset.mem_univ _, by rw [hpq, hg₂]⟩)

/-- **Reduction, connected form.** The residue may assume `H'` connected (`step_disconnected`), and then
`#W' ≤ m' + 1 ≤ D + 1` makes the leaf alternative impossible: the residue is the case where the maximum blue
degree `D` satisfies `m' ≤ D` and `D < (k-1)(m' - deg v) + 1` for every vertex `v` of `H'`. -/
theorem core_of_residue_connected (k : ℕ) (hk : 3 ≤ k)
    (hres : ∀ (m' : ℕ) (W' : Type) [Fintype W'] (H' : SimpleGraph W') [DecidableRel H'.Adj],
      (∀ v, 0 < H'.degree v) → H'.edgeSet.ncard = m' → 3 ≤ m' →
      (¬ ∃ v₀, ∀ a b, H'.Adj a b → a = v₀ ∨ b = v₀) → H'.Preconnected →
      (∀ m'' < m', ∀ (W'' : Type) [Fintype W''] (H'' : SimpleGraph W'') [DecidableRel H''.Adj],
        (∀ v, 0 < H''.degree v) → H''.edgeSet.ncard = m'' → 1 ≤ m'' →
        ∀ C'' : SimpleGraph (Fin ((k - 1) * m'' + 1)),
          (cycleGraph k).IsContained C'' ∨ H''.IsContained C''ᶜ) →
      ∀ (C' : SimpleGraph (Fin ((k - 1) * m' + 1))) [DecidableRel C'.Adj] (x : Fin ((k - 1) * m' + 1)),
        (∀ y, C'ᶜ.degree y ≤ C'ᶜ.degree x) → m' ≤ C'ᶜ.degree x →
        (∀ v, C'ᶜ.degree x < (k - 1) * (m' - H'.degree v) + 1) →
        (cycleGraph k).IsContained C' ∨ H'.IsContained C'ᶜ)
    (m : ℕ) (hm1 : 1 ≤ m) (W : Type) [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (h0 : ∀ v, 0 < H.degree v) (hm : H.edgeSet.ncard = m) (C : SimpleGraph (Fin ((k - 1) * m + 1))) :
    (cycleGraph k).IsContained C ∨ H.IsContained Cᶜ := by
  classical
  refine core_of_residue k hk ?_ m hm1 W H h0 hm C
  intro m' W' _ H' _ h0' hm' hm3' hstar _ ih C' _ x hxmax hx hall
  by_cases hconn : H'.Preconnected
  swap
  · unfold Preconnected at hconn
    push Not at hconn
    obtain ⟨a, b, hab⟩ := hconn
    have hS : ∀ p q, H'.Adj p q → (p ∈ {w | H'.Reachable a w} ↔ q ∈ {w | H'.Reachable a w}) := by
      intro p q hpq
      exact ⟨fun h => h.trans hpq.reachable, fun h => h.trans hpq.symm.reachable⟩
    exact step_disconnected k hk m' W' H' h0' hm' {w | H'.Reachable a w} hS ⟨a, Reachable.refl a⟩
      ⟨b, hab⟩ ih C'
  have hW' : Nonempty W' := nonempty_of_ncard_edgeSet_pos H' (by omega)
  have hcard : Fintype.card W' ≤ m' + 1 := by
    have h := (⟨hconn⟩ : H'.Connected).card_vert_le_card_edgeSet_add_one
    rw [Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hm'] at h
    exact h
  have hall' : ∀ v, C'ᶜ.degree x < (k - 1) * (m' - H'.degree v) + 1 := by
    intro v
    rcases hall v with h | ⟨-, h⟩
    · exact h
    · omega
  exact hres m' W' H' h0' hm' hm3' hstar hconn ih C' x hxmax hx hall'

/-! ### Edge deletion -/

/-- Deleting one edge removes one edge. -/
theorem ncard_edgeSet_deleteEdges_singleton {W : Type*} (H : SimpleGraph W) (u v : W) (huv : H.Adj u v) :
    (H.deleteEdges {s(u, v)}).edgeSet.ncard = H.edgeSet.ncard - 1 := by
  rw [edgeSet_deleteEdges]
  exact Set.ncard_sdiff_singleton_of_mem ((mem_edgeSet H).mpr huv)

/-- Deleting one edge lowers each degree by at most one. -/
theorem degree_le_degree_deleteEdges_singleton_add_one {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (u v w : W) :
    H.degree w ≤ (H.deleteEdges {s(u, v)}).degree w + 1 := by
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  have hsub : H.neighborFinset w ⊆
      insert (if w = u then v else u) ((H.deleteEdges {s(u, v)}).neighborFinset w) := by
    intro z hz
    rw [mem_neighborFinset] at hz
    rw [Finset.mem_insert, mem_neighborFinset, deleteEdges_adj, Set.mem_singleton_iff]
    by_cases h : s(w, z) = s(u, v)
    · left
      rw [Sym2.eq_iff] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [ite_eq_left rfl]
      · rw [ite_eq_right hz.ne]
    · exact Or.inr ⟨hz, h⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)

/-- A copy of `H - uv` in which the images of `u` and `v` are adjacent is a copy of `H`. -/
theorem isContained_of_deleteEdges_adj {W V : Type*} (H : SimpleGraph W) (u v : W) (G : SimpleGraph V)
    (f : Copy (H.deleteEdges {s(u, v)}) G) (huv : G.Adj (f u) (f v)) : H.IsContained G := by
  refine ⟨⟨⟨f, ?_⟩, f.injective⟩⟩
  intro p q hpq
  by_cases h : s(p, q) = s(u, v)
  · rw [Sym2.eq_iff] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact huv
    · exact huv.symm
  · exact f.toHom.map_adj (deleteEdges_adj.mpr ⟨hpq, by simpa using h⟩)


/-- A degree-one vertex has a unique neighbour. -/
theorem eq_of_adj_of_degree_eq_one {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (p : W) (hp : H.degree p = 1) (q q' : W) (hq : H.Adj p q) (hq' : H.Adj p q') :
    q = q' := by
  have hc : (H.neighborFinset p).card = 1 := by rw [card_neighborFinset_eq_degree, hp]
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hc
  have h1 : q ∈ ({y} : Finset W) := by rw [← hy, mem_neighborFinset]; exact hq
  have h2 : q' ∈ ({y} : Finset W) := by rw [← hy, mem_neighborFinset]; exact hq'
  rw [Finset.mem_singleton] at h1 h2
  rw [h1, h2]

/-- A connected graph that is not a star and has no isolated vertices has an edge both of whose ends have
degree at least two. -/
theorem exists_adj_two_le_degree {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (h0 : ∀ v, 0 < H.degree v) (hns : ¬ ∃ v₀, ∀ a b, H.Adj a b → a = v₀ ∨ b = v₀)
    (hconn : H.Preconnected) (hne : Nonempty W) :
    ∃ u v, H.Adj u v ∧ 2 ≤ H.degree u ∧ 2 ≤ H.degree v := by
  by_contra hcon
  push Not at hcon
  obtain ⟨b, hb⟩ : ∃ b, 2 ≤ H.degree b := by
    by_contra hall
    push Not at hall
    obtain ⟨a⟩ := hne
    obtain ⟨c, hac⟩ := (H.degree_pos_iff_exists_adj a).mp (h0 a)
    have ha1 : H.degree a = 1 := by have := hall a; have := h0 a; omega
    have hc1 : H.degree c = 1 := by have := hall c; have := h0 c; omega
    have hS : ∀ u w, H.Walk u w → (u = a ∨ u = c) → (w = a ∨ w = c) := by
      intro u w p
      induction p with
      | nil => exact id
      | cons h p ih =>
        intro hu
        apply ih
        rcases hu with rfl | rfl
        · exact Or.inr (eq_of_adj_of_degree_eq_one H _ ha1 _ _ hac h).symm
        · exact Or.inl (eq_of_adj_of_degree_eq_one H _ hc1 _ _ hac.symm h).symm
    apply hns
    refine ⟨a, fun p q hpq => ?_⟩
    obtain ⟨w⟩ := hconn a p
    rcases hS a p w (Or.inl rfl) with h | h
    · exact Or.inl h
    · rw [h] at hpq
      exact Or.inr (eq_of_adj_of_degree_eq_one H _ hc1 _ _ hac.symm hpq).symm
  have hnb : ∀ c, H.Adj b c → H.degree c = 1 := fun c hc => by
    have := hcon b c hc hb
    have := h0 c
    omega
  have hS : ∀ u w, H.Walk u w → (u = b ∨ H.Adj b u) → (w = b ∨ H.Adj b w) := by
    intro u w p
    induction p with
    | nil => exact id
    | cons h p ih =>
      intro hu
      apply ih
      rcases hu with rfl | hu
      · exact Or.inr h
      · exact Or.inl (eq_of_adj_of_degree_eq_one H _ (hnb _ hu) _ _ h hu.symm)
  apply hns
  refine ⟨b, fun p q hpq => ?_⟩
  obtain ⟨w⟩ := hconn b p
  rcases hS b p w (Or.inl rfl) with h | h
  · exact Or.inl h
  · exact Or.inr (eq_of_adj_of_degree_eq_one H _ (hnb _ h) _ _ hpq h.symm)

/-! ### Route G: red paths in red neighbourhoods -/

/-- Greedy path: if every vertex of `U` has at least `d` neighbours inside `U`, then for every `j ≤ d` there is a
path of length `j` (so on `j + 1` vertices) inside `U`. -/
theorem exists_isPath_of_forall_degree_ge {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (U : Finset V) (d : ℕ) (hU : ∀ u ∈ U, d ≤ (G.neighborFinset u ∩ U).card)
    (u₀ : V) (hu₀ : u₀ ∈ U) :
    ∀ j, j ≤ d → ∃ (a b : V) (p : G.Walk a b), p.IsPath ∧ p.length = j ∧ ∀ v ∈ p.support, v ∈ U := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨u₀, u₀, Walk.nil, Walk.IsPath.nil, rfl, fun v hv => ?_⟩
    rw [Walk.support_nil, List.mem_singleton] at hv
    rw [hv]
    exact hu₀
  | succ j ih =>
    intro hj
    obtain ⟨a, b, p, hp, hlen, hsupp⟩ := ih (by omega)
    have hsub : (G.neighborFinset a ∩ U).filter (· ∈ p.support) ⊆ p.support.toFinset.erase a := by
      intro c hc
      rw [Finset.mem_filter, Finset.mem_inter, mem_neighborFinset] at hc
      rw [Finset.mem_erase, List.mem_toFinset]
      exact ⟨hc.1.1.ne.symm, hc.2⟩
    have hcard : (p.support.toFinset.erase a).card ≤ j := by
      have h1 : p.support.toFinset.card = j + 1 := by
        rw [List.toFinset_card_of_nodup ((Walk.isPath_def _).mp hp), Walk.length_support, hlen]
      rw [Finset.card_erase_of_mem (List.mem_toFinset.mpr p.start_mem_support), h1]
      omega
    obtain ⟨c, hc1, hc2⟩ : ∃ c ∈ G.neighborFinset a ∩ U, c ∉ p.support := by
      by_contra hcon
      push Not at hcon
      have heq : (G.neighborFinset a ∩ U).filter (· ∈ p.support) = G.neighborFinset a ∩ U :=
        Finset.filter_true_of_mem hcon
      have h2 := Finset.card_le_card hsub
      rw [heq] at h2
      have := hU a (hsupp a p.start_mem_support)
      omega
    rw [Finset.mem_inter, mem_neighborFinset] at hc1
    refine ⟨c, b, Walk.cons hc1.1.symm p, ?_, ?_, ?_⟩
    · exact (Walk.cons_isPath_iff _ _).mpr ⟨hp, hc2⟩
    · rw [Walk.length_cons, hlen]
    · intro v hv
      rw [Walk.support_cons, List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact hc1.2
      · exact hsupp v hv

/-- A path on `k - 1` vertices together with a vertex `z` off the path adjacent to both of its ends gives a
copy of `C_k`. -/
theorem cycleGraph_isContained_of_isPath_apex {V : Type*} (G : SimpleGraph V) (k : ℕ) (hk : 3 ≤ k)
    {a b : V} (p : G.Walk a b) (hp : p.IsPath) (hlen : p.length = k - 2) (z : V) (hz : z ∉ p.support)
    (hza : G.Adj z a) (hbz : G.Adj b z) : (cycleGraph k).IsContained G := by
  rw [cycleGraph_isContained_iff (by omega)]
  refine ⟨b, Walk.cons hbz (Walk.cons hza p), ?_, ?_⟩
  · rw [Walk.cons_isCycle_iff]
    refine ⟨(Walk.cons_isPath_iff _ _).mpr ⟨hp, hz⟩, ?_⟩
    rw [Walk.edges_cons, List.mem_cons, not_or]
    constructor
    · intro h
      rw [Sym2.eq_iff] at h
      rcases h with ⟨hbz', -⟩ | ⟨hba, -⟩
      · apply hz
        rw [← hbz']
        exact p.end_mem_support
      · subst hba
        have hnil : p.Nil := Walk.isPath_iff_nil.mp hp
        rw [← Walk.length_eq_zero_iff] at hnil
        omega
    · intro h
      exact hz (p.snd_mem_support_of_mem_edges h)
  · rw [Walk.length_cons, Walk.length_cons, hlen]
    omega

/-- Greedy blue clique when every nonempty subset of `N` has a vertex with at most `d` red neighbours inside
it: every `U ⊆ N` contains a blue clique `t` with `#U ≤ (d + 1) #t`. -/
theorem exists_isClique_of_forall_exists_low {V : Type*} [Fintype V] [DecidableEq V] (C : SimpleGraph V)
    [DecidableRel C.Adj] (d : ℕ) (N : Finset V)
    (hlow : ∀ U ⊆ N, U.Nonempty → ∃ u ∈ U, (C.neighborFinset u ∩ U).card ≤ d) :
    ∀ n, ∀ U ⊆ N, U.card ≤ n → ∃ t ⊆ U, Cᶜ.IsClique (t : Set V) ∧ U.card ≤ (d + 1) * t.card := by
  intro n
  induction n with
  | zero =>
    intro U _ hU
    exact ⟨∅, Finset.empty_subset _, by simp, by rw [Finset.card_empty, Nat.mul_zero]; exact hU⟩
  | succ n ih =>
    intro U hUN hU
    rcases U.eq_empty_or_nonempty with h | hne
    · exact ⟨∅, Finset.empty_subset _, by simp, by rw [h, Finset.card_empty]; exact Nat.zero_le _⟩
    obtain ⟨u, hu, hdeg⟩ := hlow U hUN hne
    set U' := U.filter (fun w => Cᶜ.Adj u w) with hU'
    have hsub : U' ⊆ U := Finset.filter_subset _ _
    have hu' : u ∉ U' := by
      rw [hU', Finset.mem_filter]
      exact fun h => h.2.ne rfl
    have hdiff : U \ U' ⊆ insert u (C.neighborFinset u ∩ U) := by
      intro w hw
      rw [Finset.mem_sdiff] at hw
      rw [Finset.mem_insert, Finset.mem_inter, mem_neighborFinset]
      by_cases hwu : w = u
      · exact Or.inl hwu
      · refine Or.inr ⟨?_, hw.1⟩
        by_contra hred
        apply hw.2
        rw [hU', Finset.mem_filter]
        exact ⟨hw.1, by rw [compl_adj]; exact ⟨fun h => hwu h.symm, hred⟩⟩
    have h1 : (U \ U').card ≤ d + 1 := by
      calc (U \ U').card ≤ (insert u (C.neighborFinset u ∩ U)).card := Finset.card_le_card hdiff
        _ ≤ (C.neighborFinset u ∩ U).card + 1 := Finset.card_insert_le _ _
        _ ≤ d + 1 := Nat.add_le_add_right hdeg 1
    have h2 := Finset.card_sdiff_add_card_eq_card hsub
    have hU'n : U'.card ≤ n := by
      have : U'.card < U.card :=
        Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨u, hu, fun h => h.ne rfl⟩)
      omega
    obtain ⟨t, hts, ht, hcard'⟩ := ih U' (hsub.trans hUN) hU'n
    have hut : u ∉ t := fun h => hu' (hts h)
    refine ⟨insert u t, Finset.insert_subset hu (hts.trans hsub), ?_, ?_⟩
    · rw [Finset.coe_insert]
      refine ht.insert fun b hb _ => ?_
      have hb' := hts hb
      rw [hU', Finset.mem_filter] at hb'
      exact hb'.2
    · rw [Finset.card_insert_of_notMem hut, Nat.mul_succ]
      omega

/-- **Red-degree bound.** If some vertex `z` has red degree at least `(k-2)(#W - 1) + 1`, the colouring has a
red `C_k` or a blue `H`: a red path on `k - 1` vertices inside the red neighbourhood of `z` would close to a red
`C_k` through `z`, so every nonempty subset of that neighbourhood has a vertex with at most `k - 3` red
neighbours in it, and the greedy blue clique there has at least `#W` vertices. -/
theorem core_of_red_degree {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] (k : ℕ) (hk : 3 ≤ k)
    (H : SimpleGraph W) (C : SimpleGraph V) [DecidableRel C.Adj] (z : V)
    (hz : (k - 2) * (Fintype.card W - 1) + 1 ≤ C.degree z) :
    (cycleGraph k).IsContained C ∨ H.IsContained Cᶜ := by
  classical
  by_cases hred : (cycleGraph k).IsContained C
  · exact Or.inl hred
  right
  have hzN : z ∉ C.neighborFinset z := by
    rw [mem_neighborFinset]
    exact fun h => h.ne rfl
  have hlow : ∀ U ⊆ C.neighborFinset z, U.Nonempty →
      ∃ u ∈ U, (C.neighborFinset u ∩ U).card ≤ k - 3 := by
    intro U hUN hne
    by_contra hcon
    push Not at hcon
    obtain ⟨u₀, hu₀⟩ := hne
    obtain ⟨a, b, p, hp, hlen, hsupp⟩ := exists_isPath_of_forall_degree_ge C U (k - 2)
      (fun u hu => by have := hcon u hu; omega) u₀ hu₀ (k - 2) le_rfl
    apply hred
    refine cycleGraph_isContained_of_isPath_apex C k hk p hp hlen z (fun h => hzN (hUN (hsupp z h))) ?_ ?_
    · have := hUN (hsupp a p.start_mem_support)
      rw [mem_neighborFinset] at this
      exact this
    · have := hUN (hsupp b p.end_mem_support)
      rw [mem_neighborFinset] at this
      exact this.symm
  obtain ⟨t, -, ht, hcard⟩ :=
    exists_isClique_of_forall_exists_low C (k - 3) (C.neighborFinset z) hlow _ _ le_rfl le_rfl
  refine isContained_of_isClique_card_le H Cᶜ t ht ?_
  rw [card_neighborFinset_eq_degree] at hcard
  have hk2 : k - 3 + 1 = k - 2 := by omega
  rw [hk2] at hcard
  by_contra hlt
  push Not at hlt
  have : (k - 2) * t.card ≤ (k - 2) * (Fintype.card W - 1) := Nat.mul_le_mul_left _ (by omega)
  omega

/-- **Reduction, with the red-degree bound.** The residue may further assume that every vertex has red degree
at most `(k-2)(#W' - 1)`, i.e. (as `#W' ≤ m' + 1`) blue degree at least `m'`. -/
theorem core_of_residue_connected' (k : ℕ) (hk : 3 ≤ k)
    (hres : ∀ (m' : ℕ) (W' : Type) [Fintype W'] (H' : SimpleGraph W') [DecidableRel H'.Adj],
      (∀ v, 0 < H'.degree v) → H'.edgeSet.ncard = m' → 3 ≤ m' →
      (¬ ∃ v₀, ∀ a b, H'.Adj a b → a = v₀ ∨ b = v₀) → H'.Preconnected →
      (∀ m'' < m', ∀ (W'' : Type) [Fintype W''] (H'' : SimpleGraph W'') [DecidableRel H''.Adj],
        (∀ v, 0 < H''.degree v) → H''.edgeSet.ncard = m'' → 1 ≤ m'' →
        ∀ C'' : SimpleGraph (Fin ((k - 1) * m'' + 1)),
          (cycleGraph k).IsContained C'' ∨ H''.IsContained C''ᶜ) →
      ∀ (C' : SimpleGraph (Fin ((k - 1) * m' + 1))) [DecidableRel C'.Adj] (x : Fin ((k - 1) * m' + 1)),
        (∀ y, C'ᶜ.degree y ≤ C'ᶜ.degree x) → m' ≤ C'ᶜ.degree x →
        (∀ v, C'ᶜ.degree x < (k - 1) * (m' - H'.degree v) + 1) →
        (∀ z, C'.degree z ≤ (k - 2) * (Fintype.card W' - 1)) →
        (cycleGraph k).IsContained C' ∨ H'.IsContained C'ᶜ)
    (m : ℕ) (hm1 : 1 ≤ m) (W : Type) [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (h0 : ∀ v, 0 < H.degree v) (hm : H.edgeSet.ncard = m) (C : SimpleGraph (Fin ((k - 1) * m + 1))) :
    (cycleGraph k).IsContained C ∨ H.IsContained Cᶜ := by
  classical
  refine core_of_residue_connected k hk ?_ m hm1 W H h0 hm C
  intro m' W' _ H' _ h0' hm' hm3' hstar hconn ih C' _ x hxmax hx hall
  by_cases hzdeg : ∃ z, (k - 2) * (Fintype.card W' - 1) + 1 ≤ C'.degree z
  · obtain ⟨z, hz⟩ := hzdeg
    exact core_of_red_degree k hk H' C' z hz
  · push Not at hzdeg
    exact hres m' W' H' h0' hm' hm3' hstar hconn ih C' x hxmax hx hall (fun z => by have := hzdeg z; omega)

/-! ### Route H: leaves -/

/-- In a connected graph with at least two edges, the neighbour of a degree-one vertex has degree at least two. -/
theorem two_le_degree_of_adj_of_degree_one {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (hconn : H.Preconnected) (m : ℕ) (hm : H.edgeSet.ncard = m) (hm2 : 2 ≤ m)
    (u v : W) (huv : H.Adj u v) (hu : H.degree u = 1) : 2 ≤ H.degree v := by
  by_contra hcon
  have hv : H.degree v = 1 := by
    have : 0 < H.degree v := (H.degree_pos_iff_exists_adj v).mpr ⟨u, huv.symm⟩
    omega
  have hS : ∀ a b, H.Walk a b → (a = u ∨ a = v) → (b = u ∨ b = v) := by
    intro a b p
    induction p with
    | nil => exact id
    | cons h p ih =>
      intro ha
      apply ih
      rcases ha with rfl | rfl
      · exact Or.inr (eq_of_adj_of_degree_eq_one H _ hu _ _ huv h).symm
      · exact Or.inl (eq_of_adj_of_degree_eq_one H _ hv _ _ huv.symm h).symm
  have hall : ∀ a b, H.Adj a b → a = u ∨ b = u := by
    intro a b hab
    obtain ⟨p⟩ := hconn u a
    rcases hS u a p (Or.inl rfl) with h | h
    · exact Or.inl h
    · rw [h] at hab
      exact Or.inr (eq_of_adj_of_degree_eq_one H _ hv _ _ huv.symm hab).symm
  have hle : m ≤ 1 := by
    rw [← hm, ← coe_edgeFinset, Set.ncard_coe_finset]
    have hsub : H.edgeFinset ⊆ H.incidenceFinset u := by
      intro e he
      induction e using Sym2.ind with
      | _ a b =>
        rw [mem_edgeFinset] at he
        have hab := (mem_edgeSet H).mp he
        rw [mem_incidenceFinset, mk'_mem_incidenceSet_iff]
        refine ⟨hab, ?_⟩
        rcases hall a b hab with h | h
        · exact Or.inl h.symm
        · exact Or.inr h.symm
    have := Finset.card_le_card hsub
    rw [card_incidenceFinset_eq_degree, hu] at this
    exact this
  omega

/-- **Leaf step.** If `u` is a degree-one vertex of `H` whose neighbour has degree at least two, the pointwise
statement holds for `H - u` on `(k-1)(m-1)+1 ≤ n` vertices, and every vertex has blue degree at least `#W - 1`,
then the colouring has a red `C_k` or a blue `H`: the copy of `H - u` uses `#W - 1` vertices, so the image of
the neighbour of `u` keeps a blue neighbour outside the copy. -/
theorem step_leaf (k m : ℕ) (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (u : W) (hu : H.degree u = 1)
    (ih : ∀ C' : SimpleGraph (Fin ((k - 1) * (m - 1) + 1)),
      (cycleGraph k).IsContained C' ∨ (H.induce ({u}ᶜ : Set W)).IsContained C'ᶜ)
    {n : ℕ} (C : SimpleGraph (Fin n)) [DecidableRel C.Adj] (hn : (k - 1) * (m - 1) + 1 ≤ n)
    (hblue : ∀ y, Fintype.card W - 1 ≤ Cᶜ.degree y) :
    (cycleGraph k).IsContained C ∨ H.IsContained Cᶜ := by
  classical
  rcases core_mono (cycleGraph k) (H.induce ({u}ᶜ : Set W)) hn ih C with h1 | h1
  · exact Or.inl h1
  right
  obtain ⟨f⟩ := h1
  obtain ⟨v, huv⟩ := (H.degree_pos_iff_exists_adj u).mp (by omega)
  have hvu : v ≠ u := huv.ne.symm
  have hvmem : v ∈ ({u}ᶜ : Set W) := by simpa using hvu
  set v' : ({u}ᶜ : Set W) := ⟨v, hvmem⟩ with hv'
  have hinj : Function.Injective (fun w : ({u}ᶜ : Set W) => f w) := fun a b h => f.injective h
  have himg : (Finset.univ.image (fun w : ({u}ᶜ : Set W) => f w)).card = Fintype.card W - 1 := by
    have := Finset.card_image_of_injective (Finset.univ : Finset ({u}ᶜ : Set W)) hinj
    have h1 : Fintype.card ({u} : Set W) = 1 := by simp
    rw [Finset.card_univ, Fintype.card_compl_set, h1] at this
    exact this
  -- a blue neighbour of `f v'` outside the image
  obtain ⟨y, hy⟩ : ((Cᶜ.neighborFinset (f v')) \ (Finset.univ.image (fun w : ({u}ᶜ : Set W) => f w))).Nonempty := by
    rw [← Finset.card_pos]
    have hsub : (Cᶜ.neighborFinset (f v')) ∩ (Finset.univ.image (fun w : ({u}ᶜ : Set W) => f w)) ⊆
        (Finset.univ.image (fun w : ({u}ᶜ : Set W) => f w)).erase (f v') := by
      intro z hz
      rw [Finset.mem_inter, mem_neighborFinset] at hz
      rw [Finset.mem_erase]
      exact ⟨hz.1.ne.symm, hz.2⟩
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_image.mpr ⟨v', Finset.mem_univ _, rfl⟩), himg] at h1
    have h2 := Finset.card_sdiff_add_card_inter (Cᶜ.neighborFinset (f v'))
      (Finset.univ.image (fun w : ({u}ᶜ : Set W) => f w))
    rw [card_neighborFinset_eq_degree] at h2
    have h3 := hblue (f v')
    have h4 : 2 ≤ Fintype.card W := by
      have : ({u, v} : Finset W).card = 2 := Finset.card_pair hvu.symm
      rw [← this]
      exact Finset.card_le_univ _
    omega
  rw [Finset.mem_sdiff, mem_neighborFinset] at hy
  refine isContained_of_extend H u Cᶜ f y ?_ ?_
  · intro w h
    exact hy.2 (Finset.mem_image.mpr ⟨w, Finset.mem_univ _, h⟩)
  · intro w hw
    have hwv : (w : W) = v := eq_of_adj_of_degree_eq_one H u hu _ _ hw huv
    have : w = v' := Subtype.ext hwv
    rw [this]
    exact hy.1.symm

/-- **Reduction, minimum degree two.** The residue may assume that every vertex of `H'` has degree at least
two: a leaf is handled by `step_leaf`, whose blue-degree hypothesis follows from the red-degree bound. -/
theorem core_of_residue_connected'' (k : ℕ) (hk : 3 ≤ k)
    (hres : ∀ (m' : ℕ) (W' : Type) [Fintype W'] (H' : SimpleGraph W') [DecidableRel H'.Adj],
      (∀ v, 2 ≤ H'.degree v) → H'.edgeSet.ncard = m' → 3 ≤ m' →
      (¬ ∃ v₀, ∀ a b, H'.Adj a b → a = v₀ ∨ b = v₀) → H'.Preconnected →
      (∀ m'' < m', ∀ (W'' : Type) [Fintype W''] (H'' : SimpleGraph W'') [DecidableRel H''.Adj],
        (∀ v, 0 < H''.degree v) → H''.edgeSet.ncard = m'' → 1 ≤ m'' →
        ∀ C'' : SimpleGraph (Fin ((k - 1) * m'' + 1)),
          (cycleGraph k).IsContained C'' ∨ H''.IsContained C''ᶜ) →
      ∀ (C' : SimpleGraph (Fin ((k - 1) * m' + 1))) [DecidableRel C'.Adj] (x : Fin ((k - 1) * m' + 1)),
        (∀ y, C'ᶜ.degree y ≤ C'ᶜ.degree x) → m' ≤ C'ᶜ.degree x →
        (∀ v, C'ᶜ.degree x < (k - 1) * (m' - H'.degree v) + 1) →
        (∀ z, C'.degree z ≤ (k - 2) * (Fintype.card W' - 1)) →
        (cycleGraph k).IsContained C' ∨ H'.IsContained C'ᶜ)
    (m : ℕ) (hm1 : 1 ≤ m) (W : Type) [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (h0 : ∀ v, 0 < H.degree v) (hm : H.edgeSet.ncard = m) (C : SimpleGraph (Fin ((k - 1) * m + 1))) :
    (cycleGraph k).IsContained C ∨ H.IsContained Cᶜ := by
  classical
  refine core_of_residue_connected' k hk ?_ m hm1 W H h0 hm C
  intro m' W' _ H' _ h0' hm' hm3' hstar hconn ih C' _ x hxmax hx hall hred
  have hW' : Nonempty W' := nonempty_of_ncard_edgeSet_pos H' (by omega)
  have hcard : Fintype.card W' ≤ m' + 1 := by
    have h := (⟨hconn⟩ : H'.Connected).card_vert_le_card_edgeSet_add_one
    rw [Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hm'] at h
    exact h
  by_cases hmin : ∀ v, 2 ≤ H'.degree v
  · exact hres m' W' H' hmin hm' hm3' hstar hconn ih C' x hxmax hx hall hred
  · push Not at hmin
    obtain ⟨u, hu2⟩ := hmin
    have hu : H'.degree u = 1 := by have := h0' u; omega
    have hnb : ∀ w, H'.Adj u w → 2 ≤ H'.degree w := fun w hw =>
      two_le_degree_of_adj_of_degree_one H' hconn m' hm' (by omega) u w hw hu
    have hmu : (H'.induce ({u}ᶜ : Set W')).edgeSet.ncard = m' - 1 := by
      rw [ncard_edgeSet_induce_compl_singleton, hm', hu]
    have ih' := ih (m' - 1) (by omega) _ (H'.induce ({u}ᶜ : Set W'))
      (degree_pos_induce_compl_singleton H' h0' u hnb) hmu (by omega)
    have hn : (k - 1) * (m' - 1) + 1 ≤ (k - 1) * m' + 1 := by
      have := Nat.mul_le_mul_left (k - 1) (Nat.sub_le m' 1)
      omega
    refine step_leaf k m' W' H' u hu ih' C' hn ?_
    intro y
    have h1 := hred y
    have h2 := C'.degree_compl y
    rw [Fintype.card_fin] at h2
    have h3 : (k - 2) * (Fintype.card W' - 1) ≤ (k - 2) * m' := Nat.mul_le_mul_left _ (by omega)
    have h4 : (k - 1) * m' = (k - 2) * m' + m' := by
      have : k - 1 = (k - 2) + 1 := by omega
      rw [this, Nat.add_mul, Nat.one_mul]
    omega

/-! ### The theorem for forests -/

/-- Disconnected step with the two needed instances of the induction hypothesis given directly. -/
theorem step_disconnected' (k : ℕ) (hk : 3 ≤ k) (m : ℕ) (W : Type) [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (h0 : ∀ v, 0 < H.degree v) (hm : H.edgeSet.ncard = m)
    (S : Set W) [DecidablePred (· ∈ S)] (hS : ∀ a b, H.Adj a b → (a ∈ S ↔ b ∈ S))
    (ha : ∃ a, a ∈ S) (hb : ∃ b, b ∉ S)
    (ih₁ : ∀ C'' : SimpleGraph (Fin ((k - 1) * (H.induce S).edgeSet.ncard + 1)),
      (cycleGraph k).IsContained C'' ∨ (H.induce S).IsContained C''ᶜ)
    (ih₂ : ∀ C'' : SimpleGraph (Fin ((k - 1) * (H.induce Sᶜ).edgeSet.ncard + 1)),
      (cycleGraph k).IsContained C'' ∨ (H.induce Sᶜ).IsContained C''ᶜ)
    (C : SimpleGraph (Fin ((k - 1) * m + 1))) : (cycleGraph k).IsContained C ∨ H.IsContained Cᶜ := by
  classical
  have hS' : ∀ a b, H.Adj a b → (a ∈ Sᶜ ↔ b ∈ Sᶜ) := fun a b hab => by
    rw [Set.mem_compl_iff, Set.mem_compl_iff]
    exact not_congr (hS a b hab)
  have hsum : (H.induce S).edgeSet.ncard + (H.induce Sᶜ).edgeSet.ncard = m := by
    rw [ncard_edgeSet_induce_add_compl H S hS, hm]
  have h0₁ := degree_pos_induce_closed H h0 S hS
  obtain ⟨a, haS⟩ := ha
  obtain ⟨b, hbS⟩ := hb
  have hcard₁ : Fintype.card S ≤ 2 * (H.induce S).edgeSet.ncard := card_le_two_mul_ncard_edgeSet _ h0₁
  have hle₁ : (k - 1) * (H.induce S).edgeSet.ncard + 1 ≤ (k - 1) * m + 1 := by
    have := Nat.mul_le_mul_left (k - 1) (show (H.induce S).edgeSet.ncard ≤ m by omega)
    omega
  rcases ih₁ (C.comap (Fin.castLEEmb hle₁)) with h1 | h1
  · exact Or.inl (h1.trans ⟨(Embedding.comap _ C).toCopy⟩)
  obtain ⟨f₁⟩ := h1
  have hle₁' : (C.comap (Fin.castLEEmb hle₁))ᶜ ≤ Cᶜ.comap (Fin.castLEEmb hle₁) := by
    intro p q hpq
    rw [compl_adj, comap_adj] at hpq
    rw [comap_adj, compl_adj]
    exact ⟨fun h' => hpq.1 ((Fin.castLEEmb hle₁).injective h'), hpq.2⟩
  let g₁ : Copy (H.induce S) Cᶜ :=
    (Embedding.comap (Fin.castLEEmb hle₁) Cᶜ).toCopy.comp ((Copy.ofLE _ _ hle₁').comp f₁)
  have hg₁inj : Function.Injective (fun w : S => g₁ w) := fun p q h => g₁.injective h
  have hAcard : (k - 1) * (H.induce Sᶜ).edgeSet.ncard + 1 ≤
      (Finset.univ \ Finset.univ.image (fun w : S => g₁ w)).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      Finset.card_image_of_injective _ hg₁inj, Finset.card_univ]
    have h2 : 2 * (H.induce S).edgeSet.ncard ≤ (k - 1) * (H.induce S).edgeSet.ncard :=
      Nat.mul_le_mul_right _ (by omega)
    have h3 : (k - 1) * m = (k - 1) * (H.induce S).edgeSet.ncard + (k - 1) * (H.induce Sᶜ).edgeSet.ncard := by
      rw [← hsum, Nat.mul_add]
    omega
  obtain ⟨e₂, he₂⟩ := exists_embedding_into_finset _ _ hAcard
  rcases ih₂ (C.comap e₂) with h2 | h2
  · exact Or.inl (h2.trans ⟨(Embedding.comap e₂ C).toCopy⟩)
  obtain ⟨f₂⟩ := h2
  have hle₂' : (C.comap e₂)ᶜ ≤ Cᶜ.comap e₂ := by
    intro p q hpq
    rw [compl_adj, comap_adj] at hpq
    rw [comap_adj, compl_adj]
    exact ⟨fun h' => hpq.1 (e₂.injective h'), hpq.2⟩
  let g₂ : Copy (H.induce Sᶜ) Cᶜ :=
    (Embedding.comap e₂ Cᶜ).toCopy.comp ((Copy.ofLE _ _ hle₂').comp f₂)
  have hg₂ : ∀ w, g₂ w = e₂ (f₂ w) := fun w => rfl
  right
  refine isContained_of_union H S hS Cᶜ g₁ g₂ ?_
  intro p q hpq
  have hmem := he₂ (f₂ q)
  rw [Finset.mem_sdiff] at hmem
  exact hmem.2 (Finset.mem_image.mpr ⟨p, Finset.mem_univ _, by rw [hpq, hg₂]⟩)

/-- A tree without isolated vertices and with at least one edge has a vertex of degree one. -/
theorem exists_degree_eq_one_of_isTree {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (hT : H.IsTree) (h0 : ∀ v, 0 < H.degree v) : ∃ u, H.degree u = 1 := by
  by_contra hcon
  push Not at hcon
  have h2 : ∀ v, 2 ≤ H.degree v := fun v => by have := h0 v; have := hcon v; omega
  have h1 : ∑ _w : W, 2 ≤ ∑ w : W, H.degree w := Finset.sum_le_sum (fun w _ => h2 w)
  rw [sum_degrees_eq_twice_card_edges] at h1
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at h1
  have h3 := hT.card_edgeFinset
  have h4 : 1 ≤ Fintype.card W := Fintype.card_pos_iff.mpr hT.connected.nonempty
  omega

/-- **The theorem for forests.** For every acyclic `H` with `m ≥ 1` edges and no isolated vertices, every
colouring of `K_{(k-1)m+1}` has a red `C_k` or a blue `H`. Proof by strong induction on `m` through the proved
steps: small cases and stars; an isolated edge; a disconnected forest (both parts are forests); a tree, which
has a leaf `u`: either some vertex has large red degree (`core_of_red_degree`) or every blue degree is at least
`#W - 1` and `step_leaf` applies. -/
theorem core_forest (k : ℕ) (hk : 3 ≤ k) : ∀ (m : ℕ), 1 ≤ m → ∀ (W : Type) [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj], H.IsAcyclic → (∀ v, 0 < H.degree v) → H.edgeSet.ncard = m →
    ∀ C : SimpleGraph (Fin ((k - 1) * m + 1)), (cycleGraph k).IsContained C ∨ H.IsContained Cᶜ := by
  classical
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hm1 W _ H _ hacyc h0 hm C
  by_cases hstar : ∃ v₀, ∀ a b, H.Adj a b → a = v₀ ∨ b = v₀
  · obtain ⟨v₀, hv₀⟩ := hstar
    exact core_star k hk m W H h0 hm v₀ hv₀ C
  rcases Nat.lt_or_ge m 2 with h1 | h1
  · have : m = 1 := by omega
    subst this
    exact core_one k _ (by omega) W H h0 hm C
  rcases Nat.lt_or_ge m 3 with h2 | h2
  · have : m = 2 := by omega
    subst this
    exact core_two_nonstar k hk W H h0 hm hstar C
  have hW : Nonempty W := nonempty_of_ncard_edgeSet_pos H (by omega)
  -- an isolated edge
  by_cases hiso : ∃ a b, H.Adj a b ∧ (∀ w, H.Adj a w → w = b) ∧ (∀ w, H.Adj b w → w = a)
  · obtain ⟨a, b, hab, ha, hb⟩ := hiso
    have hmab : (H.induce ({a, b}ᶜ : Set W)).edgeSet.ncard = m - 1 := by
      rw [ncard_edgeSet_induce_compl_pair H a b hab ha hb, hm]
    exact step_isolated_edge k hk m (by omega) W H a b hab ha hb
      (ih (m - 1) (by omega) (by omega) _ _ (hacyc.induce _) (degree_pos_induce_compl_pair H h0 a b ha hb)
        hmab) C
  -- disconnected
  by_cases hconn : H.Preconnected
  swap
  · unfold Preconnected at hconn
    push Not at hconn
    obtain ⟨a, b, hab⟩ := hconn
    have hS : ∀ p q, H.Adj p q → (p ∈ {w | H.Reachable a w} ↔ q ∈ {w | H.Reachable a w}) := by
      intro p q hpq
      exact ⟨fun h => h.trans hpq.reachable, fun h => h.trans hpq.symm.reachable⟩
    have hS' : ∀ p q, H.Adj p q →
        (p ∈ ({w | H.Reachable a w}ᶜ : Set W) ↔ q ∈ ({w | H.Reachable a w}ᶜ : Set W)) := fun p q hpq => by
      rw [Set.mem_compl_iff, Set.mem_compl_iff]
      exact not_congr (hS p q hpq)
    have hsum := ncard_edgeSet_induce_add_compl H {w | H.Reachable a w} hS
    rw [hm] at hsum
    have hm₁ := one_le_ncard_edgeSet_induce_closed H h0 {w | H.Reachable a w} hS a (Reachable.refl a)
    have hm₂ := one_le_ncard_edgeSet_induce_closed H h0 ({w | H.Reachable a w}ᶜ : Set W) hS' b hab
    refine step_disconnected' k hk m W H h0 hm {w | H.Reachable a w} hS ⟨a, Reachable.refl a⟩ ⟨b, hab⟩
      (ih _ (by omega) hm₁ _ _ (hacyc.induce _) (degree_pos_induce_closed H h0 _ hS) rfl)
      (ih _ (by omega) hm₂ _ _ (hacyc.induce _) (degree_pos_induce_closed H h0 _ hS') rfl) C
  -- a tree: a leaf `u` with neighbour of degree at least two
  have hT : H.IsTree := ⟨⟨hconn⟩, hacyc⟩
  obtain ⟨u, hu⟩ := exists_degree_eq_one_of_isTree H hT h0
  have hnb : ∀ w, H.Adj u w → 2 ≤ H.degree w := fun w hw =>
    two_le_degree_of_adj_of_degree_one H hconn m hm (by omega) u w hw hu
  have hmu : (H.induce ({u}ᶜ : Set W)).edgeSet.ncard = m - 1 := by
    rw [ncard_edgeSet_induce_compl_singleton, hm, hu]
  have ih' := ih (m - 1) (by omega) (by omega) _ (H.induce ({u}ᶜ : Set W)) (hacyc.induce _)
    (degree_pos_induce_compl_singleton H h0 u hnb) hmu
  have hn : (k - 1) * (m - 1) + 1 ≤ (k - 1) * m + 1 := by
    have := Nat.mul_le_mul_left (k - 1) (Nat.sub_le m 1)
    omega
  by_cases hzdeg : ∃ z, (k - 2) * (Fintype.card W - 1) + 1 ≤ C.degree z
  · obtain ⟨z, hz⟩ := hzdeg
    exact core_of_red_degree k hk H C z hz
  push Not at hzdeg
  have hcard : Fintype.card W = m + 1 := by
    have h := hT.card_edgeFinset
    rw [← coe_edgeFinset, Set.ncard_coe_finset] at hm
    omega
  refine step_leaf k m W H u hu ih' C hn ?_
  intro y
  have h1 := hzdeg y
  have h2 := C.degree_compl y
  rw [Fintype.card_fin] at h2
  have h4 : (k - 1) * m = (k - 2) * m + m := by
    have : k - 1 = (k - 2) + 1 := by omega
    rw [this, Nat.add_mul, Nat.one_mul]
  rw [hcard] at h1 ⊢
  simp only [Nat.add_sub_cancel] at h1 ⊢
  omega

/-- **Cambie–Freschi for forests.** `R(C_k, F) ≤ (k-1)m + 1` for every forest `F` with `m` edges and no isolated
vertices. -/
theorem cambie_freschi_of_isAcyclic (k : ℕ) (hk : 3 ≤ k) (m : ℕ) (W : Type) [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (hacyc : H.IsAcyclic) (h0 : ∀ v, 0 < H.degree v) (hm : H.edgeSet.ncard = m) :
    SimpleGraph.graphRamsey (SimpleGraph.cycleGraph k) H ≤ (k - 1) * m + 1 := by
  apply graphRamsey_le_of_forall
  intro C
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h
    have := isEmpty_of_ncard_edgeSet_eq_zero H h0 hm
    exact Or.inr IsContained.of_isEmpty
  · exact core_forest k hk m h W H hacyc h0 hm C


/-! ### The residue, final form -/

/-- If `H` is not contained in `G`, no copy of `H - u` extends: for every vertex `y` outside the copy some
neighbour of `u` has image not adjacent to `y`. -/
theorem exists_not_adj_of_not_isContained {W V : Type*} [DecidableEq W] (H : SimpleGraph W) (G : SimpleGraph V)
    (hH : ¬ H.IsContained G) (u : W) (f : Copy (H.induce ({u}ᶜ : Set W)) G) (y : V) (hy : ∀ w, f w ≠ y) :
    ∃ w : ({u}ᶜ : Set W), H.Adj u w ∧ ¬ G.Adj y (f w) := by
  by_contra hcon
  push Not at hcon
  exact hH (isContained_of_extend H u G f y hy hcon)

/-- If `H` is not contained in `G`, every copy of `H - uv` has the images of `u` and `v` non-adjacent. -/
theorem not_adj_of_not_isContained {W V : Type*} (H : SimpleGraph W) (G : SimpleGraph V) (hH : ¬ H.IsContained G)
    (u v : W) (f : Copy (H.deleteEdges {s(u, v)}) G) : ¬ G.Adj (f u) (f v) :=
  fun h => hH (isContained_of_deleteEdges_adj H u v G f h)

/-- **Reduction, final form.** The forced statement follows from the impossibility of the following
configuration: a connected `H'` with `m' ≥ 3` edges and minimum degree at least two whose maximum degree
satisfies `(k-1)Δ ≤ (k-2)(#W'-1)`; the induction hypothesis for all graphs with fewer edges; a colouring of
`K_{(k-1)m'+1}` in which every red degree is at most `(k-2)(#W'-1)`, the maximum blue degree `D` (at `x`)
satisfies `m' ≤ D < (k-1)(m' - deg v) + 1` for every `v`, no blue copy of any `H' - u` extends, and every blue
copy of any `H' - uv` has `f u f v` red; and in which there is no red `C_k`. -/
theorem core_of_residue_final (k : ℕ) (hk : 3 ≤ k)
    (hres : ∀ (m' : ℕ) (W' : Type) [Fintype W'] (H' : SimpleGraph W') [DecidableRel H'.Adj],
      (∀ v, 2 ≤ H'.degree v) → H'.edgeSet.ncard = m' → 3 ≤ m' →
      (¬ ∃ v₀, ∀ a b, H'.Adj a b → a = v₀ ∨ b = v₀) → H'.Preconnected →
      (∀ v, (k - 1) * H'.degree v ≤ (k - 2) * (Fintype.card W' - 1)) →
      (∀ m'' < m', ∀ (W'' : Type) [Fintype W''] (H'' : SimpleGraph W'') [DecidableRel H''.Adj],
        (∀ v, 0 < H''.degree v) → H''.edgeSet.ncard = m'' → 1 ≤ m'' →
        ∀ C'' : SimpleGraph (Fin ((k - 1) * m'' + 1)),
          (cycleGraph k).IsContained C'' ∨ H''.IsContained C''ᶜ) →
      ∀ (C' : SimpleGraph (Fin ((k - 1) * m' + 1))) [DecidableRel C'.Adj] (x : Fin ((k - 1) * m' + 1)),
        (∀ y, C'ᶜ.degree y ≤ C'ᶜ.degree x) → m' ≤ C'ᶜ.degree x →
        (∀ v, C'ᶜ.degree x < (k - 1) * (m' - H'.degree v) + 1) →
        (∀ z, C'.degree z ≤ (k - 2) * (Fintype.card W' - 1)) →
        (∀ (u : W') (f : Copy (H'.induce ({u}ᶜ : Set W')) C'ᶜ) (y : Fin ((k - 1) * m' + 1)),
          (∀ w, f w ≠ y) → ∃ w : ({u}ᶜ : Set W'), H'.Adj u w ∧ ¬ C'ᶜ.Adj y (f w)) →
        (∀ (u v : W') (f : Copy (H'.deleteEdges {s(u, v)}) C'ᶜ), C'.Adj (f u) (f v)) →
        ¬ (cycleGraph k).IsContained C' → False)
    (m : ℕ) (hm1 : 1 ≤ m) (W : Type) [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (h0 : ∀ v, 0 < H.degree v) (hm : H.edgeSet.ncard = m) (C : SimpleGraph (Fin ((k - 1) * m + 1))) :
    (cycleGraph k).IsContained C ∨ H.IsContained Cᶜ := by
  classical
  refine core_of_residue_connected'' k hk ?_ m hm1 W H h0 hm C
  intro m' W' _ H' _ h2' hm' hm3' hstar hconn ih C' _ x hxmax hx hall hred
  by_cases hblue : H'.IsContained C'ᶜ
  · exact Or.inr hblue
  by_cases hredC : (cycleGraph k).IsContained C'
  · exact Or.inl hredC
  exfalso
  have hmax : ∀ v, (k - 1) * H'.degree v ≤ (k - 2) * (Fintype.card W' - 1) := by
    intro v
    have h1 := hall v
    have h2 := hred x
    have h3 := C'.degree_compl x
    rw [Fintype.card_fin] at h3
    have h4 : H'.degree v ≤ m' := (degree_lt_ncard_of_not_star H' m' hm' hstar v).le
    have h5 : (k - 1) * m' = (k - 1) * (m' - H'.degree v) + (k - 1) * H'.degree v := by
      rw [← Nat.mul_add, Nat.sub_add_cancel h4]
    omega
  have hnoedge : ∀ (u v : W') (f : Copy (H'.deleteEdges {s(u, v)}) C'ᶜ), C'.Adj (f u) (f v) := by
    intro u v f
    have h := not_adj_of_not_isContained H' C'ᶜ hblue u v f
    rw [compl_adj, not_and, not_not] at h
    by_cases huv : u = v
    · subst huv
      exfalso
      apply hblue
      have hle : H' ≤ H'.deleteEdges {s(u, u)} := by
        intro a b hab
        rw [deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_iff]
        exact ⟨hab, by rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> exact hab.ne rfl⟩
      exact ⟨f.comp (Copy.ofLE _ _ hle)⟩
    · exact h (f.injective.ne huv)
  exact hres m' W' H' h2' hm' hm3' hstar hconn hmax ih C' x hxmax hx hall hred
    (fun u f y hy => exists_not_adj_of_not_isContained H' C'ᶜ hblue u f y hy) hnoedge hredC

/-! ### Route I: the residue is empty for `k = 4` -/

/-- Pigeonhole for a covering: if every `y ∈ Y` is red to the image of some neighbour of `u`, and
`deg u * t < #Y`, some neighbour `w` of `u` has its image red to more than `t` vertices of `Y`. -/
theorem exists_many_red_of_cover {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
    (H : SimpleGraph W) [DecidableRel H.Adj] (C : SimpleGraph V) [DecidableRel C.Adj] (u : W)
    (hu : 0 < H.degree u) (Y : Finset V) (g : ({u}ᶜ : Set W) → V)
    (hcover : ∀ y ∈ Y, ∃ w : ({u}ᶜ : Set W), H.Adj u w ∧ C.Adj y (g w)) (t : ℕ)
    (hY : H.degree u * t < Y.card) :
    ∃ w : ({u}ᶜ : Set W), H.Adj u w ∧ t < (Y.filter (fun y => C.Adj y (g w))).card := by
  classical
  set Nu : Finset ({u}ᶜ : Set W) := Finset.univ.filter (fun w => H.Adj u w) with hNu
  have hNucard : Nu.card = H.degree u := by
    rw [← card_neighborFinset_eq_degree]
    have : Nu.map (Function.Embedding.subtype _) = H.neighborFinset u := by
      ext w
      simp only [Finset.mem_map, Function.Embedding.coe_subtype, hNu, Finset.mem_filter, Finset.mem_univ,
        true_and, mem_neighborFinset]
      constructor
      · rintro ⟨w', hw', rfl⟩
        exact hw'
      · intro hw
        exact ⟨⟨w, by simpa using hw.ne.symm⟩, hw, rfl⟩
    rw [← this, Finset.card_map]
  have hNune : Nu.Nonempty := by
    rw [← Finset.card_pos, hNucard]
    exact hu
  obtain ⟨w₀, -⟩ := hNune
  let φ : V → ({u}ᶜ : Set W) := fun y => if h : ∃ w ∈ Nu, C.Adj y (g w) then h.choose else w₀
  have hφ : ∀ y ∈ Y, φ y ∈ Nu ∧ C.Adj y (g (φ y)) := by
    intro y hy
    obtain ⟨w, hw, hyw⟩ := hcover y hy
    have hex : ∃ w ∈ Nu, C.Adj y (g w) :=
      ⟨w, by rw [hNu, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hw⟩, hyw⟩
    simp only [φ, dite_eq_left hex]
    exact hex.choose_spec
  obtain ⟨z₀, hz₀, hfib⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to (s := Y) (t := Nu)
    (f := φ) (n := t) (fun y hy => (hφ y hy).1) (by rw [hNucard]; exact hY)
  refine ⟨z₀, by rw [hNu, Finset.mem_filter] at hz₀; exact hz₀.2, lt_of_lt_of_le hfib ?_⟩
  apply Finset.card_le_card
  intro y hy
  rw [Finset.mem_filter] at hy ⊢
  refine ⟨hy.1, ?_⟩
  have := (hφ y hy.1).2
  rw [hy.2] at this
  exact this

/-- **The residue is empty for `k = 4`.** -/
theorem residue_four (k : ℕ) (hk4 : k = 4) (m' : ℕ) (W' : Type) [Fintype W'] (H' : SimpleGraph W')
    [DecidableRel H'.Adj] (h2' : ∀ v, 2 ≤ H'.degree v) (hm' : H'.edgeSet.ncard = m') (hm3' : 3 ≤ m')
    (hstar : ¬ ∃ v₀, ∀ a b, H'.Adj a b → a = v₀ ∨ b = v₀)
    (ih : ∀ m'' < m', ∀ (W'' : Type) [Fintype W''] (H'' : SimpleGraph W'') [DecidableRel H''.Adj],
      (∀ v, 0 < H''.degree v) → H''.edgeSet.ncard = m'' → 1 ≤ m'' →
      ∀ C'' : SimpleGraph (Fin ((k - 1) * m'' + 1)), (cycleGraph k).IsContained C'' ∨ H''.IsContained C''ᶜ)
    (C' : SimpleGraph (Fin ((k - 1) * m' + 1))) [DecidableRel C'.Adj] (x : Fin ((k - 1) * m' + 1))
    (hall : ∀ v, C'ᶜ.degree x < (k - 1) * (m' - H'.degree v) + 1)
    (hnoext : ∀ (u : W') (f : Copy (H'.induce ({u}ᶜ : Set W')) C'ᶜ) (y : Fin ((k - 1) * m' + 1)),
      (∀ w, f w ≠ y) → ∃ w : ({u}ᶜ : Set W'), H'.Adj u w ∧ ¬ C'ᶜ.Adj y (f w))
    (hredC : ¬ (cycleGraph k).IsContained C') : False := by
  classical
  have hW' : Nonempty W' := nonempty_of_ncard_edgeSet_pos H' (by omega)
  obtain ⟨u, hu⟩ := exists_max_degree H'
  have hu2 := h2' u
  have hult : H'.degree u < m' := degree_lt_ncard_of_not_star H' m' hm' hstar u
  have h0' : ∀ w, 0 < H'.degree w := fun w => by have := h2' w; omega
  have hmu : (H'.induce ({u}ᶜ : Set W')).edgeSet.ncard = m' - H'.degree u := by
    rw [ncard_edgeSet_induce_compl_singleton, hm']
  have ih' := ih (m' - H'.degree u) (by omega) _ (H'.induce ({u}ᶜ : Set W'))
    (degree_pos_induce_compl_singleton H' h0' u (fun w _ => h2' w)) hmu (by omega)
  have h5 : (k - 1) * m' = (k - 1) * (m' - H'.degree u) + (k - 1) * H'.degree u := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hult.le]
  -- the red neighbourhood of `x` has at least `(k-1)Δ` vertices
  have hxred : (k - 1) * H'.degree u ≤ (C'.neighborFinset x).card := by
    rw [card_neighborFinset_eq_degree]
    have h1 := hall u
    have h3 := C'.degree_compl x
    rw [Fintype.card_fin] at h3
    omega
  obtain ⟨Y, hYsub, hYcard⟩ := Finset.exists_subset_card_eq
    (show (k - 1) * H'.degree u - 1 ≤ (C'.neighborFinset x).card by omega)
  have hxY : x ∉ Y := fun h => by
    have := hYsub h
    rw [mem_neighborFinset] at this
    exact this.ne rfl
  have hScard : (k - 1) * (m' - H'.degree u) + 1 ≤ (Finset.univ \ insert x Y).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      Finset.card_insert_of_notMem hxY, hYcard]
    have : 1 ≤ (k - 1) * H'.degree u := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    omega
  obtain ⟨e, he⟩ := exists_embedding_into_finset _ _ hScard
  rcases ih' (C'.comap e) with h1 | h1
  · exact hredC (h1.trans ⟨(Embedding.comap e C').toCopy⟩)
  obtain ⟨f⟩ := h1
  have hle : (C'.comap e)ᶜ ≤ C'ᶜ.comap e := by
    intro a b hab
    rw [compl_adj, comap_adj] at hab
    rw [comap_adj, compl_adj]
    exact ⟨fun h' => hab.1 (e.injective h'), hab.2⟩
  let g : Copy (H'.induce ({u}ᶜ : Set W')) C'ᶜ :=
    (Embedding.comap e C'ᶜ).toCopy.comp ((Copy.ofLE _ _ hle).comp f)
  have hg : ∀ w, g w = e (f w) := fun w => rfl
  have hgS : ∀ w, g w ∉ insert x Y := fun w hw => by
    have := he (f w)
    rw [Finset.mem_sdiff] at this
    exact this.2 (hg w ▸ hw)
  have hgY : ∀ w, g w ∉ Y := fun w hw => hgS w (Finset.mem_insert_of_mem hw)
  have hgx : ∀ w, g w ≠ x := fun w hw => hgS w (Finset.mem_insert.mpr (Or.inl hw))
  have hcover : ∀ y ∈ Y, ∃ w : ({u}ᶜ : Set W'), H'.Adj u w ∧ C'.Adj y (g w) := by
    intro y hy
    obtain ⟨w, hw, hred'⟩ := hnoext u g y (fun w h => hgY w (h ▸ hy))
    refine ⟨w, hw, ?_⟩
    rw [compl_adj, not_and, not_not] at hred'
    exact hred' (fun h => hgY w (h ▸ hy))
  obtain ⟨w, -, hw⟩ := exists_many_red_of_cover H' C' u (by omega) Y (fun w : ({u}ᶜ : Set W') => g w) hcover
    (k - 2) (by subst hk4; omega)
  -- two distinct vertices of `Y` red to `z := g w`
  obtain ⟨y₁, hy₁, y₂, hy₂, hne⟩ := Finset.one_lt_card.mp (by subst hk4; omega : 1 < (Y.filter (fun y => C'.Adj y (g w))).card)
  rw [Finset.mem_filter] at hy₁ hy₂
  have hxy₁ : C'.Adj x y₁ := (mem_neighborFinset _ _ _).mp (hYsub hy₁.1)
  have hxy₂ : C'.Adj x y₂ := (mem_neighborFinset _ _ _).mp (hYsub hy₂.1)
  -- the red path `y₁ x y₂` with apex `g w` is a red `C_4`
  apply hredC
  have hpath : (Walk.cons hxy₁.symm (Walk.cons hxy₂ Walk.nil) : C'.Walk y₁ y₂).IsPath := by
    rw [Walk.cons_isPath_iff, Walk.cons_isPath_iff]
    refine ⟨⟨Walk.IsPath.nil, ?_⟩, ?_⟩
    · intro h
      simp only [Walk.support_nil, List.mem_singleton] at h
      exact hxY (h ▸ hy₂.1)
    · intro h
      simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h
      · exact hxY (h ▸ hy₁.1)
      · exact hne h
  refine cycleGraph_isContained_of_isPath_apex C' k (by omega) _ hpath (by subst hk4; rfl) (g w) ?_
    hy₁.2.symm hy₂.2
  intro h
  simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h
  · exact hgY w (h ▸ hy₁.1)
  · exact hgx w h
  · exact hgY w (h ▸ hy₂.1)

/-- **The core for `k = 4`**, for every `H` with `m ≥ 1` edges and no isolated vertices. -/
theorem core_four (m : ℕ) (hm1 : 1 ≤ m) (W : Type) [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (h0 : ∀ v, 0 < H.degree v) (hm : H.edgeSet.ncard = m) (C : SimpleGraph (Fin ((4 - 1) * m + 1))) :
    (cycleGraph 4).IsContained C ∨ H.IsContained Cᶜ :=
  core_of_residue_final 4 (by norm_num)
    (fun m' W' _ H' _ h2' hm' hm3' hstar _ _ ih C' _ x _ _ hall _ hnoext _ hredC =>
      residue_four 4 rfl m' W' H' h2' hm' hm3' hstar ih C' x hall hnoext hredC) m hm1 W H h0 hm C

/-- **Cambie–Freschi for `k = 4`.** `R(C_4, H) ≤ 3m + 1` for every `H` with `m` edges and no isolated
vertices. -/
theorem cambie_freschi_four (m : ℕ) (W : Type) [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (h0 : ∀ v, 0 < H.degree v) (hm : H.edgeSet.ncard = m) :
    SimpleGraph.graphRamsey (SimpleGraph.cycleGraph 4) H ≤ 3 * m + 1 := by
  apply graphRamsey_le_of_forall
  intro C
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h
    have := isEmpty_of_ncard_edgeSet_eq_zero H h0 hm
    exact Or.inr IsContained.of_isEmpty
  · exact core_four m h W H h0 hm C

/-- **Common red neighbours.** In the residue, for every vertex `x'` of red degree at least `(k-1)Δ` (where
`Δ = deg u ≥ 2` for a vertex `u` of `H'`), there is a vertex `z ≠ x'` with at least `k - 1` common red
neighbours: embed `H' - u` by the IH in the complement of `x'` and of a set `Y ⊆ N_red(x')` of size
`(k-1)Δ - 1`; no copy extends, so `Y` is covered by the red neighbourhoods of the `Δ` images of `N(u)`, and
one of them is red to more than `k - 2` vertices of `Y`. -/
theorem exists_common_red_of_residue (k : ℕ) (hk : 3 ≤ k) (m' : ℕ) (W' : Type) [Fintype W']
    (H' : SimpleGraph W') [DecidableRel H'.Adj] (h2' : ∀ v, 2 ≤ H'.degree v) (hm' : H'.edgeSet.ncard = m')
    (hstar : ¬ ∃ v₀, ∀ a b, H'.Adj a b → a = v₀ ∨ b = v₀)
    (ih : ∀ m'' < m', ∀ (W'' : Type) [Fintype W''] (H'' : SimpleGraph W'') [DecidableRel H''.Adj],
      (∀ v, 0 < H''.degree v) → H''.edgeSet.ncard = m'' → 1 ≤ m'' →
      ∀ C'' : SimpleGraph (Fin ((k - 1) * m'' + 1)), (cycleGraph k).IsContained C'' ∨ H''.IsContained C''ᶜ)
    (C' : SimpleGraph (Fin ((k - 1) * m' + 1))) [DecidableRel C'.Adj]
    (hnoext : ∀ (u : W') (f : Copy (H'.induce ({u}ᶜ : Set W')) C'ᶜ) (y : Fin ((k - 1) * m' + 1)),
      (∀ w, f w ≠ y) → ∃ w : ({u}ᶜ : Set W'), H'.Adj u w ∧ ¬ C'ᶜ.Adj y (f w))
    (hredC : ¬ (cycleGraph k).IsContained C') (u : W') (x' : Fin ((k - 1) * m' + 1))
    (hx' : (k - 1) * H'.degree u ≤ C'.degree x') :
    ∃ z, z ≠ x' ∧ k - 2 < ((C'.neighborFinset x').filter (fun y => C'.Adj y z)).card := by
  classical
  have hu2 := h2' u
  have hult : H'.degree u < m' := degree_lt_ncard_of_not_star H' m' hm' hstar u
  have h0' : ∀ w, 0 < H'.degree w := fun w => by have := h2' w; omega
  have hmu : (H'.induce ({u}ᶜ : Set W')).edgeSet.ncard = m' - H'.degree u := by
    rw [ncard_edgeSet_induce_compl_singleton, hm']
  have ih' := ih (m' - H'.degree u) (by omega) _ (H'.induce ({u}ᶜ : Set W'))
    (degree_pos_induce_compl_singleton H' h0' u (fun w _ => h2' w)) hmu (by omega)
  have h5 : (k - 1) * m' = (k - 1) * (m' - H'.degree u) + (k - 1) * H'.degree u := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hult.le]
  have hxred : (k - 1) * H'.degree u ≤ (C'.neighborFinset x').card := by
    rw [card_neighborFinset_eq_degree]; exact hx'
  obtain ⟨Y, hYsub, hYcard⟩ := Finset.exists_subset_card_eq
    (show (k - 1) * H'.degree u - 1 ≤ (C'.neighborFinset x').card by omega)
  have hxY : x' ∉ Y := fun h => by
    have := hYsub h
    rw [mem_neighborFinset] at this
    exact this.ne rfl
  have hScard : (k - 1) * (m' - H'.degree u) + 1 ≤ (Finset.univ \ insert x' Y).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      Finset.card_insert_of_notMem hxY, hYcard]
    have : 1 ≤ (k - 1) * H'.degree u := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    omega
  obtain ⟨e, he⟩ := exists_embedding_into_finset _ _ hScard
  rcases ih' (C'.comap e) with h1 | h1
  · exact (hredC (h1.trans ⟨(Embedding.comap e C').toCopy⟩)).elim
  obtain ⟨f⟩ := h1
  have hle : (C'.comap e)ᶜ ≤ C'ᶜ.comap e := by
    intro a b hab
    rw [compl_adj, comap_adj] at hab
    rw [comap_adj, compl_adj]
    exact ⟨fun h' => hab.1 (e.injective h'), hab.2⟩
  let g : Copy (H'.induce ({u}ᶜ : Set W')) C'ᶜ :=
    (Embedding.comap e C'ᶜ).toCopy.comp ((Copy.ofLE _ _ hle).comp f)
  have hg : ∀ w, g w = e (f w) := fun w => rfl
  have hgS : ∀ w, g w ∉ insert x' Y := fun w hw => by
    have := he (f w)
    rw [Finset.mem_sdiff] at this
    exact this.2 (hg w ▸ hw)
  have hgY : ∀ w, g w ∉ Y := fun w hw => hgS w (Finset.mem_insert_of_mem hw)
  have hgx : ∀ w, g w ≠ x' := fun w hw => hgS w (Finset.mem_insert.mpr (Or.inl hw))
  have hcover : ∀ y ∈ Y, ∃ w : ({u}ᶜ : Set W'), H'.Adj u w ∧ C'.Adj y (g w) := by
    intro y hy
    obtain ⟨w, hw, hred'⟩ := hnoext u g y (fun w h => hgY w (h ▸ hy))
    refine ⟨w, hw, ?_⟩
    rw [compl_adj, not_and, not_not] at hred'
    exact hred' (fun h => hgY w (h ▸ hy))
  obtain ⟨w, -, hw⟩ := exists_many_red_of_cover H' C' u (by omega) Y (fun w : ({u}ᶜ : Set W') => g w) hcover
    (k - 2) (by
      rw [hYcard]
      have h : k - 1 = k - 2 + 1 := by omega
      rw [h, Nat.add_mul, Nat.one_mul, Nat.mul_comm (k - 2)]
      omega)
  refine ⟨g w, hgx w, lt_of_lt_of_le hw ?_⟩
  apply Finset.card_le_card
  intro y hy
  rw [Finset.mem_filter] at hy ⊢
  exact ⟨hYsub hy.1, hy.2⟩

/-- **Reduction, with common red neighbours and `k ≠ 4`.** -/
theorem core_of_residue_final' (k : ℕ) (hk : 3 ≤ k)
    (hres : ∀ (m' : ℕ) (W' : Type) [Fintype W'] (H' : SimpleGraph W') [DecidableRel H'.Adj],
      (∀ v, 2 ≤ H'.degree v) → H'.edgeSet.ncard = m' → 3 ≤ m' →
      (¬ ∃ v₀, ∀ a b, H'.Adj a b → a = v₀ ∨ b = v₀) → H'.Preconnected →
      (∀ v, (k - 1) * H'.degree v ≤ (k - 2) * (Fintype.card W' - 1)) →
      (∀ m'' < m', ∀ (W'' : Type) [Fintype W''] (H'' : SimpleGraph W'') [DecidableRel H''.Adj],
        (∀ v, 0 < H''.degree v) → H''.edgeSet.ncard = m'' → 1 ≤ m'' →
        ∀ C'' : SimpleGraph (Fin ((k - 1) * m'' + 1)),
          (cycleGraph k).IsContained C'' ∨ H''.IsContained C''ᶜ) →
      ∀ (C' : SimpleGraph (Fin ((k - 1) * m' + 1))) [DecidableRel C'.Adj] (x : Fin ((k - 1) * m' + 1)),
        (∀ y, C'ᶜ.degree y ≤ C'ᶜ.degree x) → m' ≤ C'ᶜ.degree x →
        (∀ v, C'ᶜ.degree x < (k - 1) * (m' - H'.degree v) + 1) →
        (∀ z, C'.degree z ≤ (k - 2) * (Fintype.card W' - 1)) →
        (∀ (u : W') (f : Copy (H'.induce ({u}ᶜ : Set W')) C'ᶜ) (y : Fin ((k - 1) * m' + 1)),
          (∀ w, f w ≠ y) → ∃ w : ({u}ᶜ : Set W'), H'.Adj u w ∧ ¬ C'ᶜ.Adj y (f w)) →
        (∀ (u v : W') (f : Copy (H'.deleteEdges {s(u, v)}) C'ᶜ), C'.Adj (f u) (f v)) →
        ¬ (cycleGraph k).IsContained C' → k ≠ 4 →
        (∀ x' : Fin ((k - 1) * m' + 1), ∃ z, z ≠ x' ∧
          k - 2 < ((C'.neighborFinset x').filter (fun y => C'.Adj y z)).card) → False)
    (m : ℕ) (hm1 : 1 ≤ m) (W : Type) [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (h0 : ∀ v, 0 < H.degree v) (hm : H.edgeSet.ncard = m) (C : SimpleGraph (Fin ((k - 1) * m + 1))) :
    (cycleGraph k).IsContained C ∨ H.IsContained Cᶜ := by
  classical
  refine core_of_residue_final k hk ?_ m hm1 W H h0 hm C
  intro m' W' _ H' _ h2' hm' hm3' hstar hconn hmax ih C' _ x hxmax hx hall hred hnoext hnoedge hredC
  by_cases hk4 : k = 4
  · exact residue_four k hk4 m' W' H' h2' hm' hm3' hstar ih C' x hall hnoext hredC
  have hW' : Nonempty W' := nonempty_of_ncard_edgeSet_pos H' (by omega)
  obtain ⟨u, hu⟩ := exists_max_degree H'
  have hult : H'.degree u < m' := degree_lt_ncard_of_not_star H' m' hm' hstar u
  have h5 : (k - 1) * m' = (k - 1) * (m' - H'.degree u) + (k - 1) * H'.degree u := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hult.le]
  refine hres m' W' H' h2' hm' hm3' hstar hconn hmax ih C' x hxmax hx hall hred hnoext hnoedge hredC hk4 ?_
  intro x'
  refine exists_common_red_of_residue k hk m' W' H' h2' hm' hstar ih C' hnoext hredC u x' ?_
  have h1 := hall u
  have h2 := hxmax x'
  have h3 := C'.degree_compl x'
  rw [Fintype.card_fin] at h3
  omega

/-! ### Conditional closures of the residue -/

/-- **`k = 5`, conditional.** If `x ≠ z` have three common red neighbours `y₁, y₂, y₃` with `y₁ y₂` red,
there is a red `C_5`: `y₃ x y₁ y₂` is a red path with apex `z`. -/
theorem cycleGraph_five_of_common_red_edge {V : Type*} (C : SimpleGraph V) (x z y₁ y₂ y₃ : V)
    (hxz : x ≠ z) (hxy₁ : C.Adj x y₁) (hxy₂ : C.Adj x y₂) (hxy₃ : C.Adj x y₃) (hzy₁ : C.Adj z y₁)
    (hzy₂ : C.Adj z y₂) (hzy₃ : C.Adj z y₃) (h12 : C.Adj y₁ y₂) (h13 : y₁ ≠ y₃) (h23 : y₂ ≠ y₃) :
    (cycleGraph 5).IsContained C := by
  have hpath : (Walk.cons hxy₃.symm (Walk.cons hxy₁ (Walk.cons h12 Walk.nil)) : C.Walk y₃ y₂).IsPath := by
    rw [Walk.cons_isPath_iff, Walk.cons_isPath_iff, Walk.cons_isPath_iff]
    refine ⟨⟨⟨Walk.IsPath.nil, ?_⟩, ?_⟩, ?_⟩
    · intro h
      simp only [Walk.support_nil, List.mem_singleton] at h
      exact h12.ne h
    · intro h
      simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h
      · exact hxy₁.ne h
      · exact hxy₂.ne h
    · intro h
      simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h
      · exact hxy₃.ne h.symm
      · exact h13 h.symm
      · exact h23 h.symm
  refine cycleGraph_isContained_of_isPath_apex C 5 (by norm_num) _ hpath rfl z ?_ hzy₃ hzy₂.symm
  intro h
  simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h
  · exact hzy₃.ne h
  · exact hxz h.symm
  · exact hzy₁.ne h
  · exact hzy₂.ne h

/-- **Red colourable, conditional.** If the red graph is `c`-colourable and `c (#W - 1) < #V`, some colour
class is a blue clique on at least `#W` vertices, so `H` embeds in blue. In the residue (`c = k - 1`) this says
the red graph is not `(k-1)`-colourable. -/
theorem isContained_of_red_colorable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] (H : SimpleGraph W)
    (C : SimpleGraph V) (c : ℕ) (hcol : C.Colorable c) (hcard : c * (Fintype.card W - 1) < Fintype.card V) :
    H.IsContained Cᶜ := by
  classical
  obtain ⟨f⟩ := hcol
  obtain ⟨i, -, hi⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to (s := (Finset.univ : Finset V))
    (t := (Finset.univ : Finset (Fin c))) (f := f) (n := Fintype.card W - 1) (fun _ _ => Finset.mem_univ _)
    (by rw [Finset.card_univ, Finset.card_univ, Fintype.card_fin]; exact hcard)
  refine isContained_of_isClique_card_le H Cᶜ (Finset.univ.filter (fun v => f v = i)) ?_ ?_
  · intro v hv w hw hvw
    rw [Finset.mem_coe, Finset.mem_filter] at hv hw
    rw [compl_adj]
    refine ⟨hvw, fun hadj => f.valid hadj ?_⟩
    rw [hv.2, hw.2]
  · rcases Nat.eq_zero_or_pos (Fintype.card W) with h | h
    · rw [h]
      exact Nat.zero_le _
    · omega

/-- **`k = 6`, conditional.** Three pairwise distinct vertices `x, z, z'` with three common red neighbours give
a red `C_6`: the red path `y₃ x y₁ z y₂` with apex `z'`. -/
theorem cycleGraph_six_of_three_apexes {V : Type*} (C : SimpleGraph V) (x z z' y₁ y₂ y₃ : V)
    (hxz : x ≠ z) (hxz' : x ≠ z') (hzz' : z ≠ z')
    (hxy₁ : C.Adj x y₁) (hxy₂ : C.Adj x y₂) (hxy₃ : C.Adj x y₃)
    (hzy₁ : C.Adj z y₁) (hzy₂ : C.Adj z y₂) (hzy₃ : C.Adj z y₃)
    (hz'y₁ : C.Adj z' y₁) (hz'y₂ : C.Adj z' y₂) (hz'y₃ : C.Adj z' y₃)
    (h12 : y₁ ≠ y₂) (h13 : y₁ ≠ y₃) (h23 : y₂ ≠ y₃) : (cycleGraph 6).IsContained C := by
  have hpath : (Walk.cons hxy₃.symm (Walk.cons hxy₁ (Walk.cons hzy₁.symm (Walk.cons hzy₂ Walk.nil))) :
      C.Walk y₃ y₂).IsPath := by
    rw [Walk.cons_isPath_iff, Walk.cons_isPath_iff, Walk.cons_isPath_iff, Walk.cons_isPath_iff]
    refine ⟨⟨⟨⟨Walk.IsPath.nil, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · intro h
      simp only [Walk.support_nil, List.mem_singleton] at h
      exact hzy₂.ne h
    · intro h
      simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h
      · exact hzy₁.ne h.symm
      · exact h12 h
    · intro h
      simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h
      · exact hxy₁.ne h
      · exact hxz h
      · exact hxy₂.ne h
    · intro h
      simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h | h
      · exact hxy₃.ne h.symm
      · exact h13 h.symm
      · exact hzy₃.ne h.symm
      · exact h23 h.symm
  refine cycleGraph_isContained_of_isPath_apex C 6 (by norm_num) _ hpath rfl z' ?_ hz'y₃ hz'y₂.symm
  intro h
  simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h
  · exact hz'y₃.ne h
  · exact hxz' h.symm
  · exact hz'y₁.ne h
  · exact hzz' h.symm
  · exact hz'y₂.ne h

/-- **Reduction, with non-colourability.** In the residue the red graph is not `(k-1)`-colourable. -/
theorem core_of_residue_final'' (k : ℕ) (hk : 3 ≤ k)
    (hres : ∀ (m' : ℕ) (W' : Type) [Fintype W'] (H' : SimpleGraph W') [DecidableRel H'.Adj],
      (∀ v, 2 ≤ H'.degree v) → H'.edgeSet.ncard = m' → 3 ≤ m' →
      (¬ ∃ v₀, ∀ a b, H'.Adj a b → a = v₀ ∨ b = v₀) → H'.Preconnected →
      (∀ v, (k - 1) * H'.degree v ≤ (k - 2) * (Fintype.card W' - 1)) →
      (∀ m'' < m', ∀ (W'' : Type) [Fintype W''] (H'' : SimpleGraph W'') [DecidableRel H''.Adj],
        (∀ v, 0 < H''.degree v) → H''.edgeSet.ncard = m'' → 1 ≤ m'' →
        ∀ C'' : SimpleGraph (Fin ((k - 1) * m'' + 1)),
          (cycleGraph k).IsContained C'' ∨ H''.IsContained C''ᶜ) →
      ∀ (C' : SimpleGraph (Fin ((k - 1) * m' + 1))) [DecidableRel C'.Adj] (x : Fin ((k - 1) * m' + 1)),
        (∀ y, C'ᶜ.degree y ≤ C'ᶜ.degree x) → m' ≤ C'ᶜ.degree x →
        (∀ v, C'ᶜ.degree x < (k - 1) * (m' - H'.degree v) + 1) →
        (∀ z, C'.degree z ≤ (k - 2) * (Fintype.card W' - 1)) →
        (∀ (u : W') (f : Copy (H'.induce ({u}ᶜ : Set W')) C'ᶜ) (y : Fin ((k - 1) * m' + 1)),
          (∀ w, f w ≠ y) → ∃ w : ({u}ᶜ : Set W'), H'.Adj u w ∧ ¬ C'ᶜ.Adj y (f w)) →
        (∀ (u v : W') (f : Copy (H'.deleteEdges {s(u, v)}) C'ᶜ), C'.Adj (f u) (f v)) →
        ¬ (cycleGraph k).IsContained C' → k ≠ 4 →
        (∀ x' : Fin ((k - 1) * m' + 1), ∃ z, z ≠ x' ∧
          k - 2 < ((C'.neighborFinset x').filter (fun y => C'.Adj y z)).card) →
        ¬ C'.Colorable (k - 1) → False)
    (m : ℕ) (hm1 : 1 ≤ m) (W : Type) [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (h0 : ∀ v, 0 < H.degree v) (hm : H.edgeSet.ncard = m) (C : SimpleGraph (Fin ((k - 1) * m + 1))) :
    (cycleGraph k).IsContained C ∨ H.IsContained Cᶜ := by
  classical
  refine core_of_residue_final' k hk ?_ m hm1 W H h0 hm C
  intro m' W' _ H' _ h2' hm' hm3' hstar hconn hmax ih C' _ x hxmax hx hall hred hnoext hnoedge hredC hk4 hK2
  by_cases hcol : C'.Colorable (k - 1)
  · have hW' : Nonempty W' := nonempty_of_ncard_edgeSet_pos H' (by omega)
    have hcard : Fintype.card W' ≤ m' + 1 := by
      have h := (⟨hconn⟩ : H'.Connected).card_vert_le_card_edgeSet_add_one
      rw [Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hm'] at h
      exact h
    have hblue : H'.IsContained C'ᶜ := by
      refine isContained_of_red_colorable H' C' (k - 1) hcol ?_
      rw [Fintype.card_fin]
      have : (k - 1) * (Fintype.card W' - 1) ≤ (k - 1) * m' := Nat.mul_le_mul_left _ (by omega)
      omega
    -- but no copy of `H' - u` extends: contradiction with the copy restricted
    obtain ⟨f⟩ := hblue
    obtain ⟨u⟩ := hW'
    obtain ⟨w, hw, hnot⟩ := hnoext u (f.comp (Copy.induce H' ({u}ᶜ : Set W'))) (f u)
      (fun w h => w.2 (f.injective h))
    exact hnot (f.toHom.map_adj hw)
  · exact hres m' W' H' h2' hm' hm3' hstar hconn hmax ih C' x hxmax hx hall hred hnoext hnoedge hredC hk4 hK2
      hcol

/-- **General conditional closure.** If `x ≠ z` are both red to every vertex of a set containing a red path
`p` on `k - 3` vertices (from `a` to `b`) and a further vertex `y₀` off the path, there is a red `C_k`:
the red path `y₀ x a … b` on `k - 1` vertices with apex `z`. -/
theorem cycleGraph_of_common_red_path {V : Type*} (C : SimpleGraph V) (k : ℕ) (hk : 4 ≤ k) (x z y₀ : V)
    {a b : V} (p : C.Walk a b) (hp : p.IsPath) (hlen : p.length = k - 4) (hxz : x ≠ z)
    (hxp : ∀ v ∈ p.support, C.Adj x v) (hzp : ∀ v ∈ p.support, C.Adj z v)
    (hy₀p : y₀ ∉ p.support) (hxy₀ : C.Adj x y₀) (hzy₀ : C.Adj z y₀) :
    (cycleGraph k).IsContained C := by
  have hxa : C.Adj x a := hxp a p.start_mem_support
  have hzb : C.Adj z b := hzp b p.end_mem_support
  have hxnot : x ∉ p.support := fun h => (hxp x h).ne rfl
  have hznot : z ∉ p.support := fun h => (hzp z h).ne rfl
  have hpath : (Walk.cons hxy₀.symm (Walk.cons hxa p) : C.Walk y₀ b).IsPath := by
    rw [Walk.cons_isPath_iff, Walk.cons_isPath_iff]
    refine ⟨⟨hp, hxnot⟩, ?_⟩
    rw [Walk.support_cons, List.mem_cons, not_or]
    exact ⟨hxy₀.ne.symm, hy₀p⟩
  refine cycleGraph_isContained_of_isPath_apex C k (by omega) _ hpath ?_ z ?_ hzy₀ hzb.symm
  · rw [Walk.length_cons, Walk.length_cons, hlen]
    omega
  · rw [Walk.support_cons, Walk.support_cons, List.mem_cons, List.mem_cons, not_or, not_or]
    exact ⟨hzy₀.ne, hxz.symm, hznot⟩

/-! ### Route K: the union bound as a step -/

/-- **Union-bound step.** Let `u` be a vertex all of whose neighbours have degree at least two, let every red
degree be at most `r`, and suppose `(#W - 1) + deg u · r < (k-1)m + 1`. Then a copy of `H - u` given by the
induction hypothesis extends: some vertex outside the copy and outside the red neighbourhoods of the images of
`N(u)` is blue to all of them. -/
theorem step_union_bound (k m : ℕ) (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (u : W)
    (ih : ∀ C' : SimpleGraph (Fin ((k - 1) * (m - H.degree u) + 1)),
      (cycleGraph k).IsContained C' ∨ (H.induce ({u}ᶜ : Set W)).IsContained C'ᶜ)
    {n : ℕ} (C : SimpleGraph (Fin n)) [DecidableRel C.Adj] (hn : (k - 1) * (m - H.degree u) + 1 ≤ n)
    (r : ℕ) (hred : ∀ z, C.degree z ≤ r) (hineq : (Fintype.card W - 1) + H.degree u * r < n) :
    (cycleGraph k).IsContained C ∨ H.IsContained Cᶜ := by
  classical
  rcases core_mono (cycleGraph k) _ hn ih C with h1 | h1
  · exact Or.inl h1
  right
  obtain ⟨f⟩ := h1
  set I : Finset (Fin n) := Finset.univ.image (fun w : ({u}ᶜ : Set W) => f w) with hI
  set Nu : Finset ({u}ᶜ : Set W) := Finset.univ.filter (fun w => H.Adj u w) with hNu
  set B : Finset (Fin n) := Nu.biUnion (fun w => C.neighborFinset (f w)) with hB
  have hIcard : I.card = Fintype.card W - 1 := by
    have hinj : Function.Injective (fun w : ({u}ᶜ : Set W) => f w) := fun a b h => f.injective h
    have := Finset.card_image_of_injective (Finset.univ : Finset ({u}ᶜ : Set W)) hinj
    have h1 : Fintype.card ({u} : Set W) = 1 := by simp
    rw [Finset.card_univ, Fintype.card_compl_set, h1] at this
    rw [hI]
    exact this
  have hNucard : Nu.card = H.degree u := by
    rw [← card_neighborFinset_eq_degree]
    have : Nu.map (Function.Embedding.subtype _) = H.neighborFinset u := by
      ext w
      simp only [Finset.mem_map, Function.Embedding.coe_subtype, hNu, Finset.mem_filter, Finset.mem_univ,
        true_and, mem_neighborFinset]
      constructor
      · rintro ⟨w', hw', rfl⟩
        exact hw'
      · intro hw
        exact ⟨⟨w, by simpa using hw.ne.symm⟩, hw, rfl⟩
    rw [← this, Finset.card_map]
  have hBcard : B.card ≤ H.degree u * r := by
    rw [hB]
    calc (Nu.biUnion fun w => C.neighborFinset (f w)).card
        ≤ ∑ w ∈ Nu, (C.neighborFinset (f w)).card := Finset.card_biUnion_le
      _ ≤ ∑ _w ∈ Nu, r := Finset.sum_le_sum (fun w _ => by rw [card_neighborFinset_eq_degree]; exact hred _)
      _ = H.degree u * r := by rw [Finset.sum_const, smul_eq_mul, hNucard]
  obtain ⟨y, hy⟩ : (Finset.univ \ (I ∪ B)).Nonempty := by
    rw [← Finset.card_pos, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin]
    have := Finset.card_union_le I B
    omega
  rw [Finset.mem_sdiff, Finset.mem_union, not_or] at hy
  refine isContained_of_extend H u Cᶜ f y ?_ ?_
  · intro w h
    exact hy.2.1 (Finset.mem_image.mpr ⟨w, Finset.mem_univ _, h⟩)
  · intro w hw
    rw [compl_adj]
    refine ⟨fun h => hy.2.1 (Finset.mem_image.mpr ⟨w, Finset.mem_univ _, h.symm⟩), fun h => ?_⟩
    refine hy.2.2 (Finset.mem_biUnion.mpr ⟨w, ?_, (mem_neighborFinset _ _ _).mpr h.symm⟩)
    rw [hNu, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hw⟩

/-- **Reduction, with the union bound.** In the residue every vertex `u` of `H'` satisfies
`(k-1)m' + 1 ≤ (#W' - 1) + deg u · (k-2)(#W' - 1)`. -/
theorem core_of_residue_final''' (k : ℕ) (hk : 3 ≤ k)
    (hres : ∀ (m' : ℕ) (W' : Type) [Fintype W'] (H' : SimpleGraph W') [DecidableRel H'.Adj],
      (∀ v, 2 ≤ H'.degree v) → H'.edgeSet.ncard = m' → 3 ≤ m' →
      (¬ ∃ v₀, ∀ a b, H'.Adj a b → a = v₀ ∨ b = v₀) → H'.Preconnected →
      (∀ v, (k - 1) * H'.degree v ≤ (k - 2) * (Fintype.card W' - 1)) →
      (∀ m'' < m', ∀ (W'' : Type) [Fintype W''] (H'' : SimpleGraph W'') [DecidableRel H''.Adj],
        (∀ v, 0 < H''.degree v) → H''.edgeSet.ncard = m'' → 1 ≤ m'' →
        ∀ C'' : SimpleGraph (Fin ((k - 1) * m'' + 1)),
          (cycleGraph k).IsContained C'' ∨ H''.IsContained C''ᶜ) →
      ∀ (C' : SimpleGraph (Fin ((k - 1) * m' + 1))) [DecidableRel C'.Adj] (x : Fin ((k - 1) * m' + 1)),
        (∀ y, C'ᶜ.degree y ≤ C'ᶜ.degree x) → m' ≤ C'ᶜ.degree x →
        (∀ v, C'ᶜ.degree x < (k - 1) * (m' - H'.degree v) + 1) →
        (∀ z, C'.degree z ≤ (k - 2) * (Fintype.card W' - 1)) →
        (∀ (u : W') (f : Copy (H'.induce ({u}ᶜ : Set W')) C'ᶜ) (y : Fin ((k - 1) * m' + 1)),
          (∀ w, f w ≠ y) → ∃ w : ({u}ᶜ : Set W'), H'.Adj u w ∧ ¬ C'ᶜ.Adj y (f w)) →
        (∀ (u v : W') (f : Copy (H'.deleteEdges {s(u, v)}) C'ᶜ), C'.Adj (f u) (f v)) →
        ¬ (cycleGraph k).IsContained C' → k ≠ 4 →
        (∀ x' : Fin ((k - 1) * m' + 1), ∃ z, z ≠ x' ∧
          k - 2 < ((C'.neighborFinset x').filter (fun y => C'.Adj y z)).card) →
        ¬ C'.Colorable (k - 1) →
        (∀ u, (k - 1) * m' + 1 ≤ (Fintype.card W' - 1) + H'.degree u * ((k - 2) * (Fintype.card W' - 1))) →
        False)
    (m : ℕ) (hm1 : 1 ≤ m) (W : Type) [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (h0 : ∀ v, 0 < H.degree v) (hm : H.edgeSet.ncard = m) (C : SimpleGraph (Fin ((k - 1) * m + 1))) :
    (cycleGraph k).IsContained C ∨ H.IsContained Cᶜ := by
  classical
  refine core_of_residue_final'' k hk ?_ m hm1 W H h0 hm C
  intro m' W' _ H' _ h2' hm' hm3' hstar hconn hmax ih C' _ x hxmax hx hall hred hnoext hnoedge hredC hk4 hK2
    hcol
  by_cases hub : ∀ u, (k - 1) * m' + 1 ≤ (Fintype.card W' - 1) + H'.degree u * ((k - 2) * (Fintype.card W' - 1))
  · exact hres m' W' H' h2' hm' hm3' hstar hconn hmax ih C' x hxmax hx hall hred hnoext hnoedge hredC hk4 hK2
      hcol hub
  push Not at hub
  obtain ⟨u, hu⟩ := hub
  have hu2 := h2' u
  have hult : H'.degree u < m' := degree_lt_ncard_of_not_star H' m' hm' hstar u
  have h0' : ∀ w, 0 < H'.degree w := fun w => by have := h2' w; omega
  have hmu : (H'.induce ({u}ᶜ : Set W')).edgeSet.ncard = m' - H'.degree u := by
    rw [ncard_edgeSet_induce_compl_singleton, hm']
  have ih' := ih (m' - H'.degree u) (by omega) _ (H'.induce ({u}ᶜ : Set W'))
    (degree_pos_induce_compl_singleton H' h0' u (fun w _ => h2' w)) hmu (by omega)
  have hn : (k - 1) * (m' - H'.degree u) + 1 ≤ (k - 1) * m' + 1 := by
    have := Nat.mul_le_mul_left (k - 1) (Nat.sub_le m' (H'.degree u))
    omega
  rcases step_union_bound k m' W' H' u ih' C' hn _ hred hu with h | h
  · exact hredC h
  · obtain ⟨f⟩ := h
    have hW' : Nonempty W' := ⟨u⟩
    obtain ⟨w, hw, hnot⟩ := hnoext u (f.comp (Copy.induce H' ({u}ᶜ : Set W'))) (f u)
      (fun w h => w.2 (f.injective h))
    exact hnot (f.toHom.map_adj hw)

/-! ### Even `k`: a red `K_{t,t}` gives a red `C_{2t}` -/

/-- Alternating paths `a₀ b₀ a₁ b₁ … a_j` in a complete bipartite red subgraph. -/
theorem exists_alternating_path {V : Type*} (C : SimpleGraph V) (t : ℕ) (ht : 0 < t) (a b : Fin t → V)
    (ha : Function.Injective a) (hb : Function.Injective b) (hab : ∀ i j, a i ≠ b j)
    (hadj : ∀ i j, C.Adj (a i) (b j)) :
    ∀ j (hj : j < t), ∃ p : C.Walk (a ⟨0, ht⟩) (a ⟨j, hj⟩), p.IsPath ∧ p.length = 2 * j ∧
      ∀ v ∈ p.support, (∃ (i : ℕ) (hi : i < t), i ≤ j ∧ v = a ⟨i, hi⟩) ∨ (∃ (i : ℕ) (hi : i < t), i < j ∧ v = b ⟨i, hi⟩) := by
  intro j
  induction j with
  | zero =>
    intro hj
    refine ⟨Walk.nil, Walk.IsPath.nil, rfl, fun v hv => ?_⟩
    rw [Walk.support_nil, List.mem_singleton] at hv
    exact Or.inl ⟨0, ht, le_rfl, hv⟩
  | succ j ih =>
    intro hj
    obtain ⟨p, hp, hlen, hsupp⟩ := ih (by omega)
    have hjt : j < t := by omega
    have hbj : b ⟨j, hjt⟩ ∉ p.support := by
      intro hmem
      rcases hsupp _ hmem with ⟨i, hi, -, heq⟩ | ⟨i, hi, hij, heq⟩
      · exact hab _ _ heq.symm
      · have := hb heq
        rw [Fin.mk.injEq] at this
        omega
    have haj : a ⟨j + 1, hj⟩ ∉ (p.concat (hadj ⟨j, hjt⟩ ⟨j, hjt⟩)).support := by
      rw [Walk.support_concat, List.mem_append, List.mem_singleton, not_or]
      refine ⟨fun hmem => ?_, fun heq => hab _ _ heq⟩
      rcases hsupp _ hmem with ⟨i, hi, hij, heq⟩ | ⟨i, hi, -, heq⟩
      · have := ha heq
        rw [Fin.mk.injEq] at this
        omega
      · exact hab _ _ heq
    refine ⟨(p.concat (hadj ⟨j, hjt⟩ ⟨j, hjt⟩)).concat (hadj ⟨j + 1, hj⟩ ⟨j, hjt⟩).symm, ?_, ?_, ?_⟩
    · exact (hp.concat hbj _).concat haj _
    · rw [Walk.length_concat, Walk.length_concat, hlen]
      omega
    · intro v hv
      rw [Walk.support_concat, Walk.support_concat, List.mem_append, List.mem_append, List.mem_singleton,
        List.mem_singleton] at hv
      rcases hv with (hv | hv) | hv
      · rcases hsupp v hv with ⟨i, hi, hij, heq⟩ | ⟨i, hi, hij, heq⟩
        · exact Or.inl ⟨i, hi, by omega, heq⟩
        · exact Or.inr ⟨i, hi, by omega, heq⟩
      · exact Or.inr ⟨j, hjt, by omega, hv⟩
      · exact Or.inl ⟨j + 1, hj, le_rfl, hv⟩

/-- **Even `k`, conditional.** A red `K_{t,t}` (`t ≥ 2`) contains a red `C_{2t}`: the alternating path
`a₀ b₀ … b_{t-2} a_{t-1}` on `2t - 1` vertices with apex `b_{t-1}`. -/
theorem cycleGraph_isContained_of_biclique {V : Type*} (C : SimpleGraph V) (t : ℕ) (ht : 2 ≤ t)
    (a b : Fin t → V) (ha : Function.Injective a) (hb : Function.Injective b) (hab : ∀ i j, a i ≠ b j)
    (hadj : ∀ i j, C.Adj (a i) (b j)) : (cycleGraph (2 * t)).IsContained C := by
  have ht0 : 0 < t := by omega
  have hlt : t - 1 < t := by omega
  obtain ⟨p, hp, hlen, hsupp⟩ := exists_alternating_path C t ht0 a b ha hb hab hadj (t - 1) hlt
  refine cycleGraph_isContained_of_isPath_apex C (2 * t) (by omega) p hp (by rw [hlen]; omega) (b ⟨t - 1, hlt⟩)
    ?_ (hadj _ _).symm (hadj _ _)
  intro hmem
  rcases hsupp _ hmem with ⟨i, hi, -, heq⟩ | ⟨i, hi, hij, heq⟩
  · exact hab _ _ heq.symm
  · have := hb heq
    rw [Fin.mk.injEq] at this
    omega

/-! ### Route L: red domination -/

/-- **Domination.** In the residue, for every vertex `u` of `H'` and every set `T` of at most `(k-1) deg u`
vertices there is a set `Z` of at most `deg u` vertices, disjoint from `T`, such that every vertex of `T` has a
red neighbour in `Z`: take an IH copy of `H' - u` inside `V \ T` and let `Z` be the images of `N(u)`. -/
theorem domination_of_residue (k : ℕ) (m' : ℕ) (W' : Type) [Fintype W']
    (H' : SimpleGraph W') [DecidableRel H'.Adj] (h2' : ∀ v, 2 ≤ H'.degree v) (hm' : H'.edgeSet.ncard = m')
    (hstar : ¬ ∃ v₀, ∀ a b, H'.Adj a b → a = v₀ ∨ b = v₀)
    (ih : ∀ m'' < m', ∀ (W'' : Type) [Fintype W''] (H'' : SimpleGraph W'') [DecidableRel H''.Adj],
      (∀ v, 0 < H''.degree v) → H''.edgeSet.ncard = m'' → 1 ≤ m'' →
      ∀ C'' : SimpleGraph (Fin ((k - 1) * m'' + 1)), (cycleGraph k).IsContained C'' ∨ H''.IsContained C''ᶜ)
    (C' : SimpleGraph (Fin ((k - 1) * m' + 1))) [DecidableRel C'.Adj]
    (hnoext : ∀ (u : W') (f : Copy (H'.induce ({u}ᶜ : Set W')) C'ᶜ) (y : Fin ((k - 1) * m' + 1)),
      (∀ w, f w ≠ y) → ∃ w : ({u}ᶜ : Set W'), H'.Adj u w ∧ ¬ C'ᶜ.Adj y (f w))
    (hredC : ¬ (cycleGraph k).IsContained C') (u : W') (T : Finset (Fin ((k - 1) * m' + 1)))
    (hT : T.card ≤ (k - 1) * H'.degree u) :
    ∃ Z : Finset (Fin ((k - 1) * m' + 1)), Z.card ≤ H'.degree u ∧ Disjoint Z T ∧
      ∀ y ∈ T, ∃ z ∈ Z, C'.Adj y z := by
  classical
  have hu2 := h2' u
  have hult : H'.degree u < m' := degree_lt_ncard_of_not_star H' m' hm' hstar u
  have h0' : ∀ w, 0 < H'.degree w := fun w => by have := h2' w; omega
  have hmu : (H'.induce ({u}ᶜ : Set W')).edgeSet.ncard = m' - H'.degree u := by
    rw [ncard_edgeSet_induce_compl_singleton, hm']
  have ih' := ih (m' - H'.degree u) (by omega) _ (H'.induce ({u}ᶜ : Set W'))
    (degree_pos_induce_compl_singleton H' h0' u (fun w _ => h2' w)) hmu (by omega)
  have h5 : (k - 1) * m' = (k - 1) * (m' - H'.degree u) + (k - 1) * H'.degree u := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hult.le]
  have hScard : (k - 1) * (m' - H'.degree u) + 1 ≤ (Finset.univ \ T).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨e, he⟩ := exists_embedding_into_finset _ _ hScard
  rcases ih' (C'.comap e) with h1 | h1
  · exact (hredC (h1.trans ⟨(Embedding.comap e C').toCopy⟩)).elim
  obtain ⟨f⟩ := h1
  have hle : (C'.comap e)ᶜ ≤ C'ᶜ.comap e := by
    intro a b hab
    rw [compl_adj, comap_adj] at hab
    rw [comap_adj, compl_adj]
    exact ⟨fun h' => hab.1 (e.injective h'), hab.2⟩
  let g : Copy (H'.induce ({u}ᶜ : Set W')) C'ᶜ :=
    (Embedding.comap e C'ᶜ).toCopy.comp ((Copy.ofLE _ _ hle).comp f)
  have hg : ∀ w, g w = e (f w) := fun w => rfl
  have hgT : ∀ w, g w ∉ T := fun w hw => by
    have := he (f w)
    rw [Finset.mem_sdiff] at this
    exact this.2 (hg w ▸ hw)
  set Nu : Finset ({u}ᶜ : Set W') := Finset.univ.filter (fun w => H'.Adj u w) with hNu
  have hNucard : Nu.card = H'.degree u := by
    rw [← card_neighborFinset_eq_degree]
    have : Nu.map (Function.Embedding.subtype _) = H'.neighborFinset u := by
      ext w
      simp only [Finset.mem_map, Function.Embedding.coe_subtype, hNu, Finset.mem_filter, Finset.mem_univ,
        true_and, mem_neighborFinset]
      constructor
      · rintro ⟨w', hw', rfl⟩
        exact hw'
      · intro hw
        exact ⟨⟨w, by simpa using hw.ne.symm⟩, hw, rfl⟩
    rw [← this, Finset.card_map]
  refine ⟨Nu.image (fun w => g w), ?_, ?_, ?_⟩
  · exact (Finset.card_image_le).trans hNucard.le
  · rw [Finset.disjoint_left]
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨w, -, rfl⟩ := hy
    exact hgT w
  · intro y hy
    obtain ⟨w, hw, hred'⟩ := hnoext u g y (fun w h => hgT w (h ▸ hy))
    refine ⟨g w, Finset.mem_image.mpr ⟨w, by rw [hNu, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hw⟩, rfl⟩, ?_⟩
    rw [compl_adj, not_and, not_not] at hred'
    exact hred' (fun h => hgT w (h ▸ hy))

/-- In the residue the red graph contains a `C_4` (a red `K_{2,k-1}` sits on every vertex). -/
theorem cycleGraph_four_of_common_red (k : ℕ) (hk : 3 ≤ k) {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) [DecidableRel C.Adj] (x z : V) (hzx : z ≠ x)
    (hz : k - 2 < ((C.neighborFinset x).filter (fun y => C.Adj y z)).card) : (cycleGraph 4).IsContained C := by
  obtain ⟨y₁, hy₁, y₂, hy₂, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < ((C.neighborFinset x).filter (fun y => C.Adj y z)).card)
  rw [Finset.mem_filter, mem_neighborFinset] at hy₁ hy₂
  have := cycleGraph_isContained_of_biclique C 2 le_rfl ![x, z] ![y₁, y₂] ?_ ?_ ?_ ?_
  · simpa using this
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [hy₁.1.ne, hy₂.1.ne, hy₁.2.ne.symm, hy₂.2.ne.symm]
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [hy₁.1, hy₂.1, hy₁.2.symm, hy₂.2.symm]


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
  -- Routes E–I: reduce to the residue in final form.
  refine core_of_residue_final''' k hk ?_ m (by omega) W H h0 hm C
  intro m' W' _ H' _ h2' hm' hm3' hstar hconn hmax ih C' _ x hxmax hx hall hred hnoext hnoedge hredC hk4 hK2 hcol hub
  -- Residue attempt 13 (generic k ≥ 5): `x` and its partner `z` have `≥ k-1` common red neighbours `Yz`. By
  -- `cycleGraph_of_common_red_path` a red path on `k-3` vertices inside `Yz` closes a red `C_k`. The single gap
  -- is the existence of such a path: red[N_red(x)] is only known to be `P_{k-1}`-free, which does not forbid
  -- `Yz` from being a blue clique.
  obtain ⟨z, hzx, hz⟩ := hK2 x
  set Yz := (C'.neighborFinset x).filter (fun y => C'.Adj y z) with hYz
  have hYzx : ∀ y ∈ Yz, C'.Adj x y := fun y hy => by
    rw [hYz, Finset.mem_filter, mem_neighborFinset] at hy
    exact hy.1
  have hYzz : ∀ y ∈ Yz, C'.Adj z y := fun y hy => by
    rw [hYz, Finset.mem_filter] at hy
    exact hy.2.symm
  rcases Nat.lt_or_ge k 5 with hk3 | hk5
  · -- `k = 3` (Residue attempt 17, Route L): a red star `T` with centre `c` and `2Δ - 1` leaves is dominated by
    -- a `Δ`-set `Z`; a dominator red to the centre and to a leaf gives a red triangle. The gap: the dominator of
    -- the centre need not dominate any leaf.
    have hk3' : k = 3 := by omega
    have hW' : Nonempty W' := nonempty_of_ncard_edgeSet_pos H' (by omega)
    obtain ⟨u, hu⟩ := exists_max_degree H'
    have hu2 := h2' u
    have hult : H'.degree u < m' := degree_lt_ncard_of_not_star H' m' hm' hstar u
    have hxred : (k - 1) * H'.degree u ≤ C'.degree x := by
      have h1 := hall u
      have h3 := C'.degree_compl x
      rw [Fintype.card_fin] at h3
      have h5 : (k - 1) * m' = (k - 1) * (m' - H'.degree u) + (k - 1) * H'.degree u := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hult.le]
      omega
    obtain ⟨L, hLsub, hLcard⟩ := Finset.exists_subset_card_eq
      (show (k - 1) * H'.degree u - 1 ≤ (C'.neighborFinset x).card by
        rw [card_neighborFinset_eq_degree]; omega)
    have hxL : x ∉ L := fun h => (((mem_neighborFinset _ _ _).mp (hLsub h)).ne rfl)
    obtain ⟨Z, hZcard, hZT, hZdom⟩ := domination_of_residue k m' W' H' h2' hm' hstar ih C' hnoext hredC u
      (insert x L) (by rw [Finset.card_insert_of_notMem hxL, hLcard]; omega)
    obtain ⟨z, hzZ, hxz⟩ := hZdom x (Finset.mem_insert_self _ _)
    -- the gap: a leaf `ℓ ∈ L` red to `z`
    have hleaf : ∃ ℓ ∈ L, C'.Adj ℓ z := by
      exact absurd hzZ (by omega)
    obtain ⟨ℓ, hℓ, hℓz⟩ := hleaf
    have hzL : z ∉ insert x L := Finset.disjoint_left.mp hZT hzZ
    have hzℓ : z ≠ ℓ := fun h => hzL (h ▸ Finset.mem_insert_of_mem hℓ)
    have hxℓ : C'.Adj x ℓ := (mem_neighborFinset _ _ _).mp (hLsub hℓ)
    apply hredC
    rw [hk3']
    exact cycleGraph_isContained_of_isClique C' {x, ℓ, z} (by
      rw [Finset.coe_insert, Finset.coe_insert, Finset.coe_singleton]
      exact (((C'.isClique_singleton z).insert fun b hb _ => by
        rw [Set.mem_singleton_iff] at hb; subst hb; exact hℓz).insert fun b hb hne => by
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
        rcases hb with rfl | rfl
        · exact hxℓ
        · exact hxz)) 3 (by
      rw [Finset.card_insert_of_notMem, Finset.card_pair hzℓ]
      rw [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hxℓ.ne, hxz.ne⟩)
  -- Residue attempt 15 (even k = 2t ≥ 6): a red `K_{t,t}` would do (`cycleGraph_isContained_of_biclique`); the
  -- partner structure only provides `K_{2,k-1}`, so the `t - 2` further apexes are the gap.
  by_cases heven : Even k
  · obtain ⟨t, ht⟩ := heven
    have ht3 : 3 ≤ t := by omega
    have hbic : ∃ (a b : Fin t → Fin ((k - 1) * m' + 1)), Function.Injective a ∧ Function.Injective b ∧
        (∀ i j, a i ≠ b j) ∧ ∀ i j, C'.Adj (a i) (b j) := by
      exact absurd ht3 (by omega)
    obtain ⟨a, b, ha, hb, hab, hadj⟩ := hbic
    have := cycleGraph_isContained_of_biclique C' t (by omega) a b ha hb hab hadj
    rw [show 2 * t = k by omega] at this
    exact hredC this
  -- Residue attempt 16 (odd k ≥ 5, Route L): a red path `T` on `(k-1)Δ` vertices is red-dominated by the
  -- `Δ` images of `N(u)` (`domination_of_residue`); some image `z` is red to `≥ k-1` vertices of `T`, and two
  -- of them at path-distance exactly `k-2` would close a red `C_k` through `z`. The gap: a `(k-1)`-subset of a
  -- path on `(k-1)Δ` vertices can avoid all pairs at distance `k-2`.
  have hW' : Nonempty W' := nonempty_of_ncard_edgeSet_pos H' (by omega)
  obtain ⟨u, hu⟩ := exists_max_degree H'
  have hu2 := h2' u
  have hult : H'.degree u < m' := degree_lt_ncard_of_not_star H' m' hm' hstar u
  have hmind : ∀ y, (k - 1) * H'.degree u ≤ C'.degree y := by
    intro y
    have h1 := hall u
    have h2 := hxmax y
    have h3 := C'.degree_compl y
    rw [Fintype.card_fin] at h3
    have h5 : (k - 1) * m' = (k - 1) * (m' - H'.degree u) + (k - 1) * H'.degree u := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hult.le]
    omega
  obtain ⟨a, b, p, hp, hlen, -⟩ := exists_isPath_of_forall_degree_ge C' Finset.univ ((k - 1) * H'.degree u)
    (fun y _ => by rw [Finset.inter_univ, card_neighborFinset_eq_degree]; exact hmind y) x (Finset.mem_univ _)
    ((k - 1) * H'.degree u - 1) (Nat.sub_le _ _)
  have hTcard : p.support.toFinset.card ≤ (k - 1) * H'.degree u := by
    rw [List.toFinset_card_of_nodup ((Walk.isPath_def _).mp hp), Walk.length_support, hlen]
    have : 1 ≤ (k - 1) * H'.degree u := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    omega
  obtain ⟨Z, hZcard, hZT, hZdom⟩ := domination_of_residue k m' W' H' h2' hm' hstar ih C' hnoext hredC u
    p.support.toFinset hTcard
  -- the gap: a dominator red to both ends of a sub-path on `k - 1` vertices
  have hgap : ∃ z ∈ Z, ∃ (c d : Fin ((k - 1) * m' + 1)) (q : C'.Walk c d), q.IsPath ∧ q.length = k - 2 ∧
      z ∉ q.support ∧ C'.Adj z c ∧ C'.Adj d z := by
    exact absurd hZcard (by omega)
  obtain ⟨z, -, c, d, q, hq, hqlen, hzq, hzc, hdz⟩ := hgap
  exact hredC (cycleGraph_isContained_of_isPath_apex C' k hk q hq hqlen z hzq hzc hdz)

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
