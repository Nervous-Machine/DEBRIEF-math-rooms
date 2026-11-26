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

/-! ### Scaffold for the open core: strong induction on the number of edges

The plan: delete a vertex `u` of `H`, embed `H - u` in the blue neighbourhood of a vertex `x` of large
blue degree by induction, and send `u` to `x`. The statement is generalised to allow isolated vertices
in `H` (they appear when a neighbour of `u` is a leaf), paying for them with `#W ≤ n`. -/

/-- A graph with no isolated vertices has at most twice as many vertices as edges. -/
theorem card_le_two_mul_ncard_edgeSet {W : Type} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (h0 : ∀ v, 0 < H.degree v) : Fintype.card W ≤ 2 * H.edgeSet.ncard := by
  classical
  have h1 : ∑ v, H.degree v = 2 * H.edgeFinset.card := H.sum_degrees_eq_twice_card_edges
  have h2 : Fintype.card W ≤ ∑ v, H.degree v := by
    calc Fintype.card W = ∑ _v : W, 1 := by simp
      _ ≤ ∑ v, H.degree v := Finset.sum_le_sum fun v _ => h0 v
  rw [← coe_edgeFinset, Set.ncard_coe_finset]
  omega

/-- The number of edges of `H - u`. -/
theorem ncard_edgeSet_induce_compl_singleton {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (u : W) :
    (H.induce ({u}ᶜ : Set W)).edgeSet.ncard = H.edgeSet.ncard - H.degree u := by
  rw [← coe_edgeFinset, Set.ncard_coe_finset, ← coe_edgeFinset, Set.ncard_coe_finset,
    card_edgeFinset_induce_compl_singleton, card_edgeFinset_deleteIncidenceSet]

/-- The number of vertices of `H - u`. -/
theorem card_compl_singleton' {W : Type} [Fintype W] [DecidableEq W] (u : W) :
    Fintype.card ({u}ᶜ : Set W) = Fintype.card W - 1 := by
  rw [Fintype.card_compl_set, Set.card_singleton]

/-- The degree of a vertex is at most the number of edges. -/
theorem degree_le_ncard_edgeSet {W : Type} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj] (u : W) :
    H.degree u ≤ H.edgeSet.ncard := by
  classical
  rw [← coe_edgeFinset, Set.ncard_coe_finset]
  exact degree_le_card_edgeFinset H u

/-- If the colouring restricted along `e : Fin b ↪ Fin n`, whose image lies in the blue neighbourhood of
`x`, contains a blue copy of `H - u`, then the colouring contains a blue copy of `H` (send `u` to `x`). -/
theorem isContained_compl_of_extend_nbhd {n b : ℕ} (C : SimpleGraph (Fin n)) (x : Fin n) (e : Fin b ↪ Fin n)
    (he : ∀ i, Cᶜ.Adj x (e i)) {W : Type} [DecidableEq W] (H : SimpleGraph W) (u : W)
    (h : (H.induce ({u}ᶜ : Set W)).IsContained (C.comap e)ᶜ) : H.IsContained Cᶜ := by
  obtain ⟨f⟩ := h
  have hle : (C.comap e)ᶜ ≤ Cᶜ.comap e := by
    intro a b hab
    rw [compl_adj, comap_adj] at hab
    rw [comap_adj, compl_adj]
    exact ⟨fun h' => hab.1 (e.injective h'), hab.2⟩
  let g : Copy (H.induce ({u}ᶜ : Set W)) Cᶜ :=
    (Embedding.comap e Cᶜ).toCopy.comp ((Copy.ofLE _ _ hle).comp f)
  have hg : ∀ w, g w = e (f w) := fun w => rfl
  refine isContained_of_extend H u Cᶜ g x (fun w => ?_) (fun w _ => ?_)
  · rw [hg]
    exact (he (f w)).ne.symm
  · rw [hg]
    exact he (f w)

/-- A red `C_k` in the restricted colouring is a red `C_k`. -/
theorem cycleGraph_isContained_of_comap {n b k : ℕ} (C : SimpleGraph (Fin n)) (e : Fin b ↪ Fin n)
    (h : (cycleGraph k).IsContained (C.comap e)) : (cycleGraph k).IsContained C :=
  h.trans ⟨(Embedding.comap e C).toCopy⟩

/-! ### Red structure: chords of a longest red path -/

/-- A chord from the start of a path to its `i`-th vertex (`2 ≤ i ≤ length`) closes a cycle of
length `i + 1`. -/
theorem cycleGraph_isContained_of_isPath_adj_getVert {V : Type*} {G : SimpleGraph V} {u v : V}
    {p : G.Walk u v} (hp : p.IsPath) {i : ℕ} (hi2 : 2 ≤ i) (hil : i ≤ p.length)
    (hadj : G.Adj u (p.getVert i)) : (cycleGraph (i + 1)).IsContained G := by
  rw [cycleGraph_isContained_iff (by omega)]
  refine ⟨p.getVert i, Walk.cons hadj.symm (p.take i), ?_, ?_⟩
  · rw [Walk.cons_isCycle_iff]
    refine ⟨hp.take i, fun hmem => ?_⟩
    rw [Sym2.eq_swap] at hmem
    have h1 := (hp.take i).length_eq_one_of_mem_edges hmem
    rw [Walk.take_length] at h1
    omega
  · rw [Walk.length_cons, Walk.take_length]
    omega

/-- In a `C_k`-free graph, the start of a longest path (of length at least `k - 1`) has all its
neighbours on the path and none at position `k - 1`, so its degree is at most `length - 1`. -/
theorem degree_add_one_le_length_of_longest_path {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ} (hk : 3 ≤ k)
    (hfree : ¬ (cycleGraph k).IsContained G) {u v : V} {p : G.Walk u v} (hp : p.IsPath)
    (hmax : ∀ (u' v' : V) (p' : G.Walk u' v'), p'.IsPath → p'.length ≤ p.length)
    (hkL : k - 1 ≤ p.length) : G.degree u + 1 ≤ p.length := by
  have hsub : G.neighborFinset u ⊆ ((Finset.Icc 1 p.length).erase (k - 1)).image p.getVert := by
    intro w hw
    rw [mem_neighborFinset] at hw
    have hwp : w ∈ p.support := by
      by_contra hnot
      have := hmax _ _ (Walk.cons hw.symm p) (hp.cons hnot)
      rw [Walk.length_cons] at this
      omega
    obtain ⟨i, rfl, hi⟩ := Walk.mem_support_iff_exists_getVert.mp hwp
    rw [Finset.mem_image]
    refine ⟨i, ?_, rfl⟩
    rw [Finset.mem_erase, Finset.mem_Icc]
    refine ⟨?_, ?_, hi⟩
    · intro hik
      subst hik
      apply hfree
      have := cycleGraph_isContained_of_isPath_adj_getVert hp (by omega) hkL hw
      rwa [Nat.sub_add_cancel (by omega)] at this
    · by_contra h0
      have : i = 0 := by omega
      subst this
      rw [Walk.getVert_zero] at hw
      exact hw.ne rfl
  have h1 := Finset.card_le_card hsub
  have h2 : (((Finset.Icc 1 p.length).erase (k - 1)).image p.getVert).card ≤
      ((Finset.Icc 1 p.length).erase (k - 1)).card := Finset.card_image_le
  rw [Finset.card_erase_of_mem (by rw [Finset.mem_Icc]; omega), Nat.card_Icc] at h2
  rw [card_neighborFinset_eq_degree] at h1
  omega

/-- Two chords from the start of a path to the positions `j` and `j + (k - 2)` (`1 ≤ j`, `3 ≤ k`)
close a cycle of length exactly `k`: `u, p_j, p_{j+1}, …, p_{j+k-2}, u`. -/
theorem cycleGraph_isContained_of_two_chords {V : Type*} {G : SimpleGraph V} {u v : V}
    {p : G.Walk u v} (hp : p.IsPath) {j k : ℕ} (hj : 1 ≤ j) (hk : 3 ≤ k)
    (hjk : j + (k - 2) ≤ p.length) (h₁ : G.Adj u (p.getVert j))
    (h₂ : G.Adj u (p.getVert (j + (k - 2)))) : (cycleGraph k).IsContained G := by
  let q : G.Walk (p.getVert j) (p.getVert (j + (k - 2))) :=
    ((p.drop j).take (k - 2)).copy rfl (p.drop_getVert j (k - 2))
  have hqlen : q.length = k - 2 := by
    simp only [q, Walk.length_copy, Walk.take_length, Walk.drop_length]
    omega
  have hqpath : q.IsPath := (Walk.isPath_copy _ _ _).mpr ((hp.drop j).take (k - 2))
  have hqget : ∀ i, q.getVert i = p.getVert (j + min (k - 2) i) := fun i => by
    simp only [q, Walk.getVert_copy, Walk.take_getVert, Walk.drop_getVert]
  have hu : u ∉ q.support := by
    intro hmem
    obtain ⟨i, hi, hile⟩ := Walk.mem_support_iff_exists_getVert.mp hmem
    rw [hqget] at hi
    have := (hp.getVert_eq_start_iff (by omega)).mp hi
    omega
  have hinj := hp.getVert_injOn
  have hne : p.getVert j ≠ p.getVert (j + (k - 2)) := by
    intro heq
    have := hinj (by simp; omega) (by simp; omega) heq
    omega
  rw [cycleGraph_isContained_iff (by omega)]
  refine ⟨u, Walk.cons h₁ (q.concat h₂.symm), ?_, ?_⟩
  · rw [Walk.cons_isCycle_iff]
    refine ⟨(Walk.isPath_concat _).mpr ⟨hqpath, hu⟩, ?_⟩
    rw [Walk.edges_concat, List.concat_eq_append, List.mem_append, List.mem_singleton]
    rintro (hmem | heq)
    · exact hu (q.fst_mem_support_of_mem_edges hmem)
    · rcases Sym2.eq_iff.mp heq with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact h₂.ne h1
      · exact hne h2
  · rw [Walk.length_cons, Walk.length_concat, hqlen]
    omega

/-- In a `C_k`-free graph the start `a` of a longest path has all its neighbours on the path, and no
two of them at positions differing by `k - 2`; shifting by `k - 2` is an injection from the
neighbour positions `≤ length - (k - 2)` into the non-neighbour positions, so
`2 · deg a ≤ length + (k - 2)`. -/
theorem two_mul_degree_le_of_longest_path {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ} (hk : 3 ≤ k)
    (hfree : ¬ (cycleGraph k).IsContained G) {a b : V} {p : G.Walk a b} (hp : p.IsPath)
    (hmax : ∀ (u' v' : V) (p' : G.Walk u' v'), p'.IsPath → p'.length ≤ p.length) :
    2 * G.degree a ≤ p.length + (k - 2) := by
  obtain ⟨N, hN⟩ : ∃ N : Finset ℕ,
      N = (Finset.Icc 1 p.length).filter (fun i => G.Adj a (p.getVert i)) := ⟨_, rfl⟩
  have hmemN : ∀ i, i ∈ N ↔ (1 ≤ i ∧ i ≤ p.length) ∧ G.Adj a (p.getVert i) := fun i => by
    rw [hN, Finset.mem_filter, Finset.mem_Icc]
  have hsub : G.neighborFinset a ⊆ N.image p.getVert := by
    intro w hw
    rw [mem_neighborFinset] at hw
    have hwp : w ∈ p.support := by
      by_contra hnot
      have := hmax _ _ (Walk.cons hw.symm p) (hp.cons hnot)
      rw [Walk.length_cons] at this
      omega
    obtain ⟨i, rfl, hi⟩ := Walk.mem_support_iff_exists_getVert.mp hwp
    rw [Finset.mem_image]
    refine ⟨i, (hmemN i).mpr ⟨⟨?_, hi⟩, hw⟩, rfl⟩
    by_contra h0
    have : i = 0 := by omega
    subst this
    rw [Walk.getVert_zero] at hw
    exact hw.ne rfl
  have hdeg : G.degree a ≤ N.card := by
    have h1 := Finset.card_le_card hsub
    rw [card_neighborFinset_eq_degree, Finset.card_image_of_injOn] at h1
    · exact h1
    · intro i hi i' hi' hii'
      have hi1 := ((hmemN i).mp (Finset.mem_coe.mp hi)).1
      have hi2 := ((hmemN i').mp (Finset.mem_coe.mp hi')).1
      exact hp.getVert_injOn (by simp; omega) (by simp; omega) hii'
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : Finset ℕ, N₁ = N.filter (fun i => i + (k - 2) ≤ p.length) := ⟨_, rfl⟩
  have hmemN₁ : ∀ i, i ∈ N₁ ↔ i ∈ N ∧ i + (k - 2) ≤ p.length := fun i => by
    rw [hN₁, Finset.mem_filter]
  have hNsub : N ⊆ Finset.Icc 1 p.length := fun i hi => Finset.mem_Icc.mpr ((hmemN i).mp hi).1
  have hN₁sub : N₁ ⊆ N := fun i hi => ((hmemN₁ i).mp hi).1
  -- shifting by `k - 2` maps `N₁` into `Icc 1 L \ N`
  have hshift : N₁.card ≤ ((Finset.Icc 1 p.length) \ N).card := by
    refine Finset.card_le_card_of_injOn (fun i => i + (k - 2)) ?_ ?_
    · intro i hi
      obtain ⟨hiN, hik⟩ := (hmemN₁ i).mp (Finset.mem_coe.mp hi)
      obtain ⟨⟨hi1, hi2⟩, hadj⟩ := (hmemN i).mp hiN
      refine Finset.mem_coe.mpr (Finset.mem_sdiff.mpr ⟨Finset.mem_Icc.mpr
        ⟨by show 1 ≤ i + (k - 2); omega, by show i + (k - 2) ≤ p.length; exact hik⟩, fun h => ?_⟩)
      have hadj' := ((hmemN _).mp h).2
      exact hfree (cycleGraph_isContained_of_two_chords hp hi1 hk hik hadj hadj')
    · intro i _ i' _ h
      simpa using h
  have h2 : ((Finset.Icc 1 p.length) \ N).card + N.card = p.length := by
    rw [Finset.card_sdiff_add_card_eq_card hNsub, Nat.card_Icc]
    omega
  -- `N \ N₁` lies in the last `k - 2` positions
  have h3 : N.card ≤ N₁.card + (k - 2) := by
    have hsub' : N \ N₁ ⊆ Finset.Ioc (p.length - (k - 2)) p.length := by
      intro i hi
      obtain ⟨hiN, hiN₁⟩ := Finset.mem_sdiff.mp hi
      obtain ⟨⟨hi1, hi2⟩, _⟩ := (hmemN i).mp hiN
      refine Finset.mem_Ioc.mpr ⟨?_, hi2⟩
      by_contra hle
      exact hiN₁ ((hmemN₁ i).mpr ⟨hiN, by omega⟩)
    have h5 := Finset.card_le_card hsub'
    rw [Nat.card_Ioc] at h5
    have h4 : (N \ N₁).card + N₁.card = N.card := Finset.card_sdiff_add_card_eq_card hN₁sub
    omega
  omega

/-- `cycleGraph_isContained_of_compl_degree_lt` for any `n ≥ (k - 1) * m + 1` vertices. -/
theorem cycleGraph_isContained_of_compl_degree_lt' (k m n : ℕ) (hm1 : 1 ≤ m) (hn : (k - 1) * m + 1 ≤ n)
    (C : SimpleGraph (Fin n)) [DecidableRel C.Adj] (hdeg : ∀ x, Cᶜ.degree x < m) :
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

/-! ### The matching sub-case (`H` of maximum degree 1): a blue edge absorbs an isolated edge of `H` -/

/-- Extending a copy of `H - {u, v}` by an edge `x y` of `G`, when `u v` is an isolated edge of `H`. -/
theorem isContained_of_extend_edge {W V : Type*} [DecidableEq W] (H : SimpleGraph W) (u v : W)
    (huv : H.Adj u v) (hu : ∀ w, H.Adj u w → w = v) (hv : ∀ w, H.Adj v w → w = u)
    (G : SimpleGraph V) (f : Copy (H.induce ({u, v}ᶜ : Set W)) G) (x y : V) (hxy : G.Adj x y)
    (hx : ∀ w, f w ≠ x) (hy : ∀ w, f w ≠ y) : H.IsContained G := by
  have hmem : ∀ w : W, w ≠ u → w ≠ v → w ∈ ({u, v}ᶜ : Set W) := fun w h1 h2 => by
    simp [h1, h2]
  have hne : u ≠ v := huv.ne
  let g : W → V := fun w => if h : w = u then x else if h' : w = v then y else f ⟨w, hmem w h h'⟩
  have gu : g u = x := by simp [g]
  have gv : g v = y := by simp [g, hne.symm]
  have gw : ∀ w (h : w ≠ u) (h' : w ≠ v), g w = f ⟨w, hmem w h h'⟩ := fun w h h' => by
    simp [g, h, h']
  refine ⟨⟨⟨g, ?_⟩, ?_⟩⟩
  · intro a b hab
    by_cases ha : a = u
    · subst ha
      have hb := hu b hab
      subst hb
      rw [gu, gv]
      exact hxy
    by_cases ha' : a = v
    · subst ha'
      have hb := hv b hab
      subst hb
      rw [gu, gv]
      exact hxy.symm
    have hb : b ≠ u := fun h => by subst h; exact ha' (hu a hab.symm)
    have hb' : b ≠ v := fun h => by subst h; exact ha (hv a hab.symm)
    rw [gw a ha ha', gw b hb hb']
    exact f.toHom.map_adj (induce_adj.mpr hab)
  · intro a b h
    change g a = g b at h
    by_cases ha : a = u <;> by_cases hb : b = u
    · rw [ha, hb]
    · subst ha
      rw [gu] at h
      by_cases hb' : b = v
      · subst hb'
        rw [gv] at h
        exact absurd h hxy.ne
      · rw [gw b hb hb'] at h
        exact absurd h.symm (hx _)
    · subst hb
      rw [gu] at h
      by_cases ha' : a = v
      · subst ha'
        rw [gv] at h
        exact absurd h.symm hxy.ne
      · rw [gw a ha ha'] at h
        exact absurd h (hx _)
    · by_cases ha' : a = v <;> by_cases hb' : b = v
      · rw [ha', hb']
      · subst ha'
        rw [gv, gw b hb hb'] at h
        exact absurd h.symm (hy _)
      · subst hb'
        rw [gv, gw a ha ha'] at h
        exact absurd h (hy _)
      · rw [gw a ha ha', gw b hb hb'] at h
        exact congrArg Subtype.val (f.injective h)

/-- The core for `H` of maximum degree at most 1 (a matching plus isolated vertices), by induction on
`m`: a blue edge `x y` exists unless red is complete (then red `C_k`), and it absorbs an edge `u v` of
`H`; the rest of `H` is embedded by induction in the colouring minus `x, y`. -/
theorem core_matching (k : ℕ) (hk : 3 ≤ k) (m : ℕ) :
    ∀ (W : Type) [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj], (∀ w, H.degree w ≤ 1) →
    H.edgeSet.ncard = m → ∀ n : ℕ, Fintype.card W ≤ n → (k - 1) * m + 1 ≤ n →
    ∀ C : SimpleGraph (Fin n), (cycleGraph k).IsContained C ∨ H.IsContained Cᶜ := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro W _ H _ hdeg hm n hWn hn C
  classical
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    have hbot : H = ⊥ := edgeSet_eq_empty.mp ((Set.ncard_eq_zero).mp hm)
    rw [hbot]
    right
    rw [bot_isContained_iff_card_le, Fintype.card_fin]
    exact hWn
  · obtain ⟨u, v, huv⟩ : ∃ a b, H.Adj a b := by
      by_contra hcon
      push Not at hcon
      have hbot : H = ⊥ := by
        ext a b
        simp only [bot_adj, iff_false]
        exact hcon a b
      rw [hbot, edgeSet_bot, Set.ncard_empty] at hm
      omega
    have hne : u ≠ v := huv.ne
    have honly : ∀ a b c, H.Adj a b → H.Adj a c → b = c := by
      intro a b c hab hac
      by_contra hbc
      have h2 : 2 ≤ H.degree a := by
        rw [← card_neighborFinset_eq_degree]
        have hsub : ({b, c} : Finset W) ⊆ H.neighborFinset a := by
          intro z hz
          rw [Finset.mem_insert, Finset.mem_singleton] at hz
          rw [mem_neighborFinset]
          rcases hz with rfl | rfl
          · exact hab
          · exact hac
        have := Finset.card_le_card hsub
        rwa [Finset.card_pair_eq_two_iff.mpr hbc] at this
      have := hdeg a
      omega
    have hu : ∀ w, H.Adj u w → w = v := fun w hw => honly u w v hw huv
    have hv : ∀ w, H.Adj v w → w = u := fun w hw => honly v w u hw huv.symm
    have hkm : (k - 1) * 1 ≤ (k - 1) * m := Nat.mul_le_mul_left _ hpos
    by_cases hC : Cᶜ = ⊥
    · left
      rw [compl_eq_bot.mp hC]
      exact cycleGraph_isContained_top (by omega)
    · obtain ⟨x, y, hxy⟩ := ne_bot_iff_exists_adj.mp hC
      have hxy' : x ≠ y := hxy.ne
      -- `H - {u, v}`
      have hsupp : (H.deleteEdges {s(u, v)}).support ⊆ ({u, v}ᶜ : Set W) := by
        intro w hw
        rw [mem_support] at hw
        obtain ⟨z, hz⟩ := hw
        rw [deleteEdges_adj, Set.mem_singleton_iff] at hz
        simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        refine ⟨fun h => ?_, fun h => ?_⟩
        · subst h
          exact hz.2 (by rw [hu z hz.1])
        · subst h
          exact hz.2 (by rw [hv z hz.1, Sym2.eq_swap])
      have hind : H.induce ({u, v}ᶜ : Set W) = (H.deleteEdges {s(u, v)}).induce ({u, v}ᶜ : Set W) := by
        ext a b
        rw [induce_adj, induce_adj, deleteEdges_adj, Set.mem_singleton_iff]
        refine ⟨fun h => ⟨h, fun heq => ?_⟩, fun h => h.1⟩
        have ha := a.2
        rcases Sym2.eq_iff.mp heq with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact ha (by rw [h1]; simp)
        · exact ha (by rw [h1]; simp)
      have hH' : (H.induce ({u, v}ᶜ : Set W)).edgeSet.ncard = m - 1 := by
        have h1 : (H.induce ({u, v}ᶜ : Set W)).edgeSet =
            ((H.deleteEdges {s(u, v)}).induce ({u, v}ᶜ : Set W)).edgeSet := by rw [hind]
        rw [h1, ← coe_edgeFinset, Set.ncard_coe_finset,
          card_edgeFinset_induce_of_support_subset hsupp, ← Set.ncard_coe_finset, coe_edgeFinset,
          edgeSet_deleteEdges]
        have := Set.ncard_sdiff_singleton_add_one ((mem_edgeSet H).mpr huv)
        omega
      have hdeg' : ∀ w, (H.induce ({u, v}ᶜ : Set W)).degree w ≤ 1 := fun w =>
        ((Copy.induce H _).degree_le w).trans (hdeg w)
      have hcard' : Fintype.card ({u, v}ᶜ : Set W) = Fintype.card W - 2 := by
        have h2 : Fintype.card ({u, v} : Set W) = 2 := by
          rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, Set.ncard_pair hne]
        rw [Fintype.card_compl_set, h2]
      -- the colouring minus `x, y`
      obtain ⟨S, hS⟩ : ∃ S : Finset (Fin n), S = (Finset.univ.erase x).erase y := ⟨_, rfl⟩
      have hScard : S.card = n - 2 := by
        rw [hS, Finset.card_erase_of_mem, Finset.card_erase_of_mem (Finset.mem_univ _),
          Finset.card_univ, Fintype.card_fin]
        · omega
        · exact Finset.mem_erase.mpr ⟨hxy'.symm, Finset.mem_univ _⟩
      let e : Fin S.card ↪ Fin n := (S.orderEmbOfFin rfl).toEmbedding
      have hmemS : ∀ z, z ∈ S → z ≠ x ∧ z ≠ y := fun z hz => by
        rw [hS, Finset.mem_erase, Finset.mem_erase] at hz
        exact ⟨hz.2.1, hz.1⟩
      have he : ∀ i, e i ≠ x ∧ e i ≠ y := fun i => hmemS _ (S.orderEmbOfFin_mem rfl i)
      have hkm' : (k - 1) * (m - 1) + (k - 1) * 1 = (k - 1) * m := by
        rw [← Nat.mul_add]
        congr 1
        omega
      rcases ih (m - 1) (by omega) ({u, v}ᶜ : Set W) (H.induce _) hdeg' hH' S.card
          (by rw [hScard, hcard']; omega) (by rw [hScard]; omega) (C.comap e) with hred | hblue
      · exact Or.inl (cycleGraph_isContained_of_comap C e hred)
      · obtain ⟨f⟩ := hblue
        have hle : (C.comap e)ᶜ ≤ Cᶜ.comap e := by
          intro a b hab
          rw [compl_adj, comap_adj] at hab
          rw [comap_adj, compl_adj]
          exact ⟨fun h' => hab.1 (e.injective h'), hab.2⟩
        let g : Copy (H.induce ({u, v}ᶜ : Set W)) Cᶜ :=
          (Embedding.comap e Cᶜ).toCopy.comp ((Copy.ofLE _ _ hle).comp f)
        have hg : ∀ w, g w = e (f w) := fun w => rfl
        right
        exact isContained_of_extend_edge H u v huv hu hv Cᶜ g x y hxy
          (fun w => by rw [hg]; exact (he _).1) (fun w => by rw [hg]; exact (he _).2)

/-- The start of a longest path is adjacent in the complement to every vertex off the path. -/
theorem compl_adj_of_longest_path_of_notMem {V : Type*} {G : SimpleGraph V} {a b : V}
    {p : G.Walk a b} (hp : p.IsPath)
    (hmax : ∀ (u' v' : V) (p' : G.Walk u' v'), p'.IsPath → p'.length ≤ p.length) {w : V}
    (hw : w ∉ p.support) : Gᶜ.Adj a w := by
  rw [compl_adj]
  refine ⟨fun h => hw (h ▸ p.start_mem_support), fun hadj => ?_⟩
  have := hmax _ _ (Walk.cons hadj.symm p) (hp.cons hw)
  rw [Walk.length_cons] at this
  omega

/-! ### Reduction to connected support: a closed vertex set splits `H` into two pieces, each embedded
by induction (the piece without isolated vertices first, in the whole colouring; the other in what
is left), and the two copies are glued. -/

/-- Gluing a copy of `H[S]` in `Cᶜ` with a copy of `H[Sᶜ]` in the colouring restricted along `e`,
whose image avoids the first copy, when no edge of `H` crosses `S`. -/
theorem isContained_of_closed_split {W : Type*} (H : SimpleGraph W) (S : Set W) [DecidablePred (· ∈ S)]
    (hS : ∀ a b, H.Adj a b → (a ∈ S ↔ b ∈ S)) {n : ℕ} (C : SimpleGraph (Fin n))
    (f₂ : Copy (H.induce S) Cᶜ) {b : ℕ} (e : Fin b ↪ Fin n) (hdisj : ∀ i w, e i ≠ f₂ w)
    (f₁ : Copy (H.induce (Sᶜ : Set W)) (C.comap e)ᶜ) : H.IsContained Cᶜ := by
  let g : W → Fin n := fun w => if h : w ∈ S then f₂ ⟨w, h⟩ else e (f₁ ⟨w, h⟩)
  have gin : ∀ w (h : w ∈ S), g w = f₂ ⟨w, h⟩ := fun w h => by simp [g, h]
  have gout : ∀ w (h : w ∉ S), g w = e (f₁ ⟨w, h⟩) := fun w h => by simp [g, h]
  refine ⟨⟨⟨g, ?_⟩, ?_⟩⟩
  · intro a b hab
    by_cases ha : a ∈ S
    · have hb : b ∈ S := (hS a b hab).mp ha
      rw [gin a ha, gin b hb]
      exact f₂.toHom.map_adj (induce_adj.mpr hab)
    · have hb : b ∉ S := fun hb => ha ((hS a b hab).mpr hb)
      rw [gout a ha, gout b hb]
      have h1 := f₁.toHom.map_adj ((induce_adj (s := (Sᶜ : Set W)) (u := ⟨a, ha⟩) (v := ⟨b, hb⟩)).mpr hab)
      rw [compl_adj, comap_adj] at h1
      rw [compl_adj]
      exact ⟨fun h' => h1.1 (e.injective h'), h1.2⟩
  · intro a b h
    change g a = g b at h
    by_cases ha : a ∈ S <;> by_cases hb : b ∈ S
    · rw [gin a ha, gin b hb] at h
      exact congrArg Subtype.val (f₂.injective h)
    · rw [gin a ha, gout b hb] at h
      exact absurd h.symm (hdisj _ _)
    · rw [gout a ha, gin b hb] at h
      exact absurd h (hdisj _ _)
    · rw [gout a ha, gout b hb] at h
      exact congrArg Subtype.val (f₁.injective (e.injective h))

/-- When no edge of `H` crosses `S`, the edges of `H` are those of `H[S]` and those of `H[Sᶜ]`. -/
theorem ncard_edgeSet_induce_add_ncard_edgeSet_induce_compl {W : Type} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (S : Set W) [DecidablePred (· ∈ S)]
    (hS : ∀ a b, H.Adj a b → (a ∈ S ↔ b ∈ S)) :
    (H.induce S).edgeSet.ncard + (H.induce (Sᶜ : Set W)).edgeSet.ncard = H.edgeSet.ncard := by
  rw [← coe_edgeFinset, Set.ncard_coe_finset, ← coe_edgeFinset, Set.ncard_coe_finset,
    ← coe_edgeFinset, Set.ncard_coe_finset, ← Finset.card_map (Function.Embedding.subtype (· ∈ S)).sym2Map,
    ← Finset.card_map (Function.Embedding.subtype (· ∈ (Sᶜ : Set W))).sym2Map, map_edgeFinset_induce,
    map_edgeFinset_induce]
  have hsub : H.edgeFinset ∩ S.toFinset.sym2 ⊆ H.edgeFinset := Finset.inter_subset_left
  have hdiff : H.edgeFinset \ (H.edgeFinset ∩ S.toFinset.sym2) =
      H.edgeFinset ∩ (Sᶜ : Set W).toFinset.sym2 := by
    ext x
    induction x using Sym2.ind with
    | _ a b =>
    rw [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_inter, Finset.mem_sym2_iff, Finset.mem_sym2_iff]
    simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq, Set.mem_toFinset, Set.mem_compl_iff]
    constructor
    · rintro ⟨hx, hx'⟩
      have hadj : H.Adj a b := (mem_edgeFinset.mp hx)
      refine ⟨hx, ?_, ?_⟩
      · intro ha
        exact hx' ⟨hx, ha, (hS a b hadj).mp ha⟩
      · intro hb
        exact hx' ⟨hx, (hS a b hadj).mpr hb, hb⟩
    · rintro ⟨hx, ha, hb⟩
      exact ⟨hx, fun h => ha h.2.1⟩
  have := Finset.card_sdiff_add_card_eq_card hsub
  rw [hdiff] at this
  omega

/-! ### Isolated vertices and connectedness -/

/-- A copy of `H` restricted to its support, in a graph on at least `#W` vertices, extends to a copy
of `H`: the isolated vertices go to unused vertices. -/
theorem isContained_of_induce_support {W V : Type*} [Fintype W] [Fintype V] [DecidableEq V]
    (H : SimpleGraph W) [DecidableRel H.Adj] (G : SimpleGraph V)
    (hWV : Fintype.card W ≤ Fintype.card V) (h : (H.induce H.support).IsContained G) :
    H.IsContained G := by
  classical
  obtain ⟨f⟩ := h
  have hcard : Fintype.card (H.supportᶜ : Set W) ≤
      Fintype.card ((Set.range fun w => f w)ᶜ : Set V) := by
    rw [Fintype.card_compl_set, Fintype.card_compl_set,
      Set.card_range_of_injective (f := fun w => f w) (fun a b hab => f.injective hab)]
    omega
  obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le hcard
  let φ : W → V := fun w => if hw : w ∈ H.support then f ⟨w, hw⟩ else (g ⟨w, hw⟩).1
  have φin : ∀ w (hw : w ∈ H.support), φ w = f ⟨w, hw⟩ := fun w hw => by simp [φ, hw]
  have φout : ∀ w (hw : w ∉ H.support), φ w = (g ⟨w, hw⟩).1 := fun w hw => by simp [φ, hw]
  have hg : ∀ w (hw : w ∉ H.support) w', (g ⟨w, hw⟩).1 ≠ f w' := fun w hw w' heq =>
    (g ⟨w, hw⟩).2 ⟨w', heq.symm⟩
  refine ⟨⟨⟨φ, ?_⟩, ?_⟩⟩
  · intro a b hab
    have ha : a ∈ H.support := hab.mem_support_left
    have hb : b ∈ H.support := hab.symm.mem_support_left
    rw [φin a ha, φin b hb]
    exact f.toHom.map_adj (induce_adj.mpr hab)
  · intro a b h
    change φ a = φ b at h
    by_cases ha : a ∈ H.support <;> by_cases hb : b ∈ H.support
    · rw [φin a ha, φin b hb] at h
      exact congrArg Subtype.val (f.injective h)
    · rw [φin a ha, φout b hb] at h
      exact absurd h.symm (hg b hb _)
    · rw [φout a ha, φin b hb] at h
      exact absurd h (hg a ha _)
    · rw [φout a ha, φout b hb] at h
      exact congrArg Subtype.val (g.injective (Subtype.ext h))

/-- If `H` has an edge, no isolated vertices, and no closed vertex set with edges on both sides, then
`H` is connected, so `#W ≤ m + 1`. -/
theorem card_le_ncard_edgeSet_add_one_of_no_split {W : Type} [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (h0 : ∀ v, 0 < H.degree v) {a₀ b₀ : W} (hab₀ : H.Adj a₀ b₀)
    (hsplit : ∀ S : Set W, (∀ a b, H.Adj a b → (a ∈ S ↔ b ∈ S)) → (∀ w ∈ S, ∃ z, H.Adj w z) →
      0 < (H.induce S).edgeSet.ncard → (H.induce (Sᶜ : Set W)).edgeSet.ncard = 0) :
    Fintype.card W ≤ H.edgeSet.ncard + 1 := by
  classical
  obtain ⟨S, hSdef⟩ : ∃ S : Set W, S = (H.connectedComponentMk a₀).supp := ⟨_, rfl⟩
  have hmemS : ∀ w, w ∈ S ↔ H.connectedComponentMk w = H.connectedComponentMk a₀ := fun w => by
    rw [hSdef, ConnectedComponent.mem_supp_iff]
  have hS : ∀ a b, H.Adj a b → (a ∈ S ↔ b ∈ S) := fun a b hab => by
    rw [hSdef]
    exact ConnectedComponent.mem_supp_congr_adj _ hab
  have hsupp : ∀ w ∈ S, ∃ z, H.Adj w z := fun w _ => (H.degree_pos_iff_exists_adj w).mp (h0 w)
  have ha₀ : a₀ ∈ S := (hmemS a₀).mpr rfl
  have hb₀ : b₀ ∈ S := (hS a₀ b₀ hab₀).mp ha₀
  have hpos : 0 < (H.induce S).edgeSet.ncard := by
    rw [Set.ncard_pos]
    exact ⟨s(⟨a₀, ha₀⟩, ⟨b₀, hb₀⟩), (mem_edgeSet _).mpr (induce_adj.mpr hab₀)⟩
  have hzero := hsplit S hS hsupp hpos
  rw [Set.ncard_eq_zero] at hzero
  have hall : ∀ w, w ∈ S := by
    intro w
    by_contra hw
    obtain ⟨z, hz⟩ := (H.degree_pos_iff_exists_adj w).mp (h0 w)
    have hz' : z ∉ S := fun hz' => hw ((hS w z hz).mpr hz')
    have hmem : s(⟨w, hw⟩, ⟨z, hz'⟩) ∈ (H.induce (Sᶜ : Set W)).edgeSet :=
      (mem_edgeSet _).mpr ((induce_adj (s := (Sᶜ : Set W)) (u := ⟨w, hw⟩) (v := ⟨z, hz'⟩)).mpr hz)
    rw [hzero] at hmem
    exact hmem
  have hconn : H.Connected := by
    rw [connected_iff_exists_forall_reachable]
    exact ⟨a₀, fun w => (ConnectedComponent.exact ((hmemS w).mp (hall w))).symm⟩
  have := hconn.card_vert_le_card_edgeSet_add_one
  rwa [Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at this

set_option maxHeartbeats 400000 in
/-- The generalised core, by strong induction on the number of edges `m`: `H` may have isolated
vertices, and the colouring lives on any `n ≥ (k - 1) * m + 1` vertices with `n ≥ #W`. -/
theorem core_all (k : ℕ) (hk : 3 ≤ k) (m : ℕ) :
    ∀ (W : Type) [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj], (∀ v, 0 < H.degree v) →
    H.edgeSet.ncard = m → ∀ n : ℕ, Fintype.card W ≤ n → (k - 1) * m + 1 ≤ n →
    ∀ C : SimpleGraph (Fin n), (cycleGraph k).IsContained C ∨ H.IsContained Cᶜ := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro W _ H _ h0 hm n hWn hn C
  classical
  -- the induction hypothesis for graphs that may have isolated vertices
  have Q : ∀ m' < m, ∀ (W' : Type) [Fintype W'] (H' : SimpleGraph W') [DecidableRel H'.Adj],
      H'.edgeSet.ncard = m' → ∀ n' : ℕ, Fintype.card W' ≤ n' → (k - 1) * m' + 1 ≤ n' →
      ∀ C' : SimpleGraph (Fin n'), (cycleGraph k).IsContained C' ∨ H'.IsContained C'ᶜ := by
    intro m' hm' W' _ H' _ hm'' n' hW' hn' C'
    classical
    have hsupp : Fintype.card H'.support ≤ n' :=
      (Fintype.card_le_of_injective _ Subtype.val_injective).trans hW'
    have hm''' : (H'.induce H'.support).edgeSet.ncard = m' := by
      rw [← coe_edgeFinset, Set.ncard_coe_finset, card_edgeFinset_induce_support,
        ← Set.ncard_coe_finset, coe_edgeFinset, hm'']
    rcases ih m' hm' H'.support (H'.induce H'.support) (fun v => by
        rw [degree_induce_support]
        obtain ⟨z, hz⟩ := (H'.mem_support).mp v.2
        exact (H'.degree_pos_iff_exists_adj _).mpr ⟨z, hz⟩) hm''' n' hsupp hn' C' with hred | hblue
    · exact Or.inl hred
    · exact Or.inr (isContained_of_induce_support H' C'ᶜ (by rw [Fintype.card_fin]; exact hW') hblue)
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    have hbot : H = ⊥ := edgeSet_eq_empty.mp ((Set.ncard_eq_zero).mp hm)
    rw [hbot]
    right
    rw [bot_isContained_iff_card_le, Fintype.card_fin]
    exact hWn
  · obtain ⟨a₀, b₀, hab₀⟩ : ∃ a b, H.Adj a b := by
      by_contra hcon
      push Not at hcon
      have hbot : H = ⊥ := by
        ext a b
        simp only [bot_adj, iff_false]
        exact hcon a b
      rw [hbot, edgeSet_bot, Set.ncard_empty] at hm
      omega
    haveI : Nonempty W := ⟨a₀⟩
    -- Reduction to connected support: a closed set `S` of non-isolated vertices with edges on both sides
    by_cases hsplit : ∃ S : Set W, (∀ a b, H.Adj a b → (a ∈ S ↔ b ∈ S)) ∧ (∀ w ∈ S, ∃ z, H.Adj w z) ∧
        0 < (H.induce S).edgeSet.ncard ∧ 0 < (H.induce (Sᶜ : Set W)).edgeSet.ncard
    · obtain ⟨S, hS, hSsupp, hm₂, hm₁⟩ := hsplit
      have hsum := ncard_edgeSet_induce_add_ncard_edgeSet_induce_compl H S hS
      rw [hm] at hsum
      have hS2 : Fintype.card S ≤ 2 * (H.induce S).edgeSet.ncard := by
        refine card_le_two_mul_ncard_edgeSet (H.induce S) fun w => ?_
        obtain ⟨z, hz⟩ := hSsupp w.1 w.2
        exact (degree_pos_iff_exists_adj _ _).mpr ⟨⟨z, (hS _ _ hz).mp w.2⟩, induce_adj.mpr hz⟩
      have hSW : Fintype.card S ≤ Fintype.card W := Fintype.card_le_of_injective _ Subtype.val_injective
      have hprod : (k - 1) * (H.induce S).edgeSet.ncard + (k - 1) * (H.induce (Sᶜ : Set W)).edgeSet.ncard
          = (k - 1) * m := by rw [← Nat.mul_add, hsum]
      have h2S : 2 * (H.induce S).edgeSet.ncard ≤ (k - 1) * (H.induce S).edgeSet.ncard :=
        Nat.mul_le_mul_right _ (by omega)
      rcases Q _ (by omega) S (H.induce S) rfl n (hSW.trans hWn) (by omega) C with hred | hblue₂
      · exact Or.inl hred
      · obtain ⟨f₂⟩ := hblue₂
        obtain ⟨T, hT⟩ : ∃ T : Finset (Fin n),
            T = Finset.univ \ (Finset.univ.image fun w => f₂ w) := ⟨_, rfl⟩
        have hTcard : T.card = n - Fintype.card S := by
          rw [hT, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
            Finset.card_image_of_injective (f := fun w => f₂ w) _ (fun a b hab => f₂.injective hab),
            Finset.card_univ]
        have hmemT : ∀ z, z ∈ T → ∀ w, z ≠ f₂ w := fun z hz w hzw => by
          rw [hT, Finset.mem_sdiff, Finset.mem_image] at hz
          exact hz.2 ⟨w, Finset.mem_univ _, hzw.symm⟩
        let e : Fin T.card ↪ Fin n := (T.orderEmbOfFin rfl).toEmbedding
        have he : ∀ i w, e i ≠ f₂ w := fun i w => hmemT _ (T.orderEmbOfFin_mem rfl i) w
        have hcS : Fintype.card (Sᶜ : Set W) = Fintype.card W - Fintype.card S := Fintype.card_compl_set S
        rcases Q _ (by omega) (Sᶜ : Set W) (H.induce _) rfl T.card (by rw [hTcard, hcS]; omega)
            (by rw [hTcard]; omega) (C.comap e) with hred | hblue₁
        · exact Or.inl (cycleGraph_isContained_of_comap C e hred)
        · obtain ⟨f₁⟩ := hblue₁
          exact Or.inr (isContained_of_closed_split H S hS C f₂ e he f₁)
    push Not at hsplit
    -- `u` is a vertex of maximum degree in `H`
    obtain ⟨u, hu'⟩ := H.exists_maximal_degree_vertex
    have hu : 0 < H.degree u := by
      rw [← hu']
      exact lt_of_lt_of_le ((H.degree_pos_iff_exists_adj a₀).mpr ⟨b₀, hab₀⟩) (H.degree_le_maxDegree a₀)
    set d := H.degree u with hd
    set m' := m - d with hm'
    have hdm : d ≤ m := by
      rw [← hm]
      exact degree_le_ncard_edgeSet H u
    have hm'lt : m' < m := by omega
    have hH' : (H.induce ({u}ᶜ : Set W)).edgeSet.ncard = m' := by
      rw [ncard_edgeSet_induce_compl_singleton, hm]
    have hcard' : Fintype.card ({u}ᶜ : Set W) = Fintype.card W - 1 := card_compl_singleton' u
    by_cases hx : ∃ x, (k - 1) * m' + 1 ≤ Cᶜ.degree x ∧ Fintype.card W - 1 ≤ Cᶜ.degree x
    · obtain ⟨x, hx1, hx2⟩ := hx
      let e : Fin (Cᶜ.neighborFinset x).card ↪ Fin n := ((Cᶜ.neighborFinset x).orderEmbOfFin rfl).toEmbedding
      have he : ∀ i, Cᶜ.Adj x (e i) := fun i => by
        have := (Cᶜ.neighborFinset x).orderEmbOfFin_mem rfl i
        rwa [mem_neighborFinset] at this
      have hSc : (Cᶜ.neighborFinset x).card = Cᶜ.degree x := card_neighborFinset_eq_degree Cᶜ x
      rcases Q m' hm'lt ({u}ᶜ : Set W) (H.induce _) hH' (Cᶜ.neighborFinset x).card
          (by rw [hcard', hSc]; exact hx2) (by rw [hSc]; exact hx1) (C.comap e) with hred | hblue
      · exact Or.inl (cycleGraph_isContained_of_comap C e hred)
      · exact Or.inr (isContained_compl_of_extend_nbhd C x e he H u hblue)
    · -- every vertex has small blue degree.
      -- Sub-case `D ≤ 1`: `H` is a matching plus isolated vertices; a blue edge absorbs an edge of `H`.
      rcases Nat.lt_or_ge (H.maxDegree) 2 with hD1 | hD2
      · exact core_matching k hk m W H (fun w => by have := H.degree_le_maxDegree w; omega) hm n hWn hn C
      -- Sub-case `D ≥ 2`: in case (i) the red graph has minimum degree ≥ (k-1)·D ≥ 2(k-1).
      -- Take a longest red path; its start has all red neighbours on the path, none at position k-1.
      push Not at hx
      haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
      obtain ⟨x₀, hx₀⟩ := Cᶜ.exists_maximal_degree_vertex
      have hb : ∀ x, Cᶜ.degree x ≤ Cᶜ.degree x₀ := fun x => hx₀ ▸ Cᶜ.degree_le_maxDegree x
      by_contra hcon
      push Not at hcon
      obtain ⟨hfree', hblue⟩ := hcon
      have hfree : ¬ (cycleGraph k).IsContained C := fun ⟨f⟩ => hfree'.false f
      -- some vertex has blue degree ≥ m, else the greedy red clique has k vertices
      have hbm : m ≤ Cᶜ.degree x₀ := by
        by_contra hlt
        push Not at hlt
        exact hfree (cycleGraph_isContained_of_compl_degree_lt' k m n hpos hn C
          (fun y => lt_of_le_of_lt (hb y) hlt))
      obtain ⟨a, b, p, hp, hmax⟩ := Walk.exists_isPath_forall_isPath_length_le_length C
      have hred : ∀ y, C.degree y + Cᶜ.degree y = n - 1 := fun y => by
        have h1 := degree_compl (G := C) (v := y)
        have h2 := C.degree_lt_card_verts y
        rw [Fintype.card_fin] at h1 h2
        omega
      rcases Nat.lt_or_ge (Cᶜ.degree x₀) ((k - 1) * m' + 1) with h1 | h1
      · -- (i): red degree of every vertex ≥ n - 1 - (k-1) m' ≥ (k-1) D ≥ k - 1
        have hD : (k - 1) * m' + (k - 1) * d = (k - 1) * m := by
          rw [← Nat.mul_add]; congr 1; omega
        have hdegL : C.degree a ≤ p.length := by
          by_contra hlt
          push Not at hlt
          have hsub : C.neighborFinset a ⊆ p.support.toFinset.erase a := by
            intro w hw
            rw [mem_neighborFinset] at hw
            rw [Finset.mem_erase, List.mem_toFinset]
            refine ⟨hw.ne.symm, ?_⟩
            by_contra hnot
            have := hmax _ _ (Walk.cons hw.symm p) (hp.cons hnot)
            rw [Walk.length_cons] at this
            omega
          have := Finset.card_le_card hsub
          rw [card_neighborFinset_eq_degree,
            Finset.card_erase_of_mem (List.mem_toFinset.mpr p.start_mem_support),
            List.toFinset_card_of_nodup hp.support_nodup, Walk.length_support] at this
          omega
        have hkL : k - 1 ≤ p.length := by
          have := hred a; have := hb a
          have : (k - 1) * 1 ≤ (k - 1) * d := Nat.mul_le_mul_left _ hu
          omega
        have hL := degree_add_one_le_length_of_longest_path hk hfree hp hmax hkL
        -- no two red neighbours of `a` sit at positions `j` and `j + (k - 2)` on the path
        have hchord : ∀ j, 1 ≤ j → j + (k - 2) ≤ p.length →
            C.Adj a (p.getVert j) → ¬ C.Adj a (p.getVert (j + (k - 2))) := fun j hj hjk h₁ h₂ =>
          hfree (cycleGraph_isContained_of_two_chords hp hj hk hjk h₁ h₂)
        -- density of chords: 2 · red-deg a ≤ length + k - 2, so the red path has ≥ 2(k-1)D - k + 3 vertices
        have h2a := two_mul_degree_le_of_longest_path hk hfree hp hmax
        -- the same for the other end `b` of the path
        have hmax' : ∀ (u' v' : Fin n) (p' : C.Walk u' v'), p'.IsPath → p'.length ≤ p.reverse.length := by
          intro u' v' p' hp'
          rw [Walk.length_reverse]
          exact hmax u' v' p' hp'
        have h2b := two_mul_degree_le_of_longest_path hk hfree hp.reverse hmax'
        rw [Walk.length_reverse] at h2b
        have hLb : p.length < n := hp.length_lt.trans_le (by rw [Fintype.card_fin])
        -- with D ≥ 2 the red graph has minimum degree ≥ 2(k-1) and the longest red path has
        -- length ≥ 4(k-1) - (k-2) = 3k - 2; arithmetic probe for a contradiction
        have hD2' : (k - 1) * 2 ≤ (k - 1) * d := Nat.mul_le_mul_left _ (hu' ▸ hD2)
        -- every vertex off the path is blue to `a`, so blue-deg a ≥ n - 1 - L
        have hoff : (Finset.univ \ p.support.toFinset) ⊆ Cᶜ.neighborFinset a := by
          intro w hw
          rw [Finset.mem_sdiff, List.mem_toFinset] at hw
          rw [mem_neighborFinset]
          exact compl_adj_of_longest_path_of_notMem hp hmax hw.2
        have hoffc := Finset.card_le_card hoff
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
          List.toFinset_card_of_nodup hp.support_nodup, Walk.length_support,
          card_neighborFinset_eq_degree] at hoffc
        -- Second route: embed `H - u` anywhere away from `x₀` (plenty of room), then ask whether the
        -- images of the neighbours of `u` all lie in the blue neighbourhood of `x₀`.
        obtain ⟨R, hR⟩ : ∃ R : Finset (Fin n), R = Finset.univ.erase x₀ := ⟨_, rfl⟩
        have hRcard : R.card = n - 1 := by
          rw [hR, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
        let e : Fin R.card ↪ Fin n := (R.orderEmbOfFin rfl).toEmbedding
        have hmemR : ∀ z, z ∈ R → z ≠ x₀ := fun z hz => by
          rw [hR, Finset.mem_erase] at hz
          exact hz.1
        have he : ∀ i, e i ≠ x₀ := fun i => hmemR _ (R.orderEmbOfFin_mem rfl i)
        have hWm1 : Fintype.card W ≤ m + 1 := by
          rw [← hm]
          exact card_le_ncard_edgeSet_add_one_of_no_split H h0 hab₀
            (fun S h1 h2 h3 => by have := hsplit S h1 h2 h3; omega)
        rcases Q m' hm'lt ({u}ᶜ : Set W) (H.induce _) hH' R.card (by rw [hRcard, hcard']; omega)
            (by rw [hRcard]; omega) (C.comap e) with hred | hblue'
        · exact hfree (cycleGraph_isContained_of_comap C e hred)
        · obtain ⟨f⟩ := hblue'
          have hle : (C.comap e)ᶜ ≤ Cᶜ.comap e := by
            intro a b hab
            rw [compl_adj, comap_adj] at hab
            rw [comap_adj, compl_adj]
            exact ⟨fun h' => hab.1 (e.injective h'), hab.2⟩
          let g : Copy (H.induce ({u}ᶜ : Set W)) Cᶜ :=
            (Embedding.comap e Cᶜ).toCopy.comp ((Copy.ofLE _ _ hle).comp f)
          have hg : ∀ w, g w = e (f w) := fun w => rfl
          by_cases hnbr : ∀ w : ({u}ᶜ : Set W), H.Adj u w → Cᶜ.Adj x₀ (g w)
          · exact hblue.false
              (isContained_of_extend H u Cᶜ g x₀ (fun w => by rw [hg]; exact he _) hnbr).some
          · -- some neighbour `w` of `u` is sent to a red neighbour of `x₀`
            push Not at hnbr
            obtain ⟨w, hw, hred⟩ := hnbr
            have hgw : C.Adj x₀ (g w) := by
              have hne : x₀ ≠ g w := by rw [hg]; exact (he _).symm
              by_contra hcon
              exact hred ((compl_adj C x₀ (g w)).mpr ⟨hne, hcon⟩)
            -- nonlinear arithmetic probe: the products (k-1)m', (k-1)d, 2·deg, the path length and n
            have hprod : (k - 1) * m' + (k - 1) * d = (k - 1) * m := by
              rw [← Nat.mul_add]; congr 1; omega
            nlinarith [hbm, h1, hb a, hb b, hred a, hred b, h2a, h2b, hLb, hoffc, hprod, hD2', hkL, hL, hn, hWm1]
      · -- (ii): all blue degrees ≤ #W - 2, but #W ≤ m + 1 (connected support) and blue-deg x₀ ≥ m
        have h2 := hx x₀ h1
        have hWm1 : Fintype.card W ≤ m + 1 := by
          rw [← hm]
          exact card_le_ncard_edgeSet_add_one_of_no_split H h0 hab₀
            (fun S h1 h2 h3 => by have := hsplit S h1 h2 h3; omega)
        omega

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
  have hW : Fintype.card W ≤ (k - 1) * m + 1 := by
    have h1 := card_le_two_mul_ncard_edgeSet H h0
    rw [hm] at h1
    have h2 : 2 * m ≤ (k - 1) * m := Nat.mul_le_mul_right m (by omega)
    omega
  exact core_all k hk m W H h0 hm _ hW le_rfl C

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
