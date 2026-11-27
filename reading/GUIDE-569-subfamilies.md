# Reading guide: two theorems proved as by-products of build 5 (results/B5_C108_full_forced/final.lean)

Both compile in the pinned project on the standard three axioms (`#print axioms` recorded in the build 5 record).
Nobody has read them.

```lean
theorem cambie_freschi_four (m : ℕ) (W : Type) [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (h0 : ∀ v, 0 < H.degree v) (hm : H.edgeSet.ncard = m) :
    SimpleGraph.graphRamsey (SimpleGraph.cycleGraph 4) H ≤ 3 * m + 1

theorem cambie_freschi_of_isAcyclic (k : ℕ) (hk : 3 ≤ k) (m : ℕ) (W : Type) [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (hacyc : H.IsAcyclic) (h0 : ∀ v, 0 < H.degree v) (hm : H.edgeSet.ncard = m) :
    SimpleGraph.graphRamsey (SimpleGraph.cycleGraph k) H ≤ (k - 1) * m + 1
```

**In words.** The first: for every graph H with m edges and no isolated vertex, R(C₄, H) ≤ 3m + 1. The second: for
every forest F with m edges and no isolated vertex and every k ≥ 3, R(C_k, F) ≤ (k − 1)m + 1.

**The two questions.** (1) Are these the k = 4 case and the forest case of the Erdős 569 bound, as stated in
GUIDE-569.md, with the same definitions? (2) Are they known results, and if so where (the registrar has not searched
the literature for them and makes no claim of novelty; a reader who knows the cycle-versus-graph Ramsey literature
can say). Answer each: agree / disagree / cannot tell, with references for (2) if known.

Known points of care: `H.IsAcyclic` is Mathlib's acyclicity for simple graphs (a forest); the proofs were produced by a
searcher that had no paper and no blueprint for this file, from the statement and Mathlib alone.
