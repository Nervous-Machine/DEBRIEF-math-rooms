# Reading guide: Challenge_569.lean against Cambie–Freschi Theorem 3 and Erdős problem 569 (gap EG4)

**The Lean statement** (`rooms/Challenge_569.lean`, namespace `Erdos569`; `SimpleGraph.graphRamsey` is copied from
google-deepmind/formal-conjectures):

```lean
theorem cambie_freschi (k : ℕ) (hk : 3 ≤ k) (m : ℕ) (W : Type) [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (h0 : ∀ v, 0 < H.degree v) (hm : H.edgeSet.ncard = m) :
    SimpleGraph.graphRamsey (SimpleGraph.cycleGraph k) H ≤ (k - 1) * m + 1
```

**In words.** For every k ≥ 3 and every finite graph H with m edges and no isolated vertex, the Ramsey number
R(C_k, H) is at most (k − 1)m + 1.

**What the sources say.** Erdős problem 569 asks whether R(C_k, H) ≤ (k − 1)m + 1 for every graph H with m edges
and no isolated vertices (the registrar's reading of erdosproblems.com/569). Cambie and Freschi, arXiv:2606.11174,
Theorem 3, state the bound for k ≥ 3 (the registrar's reading). The reader should check: the definition of
`graphRamsey G H` in the Challenge file (the least n such that every red/blue colouring of K_n has a red copy of G or a
blue copy of H; copies are subgraph containments, not induced); whether the paper's "no isolated vertices" matches
`∀ v, 0 < H.degree v`; whether the paper counts m as the number of edges of H exactly (`H.edgeSet.ncard = m`); and
whether the paper's k range is k ≥ 3 or k ≥ 4 with k = 3 covered separately.

**The one question.** Does the Lean statement say what Theorem 3 and problem 569 say? Answer: agree / disagree (with
the difference) / cannot tell.

Known points of care: `cycleGraph k` for k ≥ 3 is the k-cycle; `graphRamsey` is formal-conjectures' definition, used
verbatim; natural-number subtraction in `(k - 1)` is safe because k ≥ 3.
