# Rooms and hinges, build 5: the scaled-down corner

**Question written down first.** Heidi Bennett's equation: the outcome of a machine proof is some function of checker precision, shared foundation, a formal statement, compute, and route knowledge, and the terms trade. The labs' proofs sit in the far corner of that space, unknown hinges with compute spent liberally, and cannot be rerun here. What can be run is the exchange rate on one hinge whose answer exists: how much compute buys how much route, with the checker, foundation and statement fixed and no route given. Registration: [prereg_build_5.yaml](../prereg_build_5.yaml), eight predictions, one amendment.

**The hinge.** Erdős 569's remaining case as the statement-only searcher of build 3 carved it, `core_ge_three_nonstar`: k ≥ 3, m ≥ 3, H not a star, a colouring with a vertex of blue degree at least m; find a red C_k or a blue H. The searcher wrote that it is "the content of the paper" and left it without a check call. The human proof closes it through a second-neighbourhood lemma, a colour-critical edge bound and three literature inputs not in Mathlib. Three fresh searchers started from that same file, with the statement, Mathlib and Lean, and no paper, no rooms, no notes, at attempt caps of 12, 36 and 108. The tool refused any attempt with a sorry anywhere in the file and refused FINAL before the cap.

## Result

| cap | calls | genuine attempts | errors | closed | new helpers proved | file lines | tokens | tokens per attempt | minutes | fit | what it bought |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 12 | 13 | 12 | 12 | no | 20 | 932 | 235,797 | 19,650 | 35 | 0 | the triangle case; the leaf case reduced to the same statement one edge smaller |
| 36 | 37 | 36 | 36 | no | 19 | 1,207 | 355,152 | 9,865 | 61 | 0 | the whole induction on m, proved modulo one explicit hypothesis |
| 108 | 109 | 108 | 108 | no | 94 | 3,483 | 637,423 | 5,902 | 131 | 0 | two complete theorems, every forest and every H against C₄; the open case stated with no induction left |

The start file had 471 lines and 16 lemmas. No refusals in any arm. No hedge at any FINAL. No cap reached: the 108 arm used 131 of 600 minutes and a tenth of its tokens.

**Predictions.** Held: P1 and P2 (no closure at any cap, so the falsifier did not fire), P5 (fit zero at every cap), P6 (no hedges). Held in substance and missed by the letter: P3, since new declarations ran 20, 19, 94 while the content grew at every step; P8, since errors did not converge at 12 or 108 but fell from a median of 2 to 1 at 36 as the search narrowed to one goal. Missed: P7, because the 108 arm finished inside every cap; and P4 at cap 108 by the registrar's reading, below.

## What each cap bought

**Cap 12** proved the triangle case outright and built `core_step_leaf`: given the statement for H minus a leaf on (k−1)(m−1)+1 vertices, the statement for H follows. That is an inductive step the lemma as drawn cannot use on itself. From the fifth attempt the open sub-cases were marked with the no-op tactic `skip` and a comment naming the residual, so they surfaced as errors rather than sorry.

**Cap 36** proved the entire strong induction on the number of edges as `core_all_of_gap`, on the standard axioms, with the open case as an explicit hypothesis: for connected H without isolated vertices and maximum degree D ≥ 2, any colouring of at least (k−1)m+1 vertices in which every blue degree is at most (k−1)(m−D) contains a red C_k or a blue H. Matchings (`core_matching`), disconnected graphs (a closed-split gluing lemma), stars, isolated vertices and the large-blue-degree case are all discharged. The forced lemma applies the induction and fails at the one `omega` that cannot discharge the hypothesis. The searcher wrote that a red-only argument cannot close it because a bipartite red graph satisfies every hypothesis for odd k.

**Cap 108** proved two theorems nobody asked for, both on the standard three axioms:

```lean
theorem cambie_freschi_four (m : ℕ) (W : Type) [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (h0 : ∀ v, 0 < H.degree v) (hm : H.edgeSet.ncard = m) :
    SimpleGraph.graphRamsey (SimpleGraph.cycleGraph 4) H ≤ 3 * m + 1

theorem cambie_freschi_of_isAcyclic (k : ℕ) (hk : 3 ≤ k) (m : ℕ) (W : Type) [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (hacyc : H.IsAcyclic) (h0 : ∀ v, 0 < H.degree v) (hm : H.edgeSet.ncard = m) :
    SimpleGraph.graphRamsey (SimpleGraph.cycleGraph k) H ≤ (k - 1) * m + 1
```

and reduced the general case to `core_of_residue_pure`, a configuration with no induction hypothesis left: a connected H′ with minimum degree 2, maximum degree Δ with (k−1)Δ ≤ (k−2)(|W′|−1), m′ ≥ 4, k ≠ 4, and a colouring of K_{(k−1)m′+1} whose red graph is C_k-free, not (k−1)-colourable, has every red degree in [(k−1)Δ, (k−2)(|W′|−1)], dominates every small set, carries a red K_{2,k−1} at every vertex and a red C₄. The forced lemma follows from the impossibility of that configuration, which was not shown.

## The route-recovery reading (P4)

The paper's two distinctive moves are Lemma 7, which closes a k-cycle through hub vertices adjacent to a path in the second neighbourhood, and Proposition 10, an edge lower bound for graphs of minimum degree 2 that are not (t−1)-colourable. In the 108 file the registrar reads the first as present in mechanism and applied to the red graph:

```lean
theorem cycleGraph_isContained_of_isPath_apex {V : Type*} (G : SimpleGraph V) (k : ℕ) (hk : 3 ≤ k)
    {a b : V} (p : G.Walk a b) (hp : p.IsPath) (hlen : p.length = k - 2) (z : V) (hz : z ∉ p.support)
    (hza : G.Adj z a) (hbz : G.Adj b z) : (cycleGraph k).IsContained G
```

with two-apex and two-path variants, and `layers_of_residue`, which builds k disjoint neighbourhood layers from the condition that no embedding of H′ minus a vertex extends. The second move does not appear; the file has only a chromatic condition on red and a pigeonhole (`isContained_of_red_colorable`). This is a reading of statements by a registrar who has read the paper, labelled as such. By the letter P4 is missed at cap 108 on the first move.

## What it means

**On this hinge, compute bought structure and not the route.** Three doses, three honest residuals, and the residual got sharper each time: a case, then the whole induction minus one hypothesis, then that hypothesis with the induction removed and two sub-families closed outright. Closure did not move. The route through the dense configuration is what the paper supplies and what a hundred and eight attempts from the statement did not find.

**The cost per attempt fell as the cap rose, and no cap was reached.** Tokens per attempt went from 19,650 to 5,902. The budget was not the limit in any arm, as it was not in builds 1 to 4. What bounded each arm was the searcher's own stopping at its cap. Whether a thousand attempts would close the configuration is not tested and is not implied either way.

**Three ways of carrying a hole under a no-sorry rule.** Placeholders with comments, an explicit hypothesis of a proved lemma, and attempts that each fail at a stated gap. The second is the Hassana shape, induced by the rule and disclosed by the searcher. None moved the hypothesis into the forced lemma's statement. The fit did not appear at any cap, which makes eighteen arms over five builds.

**For the equation.** On a hinge inside the distribution, build 4 showed compute buys the route at once. On this hinge outside it, compute bought every sub-case the human proof covers in passing and did not buy the one idea the paper exists to supply. That is one point on the exchange rate, at a budget a subscription can afford, and it is consistent with the archive traces: a chain of cheap known structure, and the expense at the hinge.

**What this does not say.** One model, one hinge, one run per cap. The two complete theorems are unread by a human. The registrar's P4 reading is a reading.

## Files

[prereg_build_5.yaml](../prereg_build_5.yaml) · `results/B5_C12_full_forced/`, `results/B5_C36_full_forced/`, `results/B5_C108_full_forced/` (each: `calls.tsv`, `attempts/`, `final.lean`, `score.json`, `forced.json`, `forced.conf`, `work/NOTES.md`) · instruments in `rooms/` (`SEARCHER_CORNER_PROMPT.md`, `check.sh`, `forced_check.py`, `forced_score.py`, `score.py`, `audit.py`).
