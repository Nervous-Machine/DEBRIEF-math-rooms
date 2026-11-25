# R3_none searcher notes (Rooms766.lean)

Regime R3_none: no checker until FINAL. The whole file was written without compiling anything;
every Mathlib name used was verified by grep against the pinned Mathlib source first.

## Nodes

All 15 nodes plus ROOT are stated exactly as in `blueprint_nodes.yaml` (no statement changed);
the Challenge header, `forcingNumber` and the root statement are verbatim.

Believed proved (as written, before the FINAL compile):
- N1, N2: parity split via `Nat.even_or_odd'`, polynomial identities by `ring`, floor division
  closed by `omega` with the squares as atoms (fallback: `Nat.mul_div_cancel`, `Nat.add_mul_div_right`).
- N3: by contradiction; `Nat.mul_le_mul` supplies the two nonlinear inequalities, `omega` finishes.
- N4: minimal-degree vertex + `Finset.card_nsmul_le_sum` + handshake (fallback: a `calc` with `Finset.sum_le_sum`).
- N5, N8: direct from N3/N4 and N6.
- N6: `card_edgeFinset_induce_compl_singleton` + `card_edgeFinset_deleteIncidenceSet`.
- N7: `Fintype.card_compl_set` + `Set.card_singleton` (fallbacks via `Fintype.card_of_subtype`).
- N9: `SimpleGraph.Copy.induce`.
- N10: `Set.ncard_eq_toFinset_card'` (fallback `coe_edgeFinset` + `ncard_coe_finset`).
- N11: `overFin`/`overFinIso`, edge count transferred with `Nat.card_congr` on `Iso.mapEdgeSet`
  (fallback: `classical` + `Iso.card_edgeFinset_eq`).
- N12: ordinary induction on N (rather than `Nat.le_induction`); the case k = N+1 uses N11,
  the case k ≤ N deletes a low-degree vertex (N8), uses N7 for the vertex count and N9 for transitivity.
- N13: `Set.exists_subset_card_eq` + `fromEdgeSet`; `[Finite W]` ends up unused.
- N14, N15, ROOT: as the blueprint describes.

Where a step had more than one plausible spelling, the proof uses `first | ... | ...` so that a
wrong guess about one lemma's exact form does not sink the node.

## Changed statements
None.

## Not finished
Nothing knowingly left unfinished; see the FINAL output recorded in results/R3_none/calls.tsv.

## Result
First (and only) FINAL call, 2026-11-25T22:37:35Z: `ok` (rc=0, 4 s). Lean reported no errors; the
only output was linter warnings: "this tactic is never executed" / "unused tactic" for every
fallback alternative inside `first | ... | ...` (so each primary alternative succeeded), and one
style note that `haveI` could be `have` in N5. No sorry, admit, axiom, native_decide, unsafe or
maxHeartbeats in the file. Start 22:21:12Z, FINAL 22:37:35Z.
