# B7_159_none_plain_opus — searcher notes (regime R3_none)

The whole file was written with no checker. FINAL was called once, at the end.

## Nodes
- N01–N12, N14–N19, ROOT: written out with full proofs, no `sorry`. This is unchecked. Which of them
  actually compile is whatever the FINAL output says.
- N13 `core_near_extremal`: left as `sorry`. This is the open core named in the blueprint: near-extremal
  C4-free graphs must have independence number polynomially above sqrt N. I have no proof of it.
- N16, N18 and ROOT are proved *from* N13. Their own proof bodies are complete, but they depend on N13's
  `sorry`, so the root `erdos_159` is NOT proved. Lean will report it as depending on `sorryAx`.

## Changes
- No node statement was changed. The header, the `graphRamsey` definition and the `erdos_159` statement
  are copied verbatim.
- One helper lemma was added: `c4_of_four`, which builds a copy of `cycleGraph 4` from four vertices
  x0–x1–x2–x3–x0 with x0 ≠ x2 and x1 ≠ x3. It is used in N03.

## Not finished
- N13 (open problem). As a result, the root is not proved.
- The fit the blueprint warns about, N09 (R(C4,K_n) ≤ 2n²+1), is proved, but it is not presented as the
  result. It gives no c > 0.

## FINAL results
- First FINAL (the scored one) at 05:41:51Z: **[error]**. There were exactly two errors, both
  `Unknown identifier le_or_lt`: one in N14 (`sparse_branch_arith`) and one in N19 (`floor_succ_le_power`).
  At this Mathlib pin the lemma is named `le_or_gt`. The only other problem Lean reported was the
  `sorry` warning on N13. Every other node elaborated with no error.
- Second FINAL (diagnostic only, not scored) at 05:42:22Z: I made one change, renaming `le_or_lt` to
  `le_or_gt` in both places. Result: **[sorry]**. The only `sorry` is N13. So in that version, N01–N12,
  N14–N19 and ROOT compile, but the root depends on N13's `sorry`.
- A copy of the file as first submitted:
  /private/tmp/claude-501/-Users-heidibennett/5d86e9ef-2972-49cb-ba41-8f96433a6c6d/scratchpad/b7_159opus/Erdos159_first_final.lean
