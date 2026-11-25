# NOTES — R1_noplan (full Lean feedback, no blueprint), Erdős 766 Dirac–Erdős bound

Start 2026-11-25 22:49:58 UTC, FINAL 2026-11-25 22:57:30 UTC (about 8 minutes of wall clock).

## Result

First FINAL call returned `[ok]`. The file `Rooms766.lean` proves `erdos_766.variants.dirac_erdos`
as stated, with no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe` or `maxHeartbeats` option.

## Route (chosen without a blueprint)

Downward induction on the number of vertices, deleting a minimum-degree vertex at each step.

- For a graph on `n+1 ≥ 4` vertices with `e ≥ ⌊(n+1)²/4⌋ + 1` edges, a vertex `v` of minimum degree
  satisfies `(n+1)·deg v ≤ 2e` (handshake lemma). Pure arithmetic then gives
  `e − deg v ≥ ⌊n²/4⌋ + 1`, so the induced graph on `{v}ᶜ` (which has exactly `e − deg v` edges,
  Mathlib's `card_edgeFinset_induce_compl_singleton` + `card_edgeFinset_deleteIncidenceSet`)
  satisfies the hypothesis for `n`.
- Base `n = k`: transport the graph to `Fin k` along `Fintype.equivFinOfCardEq` (via `comap`, an
  `Iso`), then trim the edge set to exactly `⌊k²/4⌋ + 1` edges with `Finset.exists_subset_card_eq`
  and `fromEdgeSet`.
- The root is `Nat.sInf_le` applied to `m = ⌊n²/4⌋ + 1`.

## Lemmas (all proved)

1. `step_arith` — the arithmetic step, split into `n = 2m` / `n = 2m+1`, closed by `nlinarith`.
2. `ncard_edgeSet_eq_card_edgeFinset` — `ncard` of the edge set vs `#edgeFinset`.
3. `ncard_edgeSet_induce_compl_singleton` — `e(G.induce {v}ᶜ) + deg v = e(G)`.
4. `exists_card_mul_degree_le` — some vertex has `card V · deg v ≤ 2 e(G)`.
5. `exists_le_ncard_edgeSet_eq` — trim a graph to exactly `l ≤ e(H)` edges, below `H`.
6. `exists_copy_of_card_eq` — base case on a type of cardinality `k`.
7. `main_induction` — the induction over `n ≥ k` (`Nat.le_induction`), universally quantified over
   the vertex type `V : Type`.
8. `erdos_766.variants.dirac_erdos` — the target.

## Not finished

Nothing. No lemma was left in a partial state.

## Checks

3 calls to `check.sh`: `step_arith` (ok, two `push_neg` deprecation warnings), `step_arith` again
after replacing `push_neg` with `push Not` (ok, clean), `FINAL` (ok). 0 errors.
