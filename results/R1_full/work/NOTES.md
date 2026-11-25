# NOTES — regime R1_full, Erdős 766 (Dirac–Erdős bound)

Start 2026-11-25 21:51:51 UTC. File: `Rooms766.lean` (this directory).

## Status
All 15 blueprint nodes and the root are proved; the file compiled `[ok]` (no errors, no warnings) on
check call 2 (node N11) and is declared FINAL on call 3. No `sorry`, `admit`, `axiom`, `native_decide`,
`unsafe`, or `maxHeartbeats` anywhere. Definitions and the root statement are verbatim from `Challenge.lean`.

## Nodes
- N1–N15, ROOT: proved, statements unchanged from `blueprint_nodes.yaml`.
- Helper added (not in the blueprint): `low_degree_arith_aux (N e d q p h)` — N3's arithmetic with the
  three floor terms `N^2/4`, `(N-1)^2/4`, `N/2` abstracted as variables `q p h`; closed by `nlinarith`
  after multiplying the negated goal by `N` and `he` by `N-2` (written `N = M + 2`). N3 is then a one-line
  application of the helper to N1 and N2.
- N1, N2: parity split (`Nat.even_or_odd'`), a `ring` identity for the square, then `omega` (floors) and
  `nlinarith` (N1's final inequality).
- N11: needed `classical` because `G.overFin hc` is a `def`, so the `comap` decidability instance does
  not fire and `Fintype (G.overFin hc).edgeSet` could not be synthesized (the only error in the first check).
- N12: plain `induction N` (not `Nat.le_induction`); the `k ≤ N` hypothesis is carried in the statement,
  so the zero case is `omega` and the successor case splits on `k < n+1` vs `k = n+1`.
- N13: `Set.exists_subset_card_eq`, then `fromEdgeSet t`; `edgeSet_fromEdgeSet` plus `sdiff_eq_left`
  with disjointness from `edgeSet_subset_compl_diagSet`.

## Check calls
1. N1 — error at N11 only (instance), N1–N10 fine.
2. N11 — [ok] for the whole file.
3. FINAL.
