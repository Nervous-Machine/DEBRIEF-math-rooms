# B11_348_A_full_probe: searcher notes

## Result
I proved all 46 rooms and the root `erdos_348` in full. The file compiles as `[ok]`, with no `sorry`, no axiom and no `native_decide`.
Every blueprint statement went in exactly as drawn. None needed a change to elaborate.

## Rooms
- Proved: N01 to N46 and ROOT, in blueprint order inside `namespace Erdos348`.
- Left open: none.
- False as drawn: none. Some hypotheses turned out to be unused, which is slack, not falsity:
  - `hjk` in N26
  - `hunb` and `hT1` in N27
  - `hconst` in N29 (the constant-block hypothesis is not needed, only `b (j-1) < b j`)
  - `hkj` in N37

## Helper lemmas added (searcher's own, all proved)
- `mem_subseqSums'_iff`: Iff.rfl.
- `sum_updateFinset_zero`: before N01.
- `geom_two_sum`: before N10.
- `succ_le_fib_add_two`, `fib_upd_sum`: before N14.
- `range_le_sum`: before N25.
- Before N28:
  - `slack_eventually`: converts the ℤ Tendsto into ℕ form
  - `eventually_ge_of_unbounded`
  - `label_bounds`: labels lie in [1, T)
  - `first_change`: the first index after j where b changes

## Join types
All join types gave way: algebraic_identity, assembly, case_split, extremal_averaging and two_structure_coupling.
- N29 (constant transition, two_structure_coupling) went as the planner described. Apply the recut (N27) to R = {S_j - b_j - e}. If [l, j) is a constant block, Lemma 7 (N26) on the recut state, together with S_j = S_l + (j-l) b_l, forces j - l = 1. That gives every new label = e + b_j - b_l > e.
- N37 (tail gaps, two_structure_coupling): uses `Nat.findGreatest` for the last tail sum below x - T.

## Tactic notes
I used `push Not` in place of `push_neg`, which is deprecated at this Mathlib commit. This is a tactic change only.
