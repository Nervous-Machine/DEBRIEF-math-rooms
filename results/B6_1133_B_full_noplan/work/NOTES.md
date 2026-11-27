# NOTES — arm B6_1133_B_full_noplan (full Lean feedback, no blueprint, hold-position rule)

Start 2026-11-27 02:06:17 UTC. FINAL called at about 02:23 UTC. Root statement and file header copied verbatim from
rooms/Challenge_1133.lean and never changed (checked by diff before FINAL). No admit / axiom / native_decide / unsafe /
maxHeartbeats. No web, no literature, no other arm's files read.

## The route I drew (no planner rooms in this arm)

All lemmas live in `namespace Erdos1133` before the target.

| room | status | content |
|---|---|---|
| `Statement C` | def | the conclusion of the problem for one fixed `C` |
| `statement_mono` | proved | the conclusion is monotone in `C` (not needed for the root, kept as a sanity room) |
| `statement_of_lt_one` | proved | `C < 1` is trivial: take `y ≡ 1`, `ε = 1/2`; any `P` agreeing at one node has `|P(x_i)| = 1 > C` |
| `interpImage x m C` | def | value vectors at the nodes of polynomials of degree `≤ m` with `|P| ≤ C` on `[-1,1]` |
| `agree`, `NotCovered C` | def | Hamming-covering form: some `y` in the cube agrees in `< (1-ε)n` coordinates with every vector of `interpImage x m C`, `m < (1+ε)n` |
| `statement_of_notCovered` | proved | `NotCovered C → Statement C` (if `|P| ≤ C` everywhere then its value vector lies in `interpImage`) |
| `cube n`, `coverSet`, `MeasureSmall C` | def | covered part of `[-1,1]^n` has strictly smaller Lebesgue measure than the cube |
| `notCovered_of_measureSmall` | proved | measure pigeonhole |
| `coverSetOn x ε C S`, `bigSets n ε` | def | covered on a fixed agreement set `S`; the sets of size `≥ (1-ε)n` |
| `coverSet_inter_cube_subset` | proved | a covered `y` is covered on its own agreement set, which is big |
| `volume_coverSet_le` | proved | union bound over `S ∈ bigSets` |
| `volume_cube` | proved | `vol [-1,1]^n = 2^n` |
| `exists_volume_coverSetOn_le` | **sorry** | the analytic room, see below |
| `card_bigSets_le` | proved | `#bigSets ≤ ((1+ε) ε^{-ε})^n` by weighting subsets with `ε^{n-|S|}` (total `(1+ε)^n`) |
| `tendsto_base` | proved | `(1+ε) ε^{-ε} → 1` as `ε → 0⁺` (via continuity of `negMulLog`) |
| `exists_card_bigSets_mul_lt` | proved | the combinatorial room: for every `ρ < 1` some `ε ≤ ε₁` has `#bigSets(n,ε) ρ^n < 1` for all `n ≥ 1` |
| `measureSmall_of_one_le` | proved from the two rooms | glue: union bound × per-`S` bound × count `< 2^n` |
| `erdos_1133` | compiles, depends on the one sorry | case split `C < 1` / `C ≥ 1` |

Root: **not proved** — it rests on the single open room `exists_volume_coverSetOn_le`.

## The open room, and why it is open

`exists_volume_coverSetOn_le (hC : 1 ≤ C)`: there are `ρ < 1` and `ε₁ > 0` such that for every `0 < ε ≤ ε₁`, for all
large `n`, all nodes `x` and all `S ⊆ Fin n` with `|S| ≥ (1-ε)n`, the set of `y ∈ [-1,1]^n` whose restriction to `S`
is matched by some polynomial of degree `< (1+ε)n` bounded by `C` on `[-1,1]` has volume `≤ ρ^n 2^n`.

This is, in my reading, the whole content of the problem: that for arbitrary nodes the data interpolable by
sup-norm-bounded polynomials fill an exponentially small fraction of the cube, uniformly in the small extra freedom
(degree up to `(1+ε)n`, `εn` free coordinates). Heuristic for why it should hold: for well-spread nodes the
interpolant of random data overshoots at each of ~`n` gaps with probability bounded below, roughly independently;
for clustered nodes the Lebesgue function is larger still. I have no proof of it and no Mathlib material close to
it (nothing on Lebesgue constants or on the Chebyshev extremal property is available to grep). I did not reshape
it; I believe the statement as drawn is true but it is unproved here.

Note on uniformity: the room is stated with `ρ` uniform over all small `ε` because the combinatorial room must then
choose `ε` depending on `ρ`. If the true analytic statement only gives `ρ = ρ(ε) → ρ₀ < 1`, the glue would need a
small adjustment (choose `ε` first against `ρ₀`); the shape of the route would not change.

## What I would need to close the root

A proof of the analytic room, i.e. an exponential-volume (or entropy) bound for `{y|_S : ∃ P, deg P ≤ m, ‖P‖_∞ ≤ C,
P(x_i) = y_i on S}` inside `[-1,1]^S`, uniform over node configurations, with `m ≤ (1+ε)n`, `|S| ≥ (1-ε)n`. This is
the Erdős problem itself in measure form.

## Tool use

check.sh calls: 5 before FINAL (nodes `statement_of_lt_one` [error: `agree` needed `noncomputable`, `lt_or_le`
renamed, `push_neg` deprecated], `erdos_1133` [sorry], `measureSmall_of_one_le` [sorry],
`exists_card_bigSets_mul_lt` [error: `ring` cannot distribute a symbolic power], `exists_card_bigSets_mul_lt`
[sorry]), then FINAL. Scratch copies under the session scratchpad `b6_1133b/`.

## FINAL

First FINAL call (02:23:07 UTC) returned `[sorry]`: the file compiles with exactly one `sorry`, in
`exists_volume_coverSetOn_le`. Total check.sh calls: 6 (2 error, 3 sorry, FINAL sorry). Wall clock used: ~17 min of 180.
