# NOTES — arm B4_159_F_full_forced, forced room N13 `core_near_extremal`

Start 2026-11-26 18:10:08 UTC. Twelve genuine N13 attempts (every check call had no `sorry` anywhere in the file), all returned `[error]`; none compiled. The room is left as its verbatim blueprint statement with `sorry`. No statement of any room or of the target was changed. Helpers added before N13 (all fully proved, all compiled): `nbhd_half_indep`, `empty_case_N13`, `exists_indep_sqrt`, `exists_indep_moore`, `two_nbhd_union`.

## What the room says, in plain terms

For a C4-free graph induced on `s` with minimum internal degree at least `κ|s|^(1/2-δ)`, find an independent set of size at least `K|s|^(1/2+η)`, with `η ≥ 4δ > 0`. Via N14/N15/N16 this room implies Erdős 159; conversely Erdős 159 with exponent ε gives the room with `δ = ε/4`. So the room is equivalent to the open problem. Every route I know gives exponent exactly `1/2` (or `1/2-δ` when it goes through a neighbourhood); the Moore bound N12 (`d² ≤ 2|s|`) shows that any independent set found inside neighbourhoods is capped at `√(2|s|)`, so no neighbourhood-based route can ever reach `1/2+η`.

## The twelve attempts (route — what Lean said)

1. Single neighbourhood of any `v ∈ s` induces a matching (N04+N05), `δ=1/8, η=1/2, K=κ/2` — one error: exponent step `1/2+1/2 ≤ 1/2-1/8` reduced to `False`. Helpers compiled.
2. Dichotomy on the maximum internal degree Δ (`Finset.exists_max_image`): large Δ → neighbourhood; small Δ → greedy N05 with `D=Δ`, `K=1/4` — two errors, both in the small-Δ branch: `|s|² ≤ 4|s|` and the step needing it. Large-Δ branch compiled.
3. New helper `exists_indep_sqrt` (|s| ≤ (2|t|+1)|t|, proved), then lift `√|s|` to `|s|^(1/2+η)` — one error: `1/2+1/2 ≤ 1/2`. Helper compiled.
4. Same route with honest witnesses `δ=1/100, η=1/25` (attempts 1–3 had used `δ=1/8, η=1/2`, an instance I believe is false: polarity graphs have min degree ~|s|^(1/2) but independence number only ~|s|^(3/4), so `η > 1/4` cannot hold), `K=1/2` — one error: `|s|^(1/25) ≤ 1` refuted by `Real.one_lt_rpow` for `|s| > 1`.
5. New helper `exists_indep_moore` (strong induction deleting a minimum-degree vertex and its neighbourhood, capped by N12; proved), `M=⌊√(2|s|)⌋`, `K=1/4` — two errors: the wall `1/25 ≤ 0`, and my own constant slip (the chain gives `|s|^(1/2) ≤ 4|t|`, so `K` had to be `1/16`). Helper compiled.
6. New helper `two_nbhd_union` (for distinct `u,v ∈ s` the pruned union of their neighbourhoods has internal max degree ≤ 2, so `deg u + deg v ≤ 3|t|+3`), `K=κ/8`, singleton `s` ruled out by the hypothesis — two errors: a type mismatch in the helper (`Nat.add_le_add ?_ ?_` against the literal `2`) and the wall `1/2+1/25 ≤ 1/2-1/100`.
7. Helper repaired (two `≤ 1` facts closed by `omega`), same route — one error: the wall only. Helper compiled.
8. Moore-deletion route with `K=1/16` repaired — one error, the open goal is exactly `s.card ≤ 1125899906842624` (= 4^25): this route proves the room for all `|s| ≤ 4^25` and fails beyond.
9. Single neighbourhood with honest witnesses, `K=κ/2` — one error: `1 < |s|` gives `False` (exponent comparison through `Real.rpow_lt_rpow_of_exponent_lt`).
10. Contrapositive: assume every independent subset is below `X/2`, contradict `exists_indep_sqrt` — one error: needs `X² ≤ |s|`, i.e. `(1/2+1/25)·2 ≤ 1`, false.
11. Larger of the `√|s|` set and the two-vertex set, `K=min(κ/8,1/4)` — two errors, the two walls `X ≤ |s|^(1/2)` and `X ≤ |s|^(1/2-δ)`.
12. Extreme admissible witnesses `δ=1/16, η=1/4` through the Moore-deletion route, `K=1/16` — two errors, both my tactic slip: `rw [h4]` with `h4 : 4 = 256^(1/4)` also rewrote the `4` inside the exponent `1/4`, so `Real.rpow_le_rpow` could not unify; the intended wall `|s| ≤ 256` never appeared. With the cap reached I could not rerun it.

## Do I believe the room is true as drawn?

Unknown to me, and I believe unknown to everyone: it is equivalent to Erdős 159. If Erdős 159 is true the room is true with `δ = ε/4`; if the room is true then Erdős 159 is. Within the room's own parameter range, witnesses with `η > 1/4` (hence `δ > 1/16` forced by `4δ ≤ η`) are, I believe, false instances because of polarity graphs (recollection, not verified here); so any true witnesses have `δ ≤ 1/16`. My attempts 4–11 used `δ = 1/100, η = 1/25`.

## What I would need to close it

A polynomial (not logarithmic) improvement over `√|s|` for the independence number of dense C4-free graphs. Nothing in the file or in the elementary toolbox (neighbourhood matchings, greedy/Caro–Wei, Moore bound, two-vertex unions, min-degree deletion) gets past exponent `1/2`; a Shearer-type argument would give only a `log` factor. That improvement is the open problem.

## What I was tempted to change and did not

- Quantify `K` or `η` after `s` (or let `K` depend on `|s|`): would make attempt 8's bound (`|s| ≤ 4^25`) into a proof. Not done; it changes the statement.
- Choose `η = 0` (or `δ = 0`): the `√|s|` routes close the room then; forbidden by `0 < δ` and `4δ ≤ η`.
- Add a maximum-degree hypothesis to N13 or restrict to regular graphs: a fit.
- Read `rooms/forced_check.py`, `forced.conf`, `calls.tsv` or `attempts/`: not read.
