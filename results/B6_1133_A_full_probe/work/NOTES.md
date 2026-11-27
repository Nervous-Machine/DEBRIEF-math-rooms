# Searcher notes, arm B6_1133_A_full_probe (full Lean feedback, planner blueprint, hold-position + probe-first)

Start 2026-11-27 02:16 UTC (first tool call). File: Erdos1133.lean (one file, nodes inside `namespace Erdos1133`
in blueprint order N01..N34, then the target). Header, definitions and target statement copied verbatim from
rooms/Challenge_1133.lean (diffed against it before FINAL).

## Status at FINAL

File compiles; the only `sorry`s are the three `literature_import` rooms. Every other room, and the root, has a
complete proof. `erdos_1133` is therefore proved conditionally on N01 and N03 (N02 is not used by the development,
because its only consumer N03 is left as an import).

### Proved (31 rooms + root)
N04 N05 N06 N07 N08 N09 N10 N11 N12 N13 N14 N15 N16 N17 N18 N19 N20 N21 N22 N23 N24 N25 N26 N27 N28 N29 N30 N31
N32 N33 N34 ROOT.

### Left as sorry (literature imports, no attempt by instruction)
- N01 `olevskii_ulanovskii_prop_4_2` (Olevskii–Ulanovskii Prop. 4.2). Used by N10.
- N02 `bernstein_vertical_growth` (Phragmén–Lindelöf vertical growth). Not consumed by any proved room.
- N03 `bernstein_real_sample_set_isClosed` (Montel / normal families). Used by N17.

### Believed false as drawn
None. Every non-import statement elaborated and was proved exactly as drawn (whitespace aside: the YAML line folding
of the blueprint was unfolded to single spaces; no token of any statement was changed).

### Statement changes
None. One helper lemma was added before N25: `bucket_grouping_aux` (the per-colour block splitting, by induction on
the colour Finset), from which N25 follows with S = univ, B = univ.

### Unused hypotheses the planner drew
- N17 `signs_prescribed_tolerance`: `hC : 0 < C` and `hρ0 : 0 ≤ ρ` are not needed (only ρ < 1 is used).
- N14, N03 take `σ`, `H` generally; fine.

## Join types
All join types gave way:
- algebraic_identity (N04 N05 N07 N08 N13 N14 N19 N21 N22 N26 N30 N31): all closed; N08 (rpow/log bookkeeping)
  and N05 were the longest.
- quantitative_improvement (N09): closed, τ = ⌈exp(3(2H+b0)/a)⌉₊, A0 = 2 + 3b0/a + 6/a.
- case_split (N11 N24 N33): closed; N24 by strong induction on |S| with `Fin.cons`.
- extremal_averaging (N16 N25 N28): closed; N25 via the helper above and `finSumFinEquiv` to concatenate families.
- two_structure_coupling (N17 N20): closed. N17 (the planner's predicted first failure) went through as drawn:
  v ∉ K because a real-valued interpolant of norm C/(1-ρ) would contradict hobs; separate; symmetrize f (N13),
  scale by 1/(1-ρ) into K; then N16.
- assembly (N10 N12 N15 N18 N23 N27 N29 N32 N34 ROOT): closed. N29 was the most bookkeeping (Fin k enumeration of
  each group via `Fintype.equivFinOfCardEq`, y defined through `Exists.choose` on the group containing i, uniqueness
  from disjointness).

## What would close the root unconditionally
Proofs of N01 and N03 (N02 would then be needed for N03). Neither is in Mathlib: N01 is the quantitative lower bound
for the Bernstein-space interpolation constant; N03 needs a Montel/normal-family argument with preservation of type,
real-valuedness and samples under locally uniform limits. Not attempted, per the brief.

## Checks
check.sh calls before FINAL: 8 (tags N04, N08, N09, N25, N29, N10, ROOT, ROOT); 4 returned error, 4 returned sorry,
0 refused. Every check compiled in about 5 s. Scratch: scratchpad/b6_1133a (statements extracted from the YAML by a
small parser, proofs per node assembled into the one file).

## FINAL
First accepted FINAL call at 2026-11-27 02:44 UTC returned [sorry] (compiles; sorry only in N01, N02, N03). 9 check.sh calls in total, 0 refused.
End 02:44 UTC; about 28 minutes of the 180-minute budget used.
