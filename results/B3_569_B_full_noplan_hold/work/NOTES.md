# NOTES — arm B3_569_B_full_noplan_hold (full Lean feedback, no blueprint, no paper, hold-position rule)

Target: `Erdos569.cambie_freschi` (Cambie–Freschi 2026, Theorem 3): for `k ≥ 3` and every graph `H` with `m`
edges and no isolated vertices, `graphRamsey (cycleGraph k) H ≤ (k - 1) * m + 1`.

Start 2026-11-26 01:26:55 UTC; first FINAL call 01:54:37 UTC, result `[sorry]` (file compiles, one `sorry`).
17 check.sh calls in all (16 lemma/root checks + FINAL), 7 of them `error`, none refused. No blueprint was given; the route, lemma statements and order below are mine.
The Challenge header, the `graphRamsey` definition and the target statement are verbatim; the root keeps its exact
statement. No web access, no existing proof or paper consulted, no admit/axiom/native_decide/unsafe, no
maxHeartbeats option.

## Route

1. `graphRamsey_le_of_forall` — `sInf` bound: it suffices to show every colouring of `Fin ((k-1)m+1)` has a red
   `C_k` or a blue `H` (`Nat.sInf_le`).
2. `m = 0`: `isEmpty_of_ncard_edgeSet_eq_zero` — no edges and no isolated vertices forces `W` empty, so
   `H ⊑ Cᶜ` by `IsContained.of_isEmpty`.
3. `m ≥ 1`: `core`, a case split, all cases proved except the last:
   - `m = 1` (`core_one`, via `isContained_of_ncard_edgeSet_eq_one`, `cycleGraph_isContained_top`): `H` is a
     single edge; either blue has an edge or red is complete on `k` vertices.
   - `H` a star (some `v₀` lies on every edge) (`core_star`): if a vertex has blue degree `≥ #W - 1` the star
     embeds (`star_isContained_of_le_degree`, built on `isContained_of_extend`); otherwise all blue degrees are
     `≤ #W - 2 ≤ m - 1`, and the greedy lemma `exists_isClique_of_compl_degree_le` gives a red clique on
     `≥ ((k-1)m+1)/m > k-1` vertices, hence a red `C_k` (`cycleGraph_isContained_of_isClique`).
   - `m = 2`, not a star (`core_two_nonstar`): `H` is two disjoint edges (`isContained_of_ncard_edgeSet_eq_two`);
     either blue has two disjoint edges, or all blue edges pairwise meet, and deleting the two ends of one blue
     edge leaves a red clique on `2k - 3 ≥ k` vertices.
   - `m ≥ 3`, not a star, all blue degrees `≤ m - 1`: `cycleGraph_isContained_of_compl_degree_lt` (greedy
     clique again).
   - `m ≥ 3`, not a star, some vertex of blue degree `≥ m`: `core_ge_three_nonstar` — **left open (`sorry`)**.

## Status

Proved (no sorry): `graphRamsey_le_of_forall`, `isEmpty_of_ncard_edgeSet_eq_zero`, `cycleGraph_isContained_top`,
`isContained_of_ncard_edgeSet_eq_one`, `core_one`, `isContained_compl_of_comap`, `isContained_of_extend`,
`cycleGraph_isContained_of_isClique`, `exists_isClique_of_compl_degree_le`, `star_isContained_of_le_degree`,
`core_star`, `cycleGraph_isContained_of_compl_degree_lt`, `isContained_of_ncard_edgeSet_eq_two`,
`core_two_nonstar`, `core`, `cambie_freschi` (the last two depend on the open lemma).

Open (`sorry`): `core_ge_three_nonstar` only. Its statement is exactly the remaining content of the theorem:
`k ≥ 3`, `m ≥ 3`, `H` with `m` edges, no isolated vertices and not a star, a colouring `C` of `Fin ((k-1)m+1)`
with a vertex of blue degree `≥ m`; conclude red `C_k` or blue `H`. I believe it is true (it is a sub-case of the
Cambie–Freschi theorem) and I have no proof of it. Nothing in the file is reshaped: the root statement is the
Challenge's, and the open lemma carries only hypotheses that the proved cases discharge.

The root is therefore proved modulo `core_ge_three_nonstar`; the expected status at FINAL is `sorry`.

Unused but proved: `isContained_compl_of_comap` (restricting a colouring along an injection preserves blue
copies). It is a tool for an induction on the number of vertices that I did not assemble, see below.

## What the proved cases cover

The theorem itself holds for: `m ≤ 2` (all `H`), all stars `K_{1,m}` (all `k ≥ 3`), and all colourings whose blue
graph has maximum degree `≤ m - 1`. In words: the bound is proved whenever a red `k`-clique can be found by the
greedy independent-set argument in the blue graph; `C_k` is only ever found inside a red clique.

## What would be needed to close the root

The open case needs a red `C_k` that is not inside a red clique, or a blue `H` not obtained by a vertex-cover
argument. Every graph `H` with `m ≥ 3` edges other than a star has `H`-free graphs with independence number `< k`
on `(k-1)m+1` vertices (e.g. `H = K_3`: triangle-free graphs with small independence number), so the clique route
cannot be pushed further. An inductive route (remove a vertex `u` of `H`, embed `H - u` in blue on fewer vertices
via `isContained_compl_of_comap`, extend by a vertex via `isContained_of_extend`) has all its generic steps proved
here, but the step that actually uses `C_k`-freeness of red to find the extending vertex is the paper's argument;
I did not invent an intermediate statement for it, since any one I could state and could not prove would risk
being false as drawn. Matchings `H = mK_2` are a further family the clique route would cover (blue with no `m`
disjoint edges has an independent set of size `≥ N - 2(m-1) ≥ k`), but the embedding of an abstract perfect
matching into `m` disjoint blue edges was too much Sym2/subtype bookkeeping for the remaining budget, so it is
not attempted.

## Checks

See `results/B3_569_B_full_noplan_hold/calls.tsv`. Errors were all elaboration slips (deprecated or renamed
lemma names, explicit-vs-implicit arguments, a `dsimp` that made no progress, a `congrArg` elaborated against
the wrong subtype, a missing `DecidableRel` instance in a statement), each fixed on the next call.
