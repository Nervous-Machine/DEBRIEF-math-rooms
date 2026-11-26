# B5_C12_full_forced — searcher notes

Forced lemma: `core_ge_three_nonstar` (Cambie–Freschi core for `H` with `m ≥ 3` edges, not a star, with a vertex
`x` of blue degree `≥ m`). Cap N = 12. Start 19:41:15 UTC, last attempt 20:14:27 UTC, FINAL after 20:15 UTC
(2026-11-26). 12 genuine attempts, 0 refused calls, every attempt returned `[error]`; the lemma is not closed and
goes back as `sorry`. Every other declaration in the file is proved; all statements (target, forced lemma, earlier
lemmas) are verbatim.

## Attempts (route; what Lean said)

1. Blue-neighbourhood extension: a blue `H - u` inside `N := Cᶜ.neighborSet x` extends by `x`
   (`isContained_of_induce_neighborSet`); else try `N` as a red clique. Lean: helpers ok; residual `N` is not a
   red clique (type mismatch at the hedge), and `omega` cannot get `k ≤ Cᶜ.degree x` from `m ≤ Cᶜ.degree x`.
2. Red-path closure: a red path on `k-1` vertices with both ends red to `x` closes to a red `C_k`
   (`cycleGraph_isContained_of_path`); else try the red neighbourhood of `x` as a blue clique. Lean: helper ok;
   the two-vertex path only gives `k = 3` (`omega` fails on `1 = k - 2`); `#W ≤ C.degree x` unprovable.
3. Induction scaffold: if `Cᶜ.degree x ≥ (k-1)(m-1)+1`, pull the colouring back along `e : Fin ((k-1)(m-1)+1) ↪ N`
   (`exists_embedding_of_le_card`, `isContained_compl_of_comap_neighbor`, `degree_add_compl_degree`). Lean:
   helpers ok; residual = the statement for `H - u` on `C.comap e` (an induction hypothesis the lemma does not
   have); else-branch residual: red neighbourhood of `x` (`≥ k-1` vertices) is not a clique, and `k ≤ C.degree x`
   fails by one.
4. Non-star dichotomy: `exists_disjoint_edges_or_triangle` (two disjoint edges, or `H` is a triangle on `{a,b,c}`).
   Body: blue triangle ⇒ blue `H`; else residuals. Lean: the dichotomy helper compiled; errors only in the hedges
   (`omega` on non-arithmetic goals) of the two residual branches. (Output was truncated by my own `head`; the
   triangle-embedding block was confirmed in attempt 5.)
5. Triangle case closed: no blue triangle ⇒ blue neighbourhoods are red cliques
   (`isClique_compl_neighborFinset_of_no_triangle`) ⇒ blue degrees `< k` ⇒ red degrees `≥ n - k` ⇒ two vertices
   share `≥ n - 2k ≥ k - 2` red neighbours (`le_card_inter_neighborFinset`) ⇒ a red path on `k-1` vertices
   (`exists_isPath_length`) closes to a red `C_k` (`cycleGraph_isContained_of_common_neighbors`). Lean: two
   helper errors (`List.toFinset_card_le` needs its explicit argument); residual = the `2K_2` case.
6. Repair of 5 (explicit argument). Lean: only error = unsolved goal in the `2K_2` case. Triangle case fully
   proved inside the body.
7. Leaf step: `exists_isClique_of_forall_common_neighbor` (every `(k-1)`-set with a common neighbour outside ⇒
   `K_k`), `copyComplOfComap`, and `core_step_leaf`: for a leaf `u` with neighbour `v`, given the statement for
   `H - u` on `(k-1)(m-1)+1` vertices, every `(k-1)`-set `R` is avoided by a blue `H - u`; a vertex of `R` blue
   to the image of `v` extends the copy, otherwise the image of `v` is a common red neighbour of `R`; if that
   happens for every `R`, red `K_k`. Lean: `rcases ... with hred | ⟨g⟩` did not destructure `Nonempty`
   (5 errors on `g`); residuals = the induction hypothesis for `H - u`, and the leafless case.
8. Repair of 7 (`obtain ⟨g⟩`). Lean: `core_step_leaf` compiles; only the two residuals remain.
9. Leaf deletion bookkeeping: `ncard_edgeSet_induce_compl_leaf` (`H - u` has `m - 1` edges),
   `exists_adj_induce_compl_leaf` (no isolated vertex when `v` has another neighbour); for `m = 3` the statement
   for `H - u` comes from `core_star` / `core_two_nonstar`. Lean: both helpers compile; one error
   (`degree_pos_iff_exists_adj` takes explicit arguments); residuals: `m ≥ 4`, `K_2` component, leafless.
10. Repair of 9 and generalisation to every `m`: star `H - u` ⇒ `core_star`; `m = 3` ⇒ `core_two_nonstar`;
    small blue degrees in `C'` ⇒ `cycleGraph_isContained_of_compl_degree_lt`; what is left is exactly this lemma
    for `m - 1`, `H - u`, `C'`. Lean: clean; three residuals (recursive instance; `K_2` component; leafless).
11. Leafless route: handshake `card_le_ncard_edgeSet_of_two_le_degree` and `two_le_degree_of_exists` give
    `#W ≤ m ≤ Cᶜ.degree x`; if `N` is a blue clique, blue `H` (`isContained_of_isClique_card_le`). Lean: clean;
    residual = `N` has a red edge.
12. `K_2`-component route: in the sub-colouring `C'`, all-red ⇒ red `K_{(k-1)(m-1)+1} ⊇ C_k`; else a blue edge
    `pq` is in hand. Lean: clean; residual = blue `H - u` from `pq` and a blue `H - {u, v}` avoiding it.

## Helper lemmas added (all proved, no `sorry`; all stay in the final file)

isContained_of_isClique_card_le, isContained_of_induce_neighborSet, nonempty_of_ncard_edgeSet_ne_zero,
cycleGraph_isContained_of_path, degree_add_compl_degree, exists_embedding_of_le_card,
isContained_compl_of_comap_neighbor, exists_disjoint_edges_or_triangle, exists_isPath_length,
cycleGraph_isContained_of_common_neighbors, isClique_compl_neighborFinset_of_no_triangle,
le_card_inter_neighborFinset, exists_isClique_of_forall_common_neighbor, copyComplOfComap (def),
copyComplOfComap_apply, core_step_leaf, ncard_edgeSet_induce_compl_leaf, exists_adj_induce_compl_leaf,
card_le_ncard_edgeSet_of_two_le_degree, two_le_degree_of_exists.
No helper turned out false; none was removed.

## What is proved of the forced lemma (inside attempt 12's body, all compiling)

- `H` a triangle (`m = 3`, `H = K_3`): closed outright (`R(C_k, K_3) ≤ 3k - 2` in effect).
- `H` with a leaf `u` whose neighbour `v` has degree `≥ 2`: reduced, via `core_step_leaf`, to the statement for
  `H - u`; that statement is supplied when `H - u` is a star (any `m`) or when `m = 3`; for `m ≥ 4` and `H - u`
  not a star it is exactly the forced lemma at `m - 1` (with `cycleGraph_isContained_of_compl_degree_lt` for
  the low-blue-degree colourings). So the leaf case is a true inductive step; the lemma, not being inductive,
  cannot invoke itself.
- Open: (i) `u v` a `K_2` component (needs a two-vertex extension of a blue `H - {u, v}` by a blue edge, plus the
  statement for `H - {u, v}`); (ii) `H` leafless (minimum degree `≥ 2`, `#W ≤ m ≤ Cᶜ.degree x`); I have no
  argument for (ii) beyond "a blue clique on `N` gives `H`".

## Is the lemma true as drawn?

I believe yes: it is the content of Theorem 3 of Cambie–Freschi (the bound is tight for stars and matchings, as
the file's `core_star` and the `K_2`-step show), and nothing I found contradicts it. I did not read the paper.

## What would close it

A strong induction on `m` for all `H` with no isolated vertices (base `m ≤ 2`, stars, and the triangle are in
the file), with the leaf step (`core_step_leaf`, proved), a `K_2`-component step (two-vertex extension, not
written), and a leafless step, which is the real content I could not supply. The forced lemma's statement is
not inductive, so even the leaf step cannot be used to recurse inside it.

## Tempted and did not

- Add an induction hypothesis (or `m = 3`, or "H has a leaf") to the forced lemma's statement: not done.
- Replace `k - 2 ≤ common neighbours` by a weaker reading to make `omega` pass: not done; arithmetic is exact.
- Use `first | ... | sorry` or leave a helper open: not done.

## FINAL

FINAL called 20:15:58 UTC, accepted, returned `[sorry]`: the whole file compiles, the only open declaration is
`core_ge_three_nonstar` (line 879). 13 check calls in all: 12 tagged `core_ge_three_nonstar` (all `[error]`, none refused) and 1 FINAL.
