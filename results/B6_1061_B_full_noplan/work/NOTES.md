# NOTES — arm B6_1061_B_full_noplan (full Lean feedback, no blueprint, hold-position rule)

Start 2026-11-27 02:06 UTC. No blueprint in this arm: the route below is the searcher's own. No web access, no paper,
no discussion of the problem was read; the only inputs were the Challenge file, the brief, check.sh and Mathlib source.
Small-case numerics (my own Python, up to a+b ≤ 6000) were used only to judge plausibility of my own statements.

## Route (my own rooms), all in `namespace Erdos1061` before the target

| room | statement (informal) | status |
|---|---|---|
| `sigma_mul_of_coprime` | σ(mn) = σ(m)σ(n) for coprime m, n | proved (Mathlib `isMultiplicative_sigma`) |
| `sigma_two`, `sigma_three` | σ(2) = 3, σ(3) = 4 | proved |
| `solution_one_two` | σ(1)+σ(2) = σ(3) | proved |
| `solution_lift` | a solution (u,v) lifts to (um, vm) when gcd(uv(u+v), m) = 1 | proved |
| `solution_m_two_m` | (m, 2m) is a solution for every m coprime to 6 | proved |
| `coprime_six_succ` | gcd(6, 6k+1) = 1 | proved |
| `family_mem`, `floor_le_S` | k ↦ (6k+1, 2(6k+1)), k < ⌊x/18⌋, injects into the counted set; ⌊x/18⌋ ≤ S x | proved |
| `linear_lower` | x/18 − 1 ≤ S x | proved |
| `floor_le_S_of_solution` | any solution (u,v), u,v ≥ 1, gives ⌊x / (2 uv(u+v)·(u+v))⌋ ≤ S x via its lifts | proved |
| `prim`, `sum_prim_le_S` | Σ_{m ≤ x} #{primitive solutions (u,v) with (u+v)m ≤ x and gcd(uv(u+v), m) = 1} ≤ S x (the lifts of primitive solutions are pairwise distinct) | proved |
| `root_of_eventually_lower` | root ⇐ ∀ R>0 ∀ C, eventually C·x(log x)^R ≤ S x | proved |
| `eventually_lower` | ∀ R>0 ∀ C, eventually C·x(log x)^R ≤ S x | proved from the open room + `sum_prim_le_S` |
| `prim_sum_eventually_lower` | ∀ R>0 ∀ C, eventually C·x(log x)^R ≤ Σ_m #prim x m | **sorry** (open) |
| `li_1061` (root) | ∀ R>0, S x / (x (log x)^R) → ∞ | **sorry inherited** (depends on the open room) |

Root statement, header and the definition of `S` are verbatim from the Challenge file; nothing was changed. No admit,
axiom, native_decide, unsafe or maxHeartbeats option.

## What is open and why

The whole content of Li's theorem is the open room `prim_sum_eventually_lower`: that the number of solutions grows
faster than x (log x)^R for every R. What I could prove without the paper is the linear lower bound (x/18 − 1 ≤ S x,
from the family (m, 2m), m coprime to 6) and the structural reduction to primitive solutions. The reduction loses at
most a constant factor empirically (up to a+b ≤ 6000: 15758 solutions, of which 8268 are legitimate lifts of
primitive solutions, 4698 primitive), and the primitive count P(y) itself appears superlinear (P(y)/y: 0.47, 0.56,
0.68, 0.78 at y = 750, 1500, 3000, 6000), so I believe the open room is true as stated; but it is a *sufficient*
condition for the root, possibly stronger than the root, and I do not know how to prove it. The numerics suggest the
primitive solutions are sporadic (no algebraic family: most have a+b with exactly two prime factors and none of
a, b, a+b forced prime), so any proof would be a counting argument (e.g. n = qr with s(a) = q + r and qr − a prime, a
Goldbach-type count) well beyond what can be formalised here.

## What would be needed to close the root

A proof that the number of primitive solutions (u,v) with u+v ≤ y is ≥ y (log y)^R for every R (or any construction
producing that many solutions directly), formalised; then `sum_prim_le_S` and `root_of_eventually_lower` finish it.
Alternatively a direct construction of a family of solutions of size x (log x)^R would plug into
`root_of_eventually_lower` without passing through `prim`.

## Tool calls

check.sh: 5 calls before FINAL (nodes family_mem ×2, sum_prim_le_S ×2, eventually_lower ×1), 2 returned error
(first drafts), 3 returned sorry (file compiles, one open lemma); then FINAL at 02:16 UTC, which returned [sorry]
(the file compiles; the one `sorry` is `prim_sum_eventually_lower`, line 263, inherited by the root).
