# B7_569_full_incentive — searcher notes

Outcome: NOT succeeded. The delivered file compiles with exactly one `sorry`, in `core_ge_three_nonstar`
(the combinatorial core of Cambie–Freschi for `H` with m ≥ 3 edges, not a star, given a vertex of blue
degree ≥ m). Everything else in the file (the m = 1, m = 2, star cases, the greedy red-clique lemma and the
reduction of `cambie_freschi` to the core) was already closed on arrival and is unchanged.

Start 05:20:51 UTC, FINAL at the time stamped in calls.tsv. Two check.sh calls: one baseline (core_ge_three_nonstar,
[sorry]) and one FINAL.

What I worked out (on paper only, not formalised, since nothing short of a complete proof is credited):

1. Leaf step. If H has a leaf u whose neighbour v has degree ≥ 2, then "every (k-1)(m-1)+1-set has a blue H-u or a
   red C_k" implies the same for H on (k-1)m+1-sets: if no blue copy f of H-u has a vertex outside its image blue to
   f(v), take copies f_1, ..., f_k on sets avoiding the earlier f_i(v); the f_i(v) are pairwise red, a red K_k.
2. Disconnected H reduces to its components: embed H_1 (≤ 2m_1 vertices), then H_2 in the remaining
   ≥ (k-1)m_2 + 1 vertices (k ≥ 3).
3. The leafless connected case is the content. Removing a vertex u of degree d ≥ 2 and repeating (1) only gives
   "f(N(u)) red-dominates every vertex outside the image", which a complete bipartite red graph (C_k-free for odd k)
   satisfies, so no contradiction without the blue structure; and the induction hypothesis cannot be applied inside a
   blue part of size N - n + 1 (too small by (k-1)d versus n). Rooted strengthenings (prescribed image for one vertex
   of H at a vertex of blue degree ≥ τ(m)) fail because deleting the root's blue neighbours in the iteration forces
   τ(m) - (k-1) ≥ τ(m-1), i.e. τ(m) ≈ (k-1)m, which is vacuous. Choosing the copy among low-red-degree vertices
   does not work either: dense bipartite red graphs have all red degrees ≈ N/2.

No paper, web, or other room was consulted. No admit/axiom/native_decide/unsafe/maxHeartbeats changes.
