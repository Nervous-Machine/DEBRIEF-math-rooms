# B8_159none_plain_forced — searcher notes

Start 2026-11-27 17:28:19 UTC. Forced rooms: N16 `c4_free_indep_power`, N18 `card_le_power_of_c4_free`, ROOT `erdos_159`.
N13 `core_near_extremal` left as `sorry` (the open core), as the brief allows.

## What happened with the tool

The regime name `B8_159none_plain_forced` contains `none`, and `check.sh` refuses every non-FINAL call for a `*none*`
regime ("no checker in this regime until FINAL"). So the brief's "full Lean feedback" was not available: the single call
tagged N16 (call 1) was refused before compilation, and by the script's logic every call tagged N16, N18, ROOT or any
other node would be refused the same way. The forced rule of twelve genuine attempts per room therefore cannot be met in
this regime; the only way to an accepted FINAL is to close all three forced rooms (no `sorry` in them) and compile blind
once. That is what I did. No Lean was run any other way.

## Route (one attempt each, written blind, compiled only at FINAL)

- N16 from N13 + N10/N11/N12/N14/N15 exactly as the planner drew it. Take (δ, η, K) from N13 with κ = 1/2; ε := δ,
  K' := min(1/10, K·8^(−(1/2+η))). N = 0: empty set. N ≥ 1, split on E = |edges| vs N^(3/2−δ):
  sparse (E ≤ N^(3/2−δ)): N10 gives an independent t with N² ≤ 2(4E+N)|t|, N14 gives N^(1/2+δ) ≤ 10|t|.
  dense: d := ⌊N^(1/2−δ)⌋₊ ≥ 1, d ≤ N^(1/2−δ) ≤ 2d (floor of a real ≥ 1), so d·N ≤ N^(3/2−δ) < E and N11 gives a core
  s with internal min degree ≥ d; N12 gives d² ≤ 2|s| so N^(1−2δ) ≤ 4d² ≤ 8|s|; |s|^(1/2−δ) ≤ N^(1/2−δ) ≤ 2d gives the
  N13 hypothesis with κ = 1/2; N13 gives t ⊆ s independent with K|s|^(1/2+η) ≤ |t|; N15 gives
  K·8^(−(1/2+η))·N^(1/2+η/2) ≤ K|s|^(1/2+η); finally N^(1/2+δ) ≤ N^(1/2+η/2) since δ ≤ η/4.
- N18 from N16 + N17: c := 4ε/(1+2ε) ∈ (0, 2], C := K^(−2/(1+2ε)); IndepSetFree n forces |t| < n, so
  N ≤ C|t|^(2−c) ≤ C n^(2−c).
- ROOT from N08 + N18 + N19: N := ⌊C n^(2−c)⌋₊ + 1; any C4-free G on Fin N with no independent n-set would give
  N ≤ C n^(2−c) < N; so R(C4, K_n) ≤ N ≤ (C+1) n^(2−c).

## Belief

N16, N18 and ROOT are true conditional on N13 as drawn; the proofs above are only reductions to N13. Whether N13 is true
I cannot say: it is the open problem (independence number of near-extremal C4-free graphs polynomially above √N).

## Tempted and did not

Nothing in any statement was changed. I did not try to prove N13 or weaken it. I did not run Lean outside check.sh even
though every check call before FINAL was refused.

## Calls
1. 17:33:49Z  N16  refused ("no checker in this regime until FINAL")
2. 17:41:35Z  FINAL  accepted, compiled: [sorry] — the only `declaration uses sorry` is N13 (line 435); N16, N18 and ROOT
   compile with no sorry (closed, resting on N13). Every `first | a | b` fallback I had added went unused (Lean's
   unreachable-tactic linter confirms the primary branch succeeded in each case). Wall clock for the compile: 6 s.

## Per forced room
- N16 `c4_free_indep_power`: closed, 1 attempt (written blind, compiled at FINAL), rests on N13.
- N18 `card_le_power_of_c4_free`: closed, 1 attempt, rests on N16.
- ROOT `erdos_159`: closed, 1 attempt, rests on N18. The result is a reduction of the open problem to N13, not a proof.

End 2026-11-27 17:42 UTC. check.sh calls: 2 (1 refused, 1 FINAL accepted). Lean errors: 0.
