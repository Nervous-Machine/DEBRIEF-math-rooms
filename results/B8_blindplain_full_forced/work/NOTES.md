# B8_blindplain_full_forced — searcher notes

Start 2026-11-27 17:33:37 UTC (first tool call). Forced rooms: N16, N18, ROOT. N13 (`core_near_extremal`) allowed to stay
open; a proof resting on it counts as closed for the forced rule.

The inherited file had no `first | <proof> | sorry` fallbacks (the two `first` combinators, in N03 and N10, carry no
sorry). The four sorries were N13, N16, N18, ROOT. Lines 1–480 (N01–N15, helpers) are byte-identical to the inherited
file. All 20 statements (19 rooms + root) verbatim against the blueprint / Challenge file; header verbatim.

## N16 `c4_free_indep_power` — CLOSED after 2 genuine attempts (rests on N13)

Route: take delta, eta, and K1 := the core's constant for kappa = 1/2. epsilon := delta, K := min(1/16, 1/10, K1 * 8^(-(1/2+eta))).
Cases on N: N = 0 (t = empty, 0^(1/2+delta) = 0); 1 <= N < 16 (singleton; K <= 1/16 and N^(1/2+delta) <= N <= 16);
N >= 16, sparse (E <= N^(3/2-delta)): N10 then N14 give N^(1/2+delta) <= 10 |t|;
N >= 16, dense (E > N^(3/2-delta)): d := E / N, N11 gives a nonempty core s with internal min degree >= d, N12 gives
d^2 <= 2|s|; from E < N (d+1) and N^(3/2-delta) = N^(1/2-delta) N we get N^(1/2-delta) < d+1, and since N >= 16 forces
N^(1/2-delta) >= 16^(3/8) >= 16^(1/4) = 2, (1/2) N^(1/2-delta) <= d; |s| <= N gives the core hypothesis with kappa = 1/2;
squaring gives N^(1-2 delta) <= 8|s|; N13 then N15 give K1 8^(-(1/2+eta)) N^(1/2+eta/2) <= |t|, and delta <= eta/2 finishes.
Helpers added, all proved: `two_le_rpow_of_sixteen_le`, `dense_degree_bound`, `core_size_bound`.
- attempt 1 (17:40 UTC): [error] — one error, N = 0 case: `rw [Nat.cast_zero]` twice, the second found no `↑0` (subst had
  already produced a bare `0`). Everything else compiled.
- attempt 2 (17:41 UTC): [sorry] for the file (N13, N18, ROOT open); N16 itself compiles with no sorry warning. Closed.

## N18 `card_le_power_of_c4_free` — CLOSED after 1 genuine attempt (rests on N16, hence N13)

Route: from N16 get epsilon, K. c := 4 epsilon/(1+2 epsilon) (0 < c <= 2), C := K^(-(2/(1+2 epsilon))) >= 0. Given an
n-indepsetfree C4-free G on Fin N, N16's independent t has |t| < n (else a subset of card n is an n-independent set);
N17 gives N <= C |t|^(2-c) <= C n^(2-c) by rpow monotonicity (2 - c >= 0).
- attempt 1 (17:41 UTC): [sorry] for the file (N13, ROOT open); N18 compiles with no sorry warning. Closed.

## ROOT `erdos_159` — CLOSED after 1 genuine attempt (rests on N18, hence N13)

Route: from N18 get c, C; answer c, C + 1. For n >= 1 put x := C n^(2-c), N := floor(x) + 1. Any C4-free G on Fin N
cannot be n-indepsetfree (N18 would give N <= x < floor(x) + 1 = N); N08 gives graphRamsey <= N; N19 casts to
(C+1) n^(2-c).
- attempt 1 (17:42 UTC): [sorry] for the file (only N13 open); ROOT compiles with no sorry warning. Closed.

## Beliefs

- N16, N18, ROOT are true as drawn *conditionally on N13*: each is now a Lean proof from N13 and the proved rooms, so the
  whole file reduces the open problem Erdős 159 exactly to the planner's core N13 (near-extremal C4-free graphs have
  independence number polynomially above sqrt). The reductions are elementary and I believe them.
- N13 itself is the open problem; I did not work on it and have no belief to report beyond "unsure", as the planner wrote.

## Tempted and did not

- Nothing in a statement was changed. I was briefly tempted to avoid the small-N case by weakening nothing but choosing a
  cleverer d; the "-1" in floor(E/N) made a case split on N < 16 the honest route, so I added it inside the proof instead.
- I did not try to replace N13 with anything (no extra hypothesis, no regular/algebraic special case).

## FINAL

FINAL called 17:43 UTC, accepted: `[sorry]` — the file compiles; the one `declaration uses sorry` warning is N13
`core_near_extremal` (line 435), the allowed open core. No errors. check.sh calls: N16 x2, N18 x1, ROOT x1, FINAL x1
(5 total); 0 refusals; 1 compile error (N16 attempt 1). End 17:43:24 UTC.
