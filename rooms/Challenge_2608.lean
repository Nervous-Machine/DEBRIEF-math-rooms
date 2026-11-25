/-
Copyright 2026 Nervous Machine. Licensed under the Apache License, Version 2.0.

The statement of Theorem 1.1 of arXiv:2608.18608v2 (Subhasis Panda, "On the Diophantine equation
p^x + (2p+1)^y = z^2 with consecutive exponents", 19 October 2026), written in Lean 4 by the registrar of the
rooms experiment on 2026-11-25 from the paper's statement alone. Nobody else has read this statement against the
paper; that reading is an open gap of the record.

Theorem 1.1. Let p be an odd prime and suppose p^x + (2p+1)^y = z^2 where x, y, z are positive integers with
|x - y| = 1. Then (i) if p ≠ 7 the only solution is (x, y, z) = (2, 1, p+1); (ii) if p = 7 the only solutions are
(2, 1, 8) and (4, 3, 76).

Stated here in the form "every solution is one of the listed ones"; (2, 1, 8) is (2, 1, p+1) at p = 7.
-/
module

public import Mathlib

@[expose] public section

namespace Panda2608

/-- Theorem 1.1 of arXiv:2608.18608v2: the only positive solutions of `p^x + (2p+1)^y = z^2` with `p` an odd
prime and `|x - y| = 1` are `(x, y, z) = (2, 1, p+1)`, and, when `p = 7`, also `(4, 3, 76)`. -/
theorem consecutive_exponents (p x y z : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : x = y + 1 ∨ y = x + 1)
    (h : p ^ x + (2 * p + 1) ^ y = z ^ 2) :
    (x, y, z) = (2, 1, p + 1) ∨ (p = 7 ∧ (x, y, z) = (4, 3, 76)) := by
  sorry

end Panda2608
