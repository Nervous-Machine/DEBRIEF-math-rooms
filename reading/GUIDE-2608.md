# Reading guide: Challenge_2608.lean against arXiv:2608.18608 Theorem 1.1 (gap EG3)

**The Lean statement** (`rooms/Challenge_2608.lean`, namespace `Panda2608`):

```lean
theorem consecutive_exponents (p x y z : ℕ) (hp : p.Prime) (hodd : Odd p) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : x = y + 1 ∨ y = x + 1) (h : p ^ x + (2 * p + 1) ^ y = z ^ 2) :
    (x, y, z) = (2, 1, p + 1) ∨ (p = 7 ∧ (x, y, z) = (4, 3, 76))
```

**In words.** For an odd prime p and positive integers x, y, z with x and y consecutive (either way round), if
p^x + (2p+1)^y is a perfect square z², then either (x, y, z) = (2, 1, p+1), or p = 7 and (x, y, z) = (4, 3, 76).

**What the paper states.** Theorem 1.1 of arXiv:2608.18608 (the registrar's reading, written 2026-11-25): the
Diophantine equation p^x + (2p+1)^y = z² with p an odd prime and |x − y| = 1 has only the solutions listed. The reader
should check the paper's exact hypotheses: does it require p odd (or p ≥ 3, or exclude p = 2 some other way); does it
require x, y ≥ 1 or allow 0; does it state |x − y| = 1 or x − y = ±1 in the same sense as `hxy`; are the listed solutions
exactly the two above, with 7^4 + 15^3 = 2401 + 3375 = 5776 = 76² and p² + (2p+1) = (p+1)²; and is z required positive.

**The one question.** Does the Lean statement say what Theorem 1.1 says, no more and no less? Answer: agree /
disagree (with the difference) / cannot tell.

Known points of care: Lean's `^` on `ℕ`; `Odd p` with `p.Prime` excludes p = 2; the pair-equality `(x, y, z) = …` is
equality of triples.
