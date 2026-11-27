# Reading guide: Challenge_1061.lean against Li, arXiv:2606.25849v1, Theorem 1.1

**The Lean statement** (`rooms/Challenge_1061.lean`, namespace `Erdos1061`; `S` copied from formal-conjectures 1061.lean):

```lean
noncomputable abbrev S (x : ℝ) : ℝ :=
  ((Finset.Icc 1 ⌊x⌋₊ ×ˢ Finset.Icc 1 ⌊x⌋₊).filter fun (a, b) ↦
      a + b ≤ x ∧ σ 1 a + σ 1 b = σ 1 (a + b)).card

theorem li_1061 : ∀ R : ℝ, 0 < R →
    Tendsto (fun x : ℝ ↦ S x / (x * Real.log x ^ R)) atTop atTop
```

**In words.** S(x) counts ordered pairs (a, b) of positive integers with a + b ≤ x and σ(a) + σ(b) = σ(a + b), where σ is
the sum of divisors. The theorem: for every fixed R > 0, S(x) / (x (log x)^R) tends to infinity as x → ∞.

**What the paper says.** Theorem 1.1 (quoted by a fetch on 2026-11-26): "For every fixed R > 0, lim_{x→∞}
S(x)/(x (log x)^R) = +∞", with S(x) = #{(a,b) ∈ ℕ² : a+b ≤ x, σ(a)+σ(b) = σ(a+b)}, ℕ = {1, 2, …}, and "Ordered pairs are
counted throughout." The reader should check: that `S` counts ordered pairs over positive integers (the `Finset.Icc 1`
bounds and the product), that the real-valued `S x` and the cast behave as the paper's count for real x; that
`Real.log x ^ R` is the real power (log x)^R and that for the limit at `atTop` the region where log x ≤ 0 is irrelevant;
and that `Tendsto … atTop atTop` is the paper's limit equal to +∞.

**The one question.** Does the Lean statement say what Theorem 1.1 says? Answer: agree / disagree (with the
difference) / cannot tell.

Known points of care: formal-conjectures' own `erdos_1061` states the opposite dichotomy (S ∼ c x); Li's theorem
refutes it, and `li_1061` is the registrar's statement of Li's claim, not formal-conjectures'.
