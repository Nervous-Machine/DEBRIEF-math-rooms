Registrar verification, build 11 (outside the registration; not scored).

merged.lean: a three-way merge (git merge-file, no conflicts) of the two forced arms' accepted FINAL files
(B11_1061_F1 attempt 0014, B11_1061_F2 attempt 0020) over their common start file (B6_1061_A final.lean). It compiles
with no errors in the pinned project; the only declarations left with sorry are the two literature rooms and N34.

verify.lean: merged.lean with N34 (lattice_reduction, false as drawn, used by no proof) deleted and the two literature
rooms turned from `theorem … := by sorry` into `axiom …` with the planner's statements unchanged, plus
`#print axioms Erdos1061.li_1061`. It compiles with no errors and no sorry; verify_axioms.txt is Lean's answer:
li_1061 depends on propext, Classical.choice, Quot.sound and the two named axioms
Erdos1061.bienvenu_prop21_uniform and Erdos1061.bienvenu_lemma12_singular_series, and on nothing else.
The root statement and the definition of S are byte-identical to rooms/Challenge_1061.lean.

What this does not say: the two axioms are the planner's statements of the results Li cites (Bienvenu's Proposition
2.1 in the paper's uniform form; the singular-series Lemma 1.2). Whether they say what the cited results say has not
been read by anyone; a statement stronger than the literature would make the deduction vacuous. The root statement is
the registrar's rendering of Li's Theorem 1.1 over formal-conjectures' S, read by nobody else.
