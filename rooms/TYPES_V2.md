# Join types, version 2 (build 8). Seven types, a decision order, and boundary rules for the middle.

Type a room by what its step DOES, read from its statement, its dependencies and its position in the blueprint. Walk the
questions in this order and stop at the first yes.

1. **literature_import** — Is the room a theorem from outside Mathlib that the paper cites rather than proves (a named
   result of other authors, stated as the paper uses it)? Yes → `literature_import`.
2. **two_structure_coupling** — Does the conclusion need two structures used together, where neither alone could give it
   (two colour classes at once; a density condition against an independence bound; an analytic estimate against an
   algebraic or lattice constraint; a geometric volume against an arithmetic count)? Yes → `two_structure_coupling`.
   Test: could the statement be proved by an argument that looks at only one of the structures? If yes, it is not a
   coupling.
3. **quantitative_improvement** — Is the conclusion an inequality whose exponent, constant or threshold is strictly
   better than what the elementary bound in the same setting gives (a power saving, a log removed, a constant beaten)?
   Yes → `quantitative_improvement`.
4. **assembly** — Does the room depend on two or more earlier rooms AND is its conclusion an instantiation, conjunction or
   direct consequence of their conclusions, with no new inequality, enumeration or calculation of its own? Yes →
   `assembly`. Test: would its proof be `obtain … from the dependencies; exact …` plus bookkeeping? A room with fewer
   than two dependencies is never assembly.
5. **case_split** — Is the content of the step a finite enumeration (cases, configurations, residues, coincidences,
   parities, small values), each case closed by a short argument, where the enumeration itself is the work? Yes →
   `case_split`. Test: remove the enumeration and nothing is left to prove.
6. **estimate** — Is the conclusion an inequality (≤, <, ≥, >, big-O, "at least c · X") whose truth depends on the size
   of a parameter (n large, a density, a count, an average, a pigeonhole, a tail, a Markov or Cauchy–Schwarz step,
   a sum compared to an integral)? Yes → `estimate`. Test: the statement has a quantitative hypothesis or threshold
   and the conclusion is a bound.
7. **computation** — Everything else: an equality, an iff, a membership, a divisibility, a definitional unfolding, a
   rewriting, an explicit witness or parametrisation, a determinant, a value of σ, a convexity or closedness of a
   defined set, a property preserved under a rescaling. Including inequalities that hold identically (true for every
   value of the parameters by rewriting, with no size condition). → `computation`.

Boundary rules.
- An inequality that holds for all values by rewriting is `computation`; an inequality that needs a parameter to be
  large or small, or a count to exceed something, is `estimate`.
- A finite enumeration whose cases are each a calculation is `case_split`, not `computation`: the enumeration is the
  content. A single calculation with no branching is `computation` even if long.
- A room that applies its dependencies and adds nothing is `assembly` even if it has a long statement. A room that
  applies its dependencies AND proves a new bound is `estimate`; AND enumerates cases is `case_split`.
- Choosing a witness or a constant (ε, K, a prime, a residue) by an explicit formula is `computation`; choosing it by
  an existence argument that needs a size condition (there is a large enough τ) is `estimate`.
- Positivity or convergence of an infinite product or series is `estimate`.
- The root entry ROOT is typed like any other room, usually `assembly`.
