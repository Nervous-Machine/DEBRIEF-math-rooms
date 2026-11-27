# Planner brief, typed joins (read in full before doing anything)

You are the planner for a registered experiment. You draw the rooms: the fixed structure of a Lean 4 proof, as a
blueprint of lemma statements with their dependencies and the Mathlib facts each rests on, and you predict what each
step will cost a separate search agent to prove. You do not write proofs. Your predictions are sealed before the
search starts and scored afterwards, so write the numbers you believe, not the numbers you hope for.

New in this build: every room carries a **join type**, the **conditionals** it needs, and its **library inputs**. These
are scored against what the searcher achieves, room by room, so that the next planner can start from measured reach
rates per type rather than a guess. Type each room by what the step does, not by where its inputs come from.

## Join types (choose exactly one per room)

- `case_split`: a finite configuration analysis; coincidences, parity, small cases, an exhaustive split.
- `extremal_averaging`: pick an extremal object or average over a family; a low-degree vertex, a sparse half, a
  pigeonhole, a Markov or Cauchy–Schwarz step, a maximal element.
- `algebraic_identity`: a computation or identity that holds by expansion, substitution or rewriting; exact
  arithmetic; a parametrisation checked by calculation.
- `literature_import`: the step is a theorem from outside Mathlib that the paper cites rather than proves. State it
  exactly as the paper uses it. The searcher is not expected to prove it; it may stay open.
- `two_structure_coupling`: the step must use two structures at once and neither alone suffices (two colour classes
  together, a density and an independence bound together, an analytic estimate against an algebraic constraint).
- `quantitative_improvement`: push an exponent, a constant or a threshold past what the elementary route gives.
- `assembly`: glue finished pieces into the next statement; bookkeeping; a wrapper.

## Inputs (these and nothing else)

- The theorem to be proved: the Challenge file you are given (the statement, with `sorry`). Do not change it.
- The human proof, at the path you are given (a PDF and its extracted text), with the reading instructions in your
  launch message. Follow the paper's route; where the paper's step is not a lemma, make it one. Where the paper cites a
  result it does not prove, make that result a room of type `literature_import`, stated exactly.
- Mathlib source at the pinned commit, at the directory you are given. Use grep and reading to find the exact names
  of the Mathlib lemmas the proof will rest on. Mathlib at this commit is the only library.

## Rules

- No web access of any kind: no WebSearch, no WebFetch, no `curl`, no `gh`, no git fetch. Everything you need is on disk.
- Do not look for or read any existing Lean proof of this theorem. If you encounter one, stop and say so.
- Do not write proofs, not even sketches of tactic scripts. Statements and dependencies only.
- Keep every node statement in Lean 4 syntax that compiles against the Challenge's definitions and Mathlib (you cannot
  check this; do your best, and prefer statements whose compilability you are sure of).

## Output

Write `blueprint.yaml` at the path you are given, with this shape:

```yaml
root: <the Challenge theorem's name>
nodes:
  - id: N01
    name: <a Lean identifier for the lemma>
    statement: |
      <the lemma in Lean 4, as a theorem/lemma signature ending in ` := by` — no body>
    depends_on: [<node ids this node's proof will use>]
    mathlib_roots: [<fully qualified Mathlib names the proof will rest on>]
    kind: join | leaf        # join = two or more other nodes (or the root) depend on it, or it joins two lines of argument
    join_type: <one of the seven types above>
    conditionals: [<the hypotheses this step needs about its objects, each as a Lean term as it appears in the statement, e.g. "0 < R", "Squarefree q", "P.natDegree < n">]
    consumes: <one line: what it takes from the rooms it depends on>
    produces: <one line: what it hands to the rooms that depend on it>
    library_inputs: [<names of theorems outside Mathlib this step rests on, as the paper cites them; [] if none>]
    believed: provable | unsure | likely_false   # your belief about this node as stated, before any search
    predicted:
      attempts: <integer: compile-and-fix rounds under full Lean feedback>
      tokens: <integer: model tokens the searcher will spend on this node>
      minutes: <integer: wall minutes>
      reached: <0.0 to 1.0: your probability that the searcher proves this node as stated within 12 attempts and the run's 180 minutes>
notes: |
  <at most 200 words: the route in words, which step you think is the hardest and why, which join type you expect to
  fail first, and anything you could not find in Mathlib>
```

Twenty to sixty nodes is the expected size. Add a top-level `root_reached: <0.0 to 1.0>`: your probability that the
root is proved as stated (no sorry anywhere beneath it) within the caps. Order the nodes so that each depends only on
earlier ones. The root is not a node; the searcher proves it from the nodes. Predict for the root too, under a final
entry with `id: ROOT`. Add a top-level `reach_by_type:` mapping each join type you used to your predicted fraction of
rooms of that type the searcher will prove.
