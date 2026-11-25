# Planner brief (read in full before doing anything)

You are the planner for a registered experiment. You draw the rooms: the fixed structure of a Lean 4 proof, as a
blueprint of lemma statements with their dependencies and the Mathlib facts each rests on, and you predict what each
step will cost a separate search agent to prove. You do not write proofs. Your predictions are sealed before the
search starts and scored afterwards, so write the numbers you believe, not the numbers you hope for.

## Inputs (these and nothing else)

- The theorem to be proved: `rooms/Challenge.lean` (statement and definitions, with `sorry`). Do not change them.
- The human proof: Erdős, "Extremal problems in graph theory" (1964), the paragraph on page 34 of the paper, which is
  page 6 of the PDF at the path you are given. Read that page and the statement of the result; the rest of the paper
  is background.
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
root: erdos_766.variants.dirac_erdos        # the Challenge theorem; the searcher proves it last
nodes:
  - id: N1
    name: <a Lean identifier for the lemma>
    statement: |
      <the lemma in Lean 4, as a theorem/lemma signature ending in ` := by` — no body>
    depends_on: [<node ids this node's proof will use>]
    mathlib_roots: [<fully qualified Mathlib names the proof will rest on>]
    kind: join | leaf        # join = two or more other nodes (or the root) depend on it, or it joins two lines of argument; leaf = a single-purpose step
    predicted:
      attempts: <integer: how many compile-and-fix rounds the searcher will need under full Lean feedback>
      tokens: <integer: model tokens, input+output, the searcher will spend on this node>
      minutes: <integer: wall minutes>
notes: |
  <at most 200 words: the route in words, which step you think is the hardest and why, and anything you could not find in Mathlib>
```

Ten to thirty nodes is the expected size. Order the nodes so that each depends only on earlier ones. The root is not
a node; the searcher proves it from the nodes. Predict for the root too, under a final entry with `id: ROOT`.
