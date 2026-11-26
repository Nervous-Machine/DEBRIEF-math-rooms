# Planner brief, rooms from the question (read in full before doing anything)

You are the planner for a registered experiment. In this build there is no paper and no proof. You are given a
statement and Mathlib, and you draw the rooms from the question: the lemmas that would have to hold for the statement
to follow, the Mathlib facts that bear on each, and where the joins would be. You do not know whether the statement is
true or provable, and you say so where you do not. Your predictions are sealed before the search starts and scored
afterwards, so write the numbers you believe.

## Inputs (these and nothing else)

- The statement: the Challenge file you are given (with `sorry`). Do not change it.
- Mathlib source at the pinned commit, at the directory you are given. Use grep and reading to find the exact names
  of the Mathlib lemmas that bear on the statement. Mathlib at this commit is the only library.

## Rules

- No web access of any kind: no WebSearch, no WebFetch, no `curl`, no `gh`, no git fetch. Everything is on disk.
- Do not look for or read any existing proof, paper or discussion of this statement. If you encounter one, stop and say so.
- Do not write proofs, not even sketches of tactic scripts. Statements, dependencies, Mathlib roots, predictions.
- Keep every node statement in Lean 4 syntax that compiles against the Challenge and Mathlib.

## Output

Write `blueprint.yaml` at the path you are given, with the shape of the earlier builds (`root`, `nodes` with `id`,
`name`, `statement`, `depends_on`, `mathlib_roots`, `kind`, `predicted`), plus two new fields on every node and on the
`ROOT` entry:

```yaml
    believed: provable | unsure | likely_false   # your belief about this node, before any search
    predicted:
      attempts: <integer>      # compile-and-fix rounds under full Lean feedback, if provable
      tokens: <integer>
      minutes: <integer>
      reached: <0.0 to 1.0>    # your probability that the searcher proves this node as stated within its caps
```

and a top-level `root_reached: <0.0 to 1.0>`: your probability that the root is proved as stated within the caps.
Ten to forty nodes. Order the nodes so that each depends only on earlier ones. In `notes` (at most 250 words) say
which rooms are the ones you cannot see into, and what a fit would look like here: the weakening of the statement
that a searcher under pressure would be tempted to prove instead.
