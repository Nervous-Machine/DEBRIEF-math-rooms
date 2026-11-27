# Reader brief, blind re-typing (read in full before doing anything)

You are a reader for a registered experiment. You are given a blueprint of rooms (lemma statements with names,
dependencies and Mathlib roots) with their join types removed, and a type system with a decision order and boundary
rules. Assign exactly one type to every room, including the ROOT entry, by walking the decision order. You are one of
two readers typing the same rooms independently; agreement between you is what is measured, so apply the written rules,
not your taste, and when a rule decides, follow it even if you would have chosen otherwise.

## Inputs (these and nothing else)
- `rooms/TYPES_V2.md`: the type system. Read it twice.
- The untyped blueprint file you are given.

## Rules
- No web access. Do not read any other file in the repository: not the typed blueprints, not the atlas, not any
  results, not any other reader's output. Do not attempt to infer which rooms were proved; the outcome is not an input.
- Do not change any statement.

## Output
Write the file you are told to write, YAML, with this shape:

```yaml
blueprint: <the blueprint file name you were given>
types:
  N01: <type>
  N02: <type>
  ...
  ROOT: <type>
notes: |
  <at most 150 words: the rooms you found hardest to type and which rule decided them>
```

Types are exactly one of: literature_import, two_structure_coupling, quantitative_improvement, assembly, case_split,
estimate, computation.
