#!/usr/bin/env python3
"""Make a blueprint-shaped nodes file from a start file's declarations (build 7), so score.py can count changed
statements against the start file in arms that have no planner blueprint. usage: start_nodes.py START.lean OUT.yaml
Each theorem/lemma/def becomes a node with id = name = its short name and statement = its signature up to `:=`."""
import re, sys, yaml
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|nonrec\s+)*(theorem|lemma|def|abbrev)\s+([^\s:({\[]+)", re.M)
text = open(sys.argv[1], encoding="utf-8").read()
heads = [(m.start(), m.group(2), m.group(1)) for m in DECL.finditer(text)]
nodes = []
for i, (pos, name, kind) in enumerate(heads):
    end = heads[i + 1][0] if i + 1 < len(heads) else len(text)
    body = text[pos:end]
    j = body.find(":=")
    sig = body[: j if j >= 0 else len(body)].rstrip() + " := by"
    nodes.append({"id": name.split(".")[-1], "name": name.split(".")[-1], "statement": sig, "depends_on": [], "kind": "leaf", "join_type": None})
yaml.safe_dump({"root": None, "nodes": nodes, "notes": f"declarations of {sys.argv[1]} as nodes, for statement-change detection"}, open(sys.argv[2], "w"), sort_keys=False, allow_unicode=True, width=120)
print(len(nodes), "nodes")
