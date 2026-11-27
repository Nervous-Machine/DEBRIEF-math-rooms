#!/usr/bin/env python3
"""Probe-first rule (build 6). usage: probe_check.py FILE NODES_YAML CALLS_TSV
Exit 0 if every blueprint room whose declaration body still carries `sorry` (comments stripped) has received at least one
non-refused check call tagged with its node id or its name, except rooms of join_type literature_import, which may stay
open untried. Otherwise print the offending room names, comma-separated, and exit 1. A room that is not declared in the
file at all counts as open and untried. Used by check.sh at FINAL in `*probe*` regimes. Standard library plus PyYAML."""
import re, sys
import yaml

DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|nonrec\s+)*(theorem|lemma|def|abbrev|instance|structure|inductive|example)\s+([^\s:({\[]+)", re.M)


def strip_comments(s):
    return re.sub(r"--[^\n]*", "", re.sub(r"/-.*?-/", "", s, flags=re.S))


def main():
    path, nodes_path, calls_path = sys.argv[1:4]
    text = open(path, encoding="utf-8").read()
    heads = [(m.start(), m.group(2)) for m in DECL.finditer(text)]
    sorry_decls, present = set(), set()
    for i, (pos, name) in enumerate(heads):
        end = heads[i + 1][0] if i + 1 < len(heads) else len(text)
        short = name.split(".")[-1]
        present.add(short)
        if re.search(r"\bsorry\b", strip_comments(text[pos:end])):
            sorry_decls.add(short)
    attempts = {}
    try:
        for line in open(calls_path, encoding="utf-8"):
            f = line.rstrip("\n").split("\t")
            if len(f) >= 4 and f[3] != "refused":
                attempts[f[2]] = attempts.get(f[2], 0) + 1
    except FileNotFoundError:
        pass
    bp = yaml.safe_load(open(nodes_path, encoding="utf-8"))
    bad = []
    for n in bp.get("nodes", []):
        if n.get("id") == "ROOT":
            continue
        name = str(n.get("name", "")).split(".")[-1]
        if n.get("join_type") == "literature_import":
            continue
        is_open = name in sorry_decls or name not in present
        tried = attempts.get(str(n.get("id")), 0) + attempts.get(name, 0)
        if is_open and tried == 0:
            bad.append(name)
    print(",".join(bad))
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
