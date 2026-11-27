#!/usr/bin/env python3
"""usage: decl_sorry.py FILE NAME -> exit 0 if the declaration NAME (short name) exists and its body has no `sorry`
(comments stripped); exit 1 if it has sorry or is missing. Used by check.sh for multi-room forced regimes (build 8)."""
import re, sys
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|nonrec\s+)*(theorem|lemma|def|abbrev|instance|structure|inductive|example)\s+([^\s:({\[]+)", re.M)
text = open(sys.argv[1], encoding="utf-8").read(); name = sys.argv[2]
heads = [(m.start(), m.group(2)) for m in DECL.finditer(text)]
for i, (pos, n) in enumerate(heads):
    if n.split(".")[-1] == name:
        end = heads[i + 1][0] if i + 1 < len(heads) else len(text)
        body = re.sub(r"--[^\n]*", "", re.sub(r"/-.*?-/", "", text[pos:end], flags=re.S))
        sys.exit(1 if re.search(r"\bsorry\b", body) else 0)
sys.exit(1)
