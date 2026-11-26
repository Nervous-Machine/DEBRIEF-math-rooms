#!/usr/bin/env python3
"""Genuineness check for a forced attempt. usage: forced_check.py FILE ALLOWED_FILE
Exit 0 if no declaration outside the ALLOWED list (one short name per line; may be empty or missing) has `sorry`
in its body with comments stripped; otherwise print the offending names, comma-separated, and exit 1.
Used by check.sh in `*forced*` regimes: a call tagged with the forced node is refused unless this passes, and a
FINAL before 12 genuine attempts at the forced node is refused unless this passes. Standard library only."""
import os, re, sys

DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|nonrec\s+)*(theorem|lemma|def|abbrev|instance|structure|inductive|example)\s+([^\s:({\[]+)", re.M)


def strip_comments(s):
    return re.sub(r"--[^\n]*", "", re.sub(r"/-.*?-/", "", s, flags=re.S))


def main():
    path, allowed_path = sys.argv[1], sys.argv[2]
    text = open(path, encoding="utf-8").read()
    allowed = set()
    if os.path.exists(allowed_path):
        allowed = {l.strip() for l in open(allowed_path, encoding="utf-8") if l.strip()}
    heads = [(m.start(), m.group(2)) for m in DECL.finditer(text)]
    bad = []
    for i, (pos, name) in enumerate(heads):
        end = heads[i + 1][0] if i + 1 < len(heads) else len(text)
        body = strip_comments(text[pos:end])
        if re.search(r"\bsorry\b", body) and name.split(".")[-1] not in allowed:
            bad.append(name)
    print(",".join(bad))
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
