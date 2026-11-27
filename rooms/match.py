#!/usr/bin/env python3
"""Statement matcher over the hinge atlas (build 8c). usage:
  match.py ATLAS.yaml --statement "theorem foo (h : ...) : ... := by" [--k 5] [--exclude ARM:ID]
  match.py ATLAS.yaml --self                      # self-consistency: for every hinge, its best match among the others
  match.py ATLAS.yaml --file FILE.lean [--k 5]    # match every declaration in a Lean file against the atlas
A hinge vector is matched on the SHAPE of its statement: the binder hypotheses and the conclusion, tokenised, with
bound variable names (short identifiers that are not Mathlib names) replaced by a placeholder so that `G` and `C` do not
differ. Score = 0.6 · Jaccard(hypothesis tokens) + 0.4 · Jaccard(conclusion tokens), plus 0.1 if the conclusion's head
symbol agrees. The hinge's own `conditionals` field is used when present, otherwise its hypotheses are read from the
statement. This is a syntactic instrument: it finds statements shaped alike, which is the first filter before any
checked subsumption. Standard library plus PyYAML."""
import re, sys, yaml

TOKEN = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*|[≤<≥>=≠∣∀∃→∧∨¬↔∈∉⊆∑∏∫⌊⌋⌈⌉√‖|^*/+\-×ᶜ]")
PLACE = "·"
KEEP = {"ℕ", "ℝ", "ℤ", "ℚ", "ℂ", "Prop", "Type"}


def split_binders(sig):
    """Return (list of binder-group strings, conclusion string) from a signature without the leading name."""
    groups, depth, cur, i = [], 0, "", 0
    opens, closes = "({[⦃", ")}]⦄"
    while i < len(sig):
        ch = sig[i]
        if depth == 0 and ch == ":" and sig[i:i + 2] != ":=":
            return groups, sig[i + 1:].strip()
        if ch in opens:
            depth += 1
        if ch in closes:
            depth -= 1
            if depth == 0:
                groups.append(cur + ch); cur = ""; i += 1; continue
        if depth > 0:
            cur += ch
        i += 1
    return groups, ""


def tokens(s):
    out = []
    for t in TOKEN.findall(s):
        if t in KEEP or "." in t or len(t) > 3 or t[:1].isupper() and len(t) > 1:
            out.append(t)
        elif t.isalpha() or t.startswith("h"):
            out.append(PLACE)
        else:
            out.append(t)
    return out


def hyps_from_groups(groups):
    hs = []
    for g in groups:
        inner = g[1:-1]
        if ":" in inner:
            typ = inner.split(":", 1)[1].strip()
            if any(op in typ for op in ("≤", "<", "≥", ">", "=", "≠", "∣", "∀", "∃", "→", "∧", "∨", "¬", "Prime", "Squarefree", "IsContained", "Adj", "Injective", "Coprime", "Differentiable", "Convex", "IsClosed")):
                hs.append(typ)
    return hs


def shape(statement, conditionals=None):
    sig = re.sub(r"^\s*(theorem|lemma|def|abbrev)\s+\S+\s*", "", statement.strip())
    sig = sig.split(":=")[0]
    groups, concl = split_binders(sig)
    hs = conditionals if conditionals else hyps_from_groups(groups)
    ht = set(tokens(" ".join(hs)))
    ct = set(tokens(concl))
    head = next((t for t in tokens(concl) if t in {"≤", "<", "=", "≠", "∃", "∀", "∣", "IsContained", "Tendsto", "Convex", "IsClosed", "Differentiable"} or (t[:1].isupper() and t != PLACE)), "")
    return ht, ct, head


def jac(a, b):
    return len(a & b) / len(a | b) if (a | b) else 0.0


def score(sa, sb):
    return 0.6 * jac(sa[0], sb[0]) + 0.4 * jac(sa[1], sb[1]) + (0.1 if sa[2] and sa[2] == sb[2] else 0.0)


def load(atlas_path):
    H = yaml.safe_load(open(atlas_path))["hinges"]
    out = []
    for h in H:
        st = h.get("statement") or ""
        if not st:
            continue
        out.append((h, shape(st, h.get("conditionals") or None)))
    return out


def main():
    a = sys.argv
    atlas = load(a[1])
    k = int(a[a.index("--k") + 1]) if "--k" in a else 5
    if "--self" in a:
        same = total = 0
        for h, sh in atlas:
            best = max(((score(sh, sb), hb) for hb, sb in atlas if not (hb["arm"] == h["arm"] and hb["id"] == h["id"])), key=lambda x: x[0], default=None)
            if best is None:
                continue
            total += 1
            same += best[1]["blueprint"] == h["blueprint"]
        print(f"self-consistency: best other match is from the same blueprint for {same}/{total} = {same/total:.2f}")
        return
    queries = []
    if "--statement" in a:
        queries = [("query", a[a.index("--statement") + 1])]
    if "--file" in a:
        text = open(a[a.index("--file") + 1], encoding="utf-8").read()
        DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|nonrec\s+)*(theorem|lemma)\s+([^\s:({\[]+)", re.M)
        heads = [(m.start(), m.group(2)) for m in DECL.finditer(text)]
        for i, (pos, name) in enumerate(heads):
            end = heads[i + 1][0] if i + 1 < len(heads) else len(text)
            queries.append((name, text[pos:end].split(":=")[0]))
    excl = set(a[a.index("--exclude") + 1].split(",")) if "--exclude" in a else set()
    for qname, qst in queries:
        sq = shape(qst)
        ranked = sorted(((score(sq, sb), hb) for hb, sb in atlas if f"{hb['arm']}:{hb['id']}" not in excl and hb.get("blueprint") not in excl), key=lambda x: -x[0])[:k]
        print(f"\n{qname}:")
        for s, hb in ranked:
            print(f"  {s:.2f}  {hb['blueprint']:28s} {hb['id']:5s} {hb['name']:40s} type={hb.get('join_type')} outcome={hb.get('outcome')}")


if __name__ == "__main__":
    main()
