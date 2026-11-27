#!/usr/bin/env python3
"""Statement matcher v2.1 (build 10 amendment A1: the conjunction split stops at a nested quantifier, as the arrow
split already did; written after the registered run found the defect; not scored against build 10's predictions).
Statement matcher v2 over the hinge atlas (EG8). usage:
  match2.py ATLAS.yaml --statement "theorem foo ... := by" [--k 5] [--exclude BLUEPRINT,...]
  match2.py ATLAS.yaml --file FILE.lean [--k 5] [--exclude ...]   # every theorem/lemma in a Lean file
  match2.py ATLAS.yaml --self                                     # best other match from the same target?
  match2.py ATLAS.yaml --tau                                      # the registered threshold rule, computed
  match2.py ATLAS.yaml --sides                                    # how many atlas statements have an empty hypothesis side

Two changes from rooms/match.py (build 8c), which is left as registered:

1. Hypotheses read from inside the conclusion. After the top-level colon, leading quantifiers are peeled: for ∀ (and
   ∀ᶠ), propositional binder groups become hypotheses and the body is read on; for ∃, the binders are the statement's
   constants, the conjuncts before the last become conclusion constraints, and the last conjunct is read on; a
   top-level arrow chain A → B → C puts A and B on the hypothesis side. Bracket depth is respected throughout.
   Binder groups count as hypotheses when their type is a proposition; a function type (an arrow alone) does not.
   The planner's `conditionals` field is not used: every vector and every query is read from its statement alone.

2. A semantic feature. The constants a statement uses (dotted names and their last component, capitalised
   identifiers, lower-case identifiers of four or more letters that are not names it binds, and the operators ∑ ∏ ∫ ⌊
   ⌈ √ ‖ ∣) are compared by IDF-weighted Jaccard, the weights computed over the atlas: a constant that every proof uses
   (ℕ, Finset) weighs little; one that only one proof uses (sigma, Bernstein) weighs much.

score2 = 0.5 * shape2 + 0.5 * sem, where shape2 is match.py's formula (0.6 hypotheses + 0.4 conclusion + 0.1 head)
on the new sides. Threshold tau: for every atlas vector, its best score against vectors of the OTHER targets; tau is the
95th percentile (nearest rank) of those values. Targets: 569 (blueprint_569_nodes.yaml and start_569B_nodes.yaml, one
proof), 159, 1061, 1133. Standard library plus PyYAML."""
import math, os, re, sys, yaml

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import match as M  # noqa: E402

OPENS, CLOSES = "({[⦃⟨", ")}]⦄⟩"
STOP = {"theorem", "lemma", "fun", "Type", "Prop", "Sort", "by", "then", "else", "with", "match", "show", "from",
        "have", "let", "Type*", "this"}
OPS = {"∑", "∏", "∫", "⌊", "⌈", "√", "‖", "∣"}
TARGET = {"blueprint_569_nodes.yaml": "569", "start_569B_nodes.yaml": "569", "blueprint_159_nodes.yaml": "159",
          "start_159H_nodes.yaml": "159", "blueprint_1061_nodes.yaml": "1061", "blueprint_1133_nodes.yaml": "1133"}
PROPOP = ("≤", "<", "≥", ">", "=", "≠", "∣", "∀", "∃", "∧", "∨", "¬", "↔", "∈", "∉", "⊆")  # an arrow alone is a function type


def top_split(s, sep):
    """Split s at top-level occurrences of sep (a string), respecting brackets."""
    parts, depth, cur, i = [], 0, "", 0
    while i < len(s):
        ch = s[i]
        if ch in OPENS:
            depth += 1
        elif ch in CLOSES:
            depth -= 1
        if depth == 0 and s.startswith(sep, i):
            parts.append(cur); cur = ""; i += len(sep); continue
        cur += ch; i += 1
    parts.append(cur)
    return [p.strip() for p in parts]


def binder_groups(prefix):
    """Bracketed groups and bare names in a quantifier prefix such as ' x y (hx : 0 < x) [Fintype V]'."""
    groups, names, depth, cur, bare = [], set(), 0, "", ""
    for ch in prefix:
        if ch in OPENS:
            if depth == 0:
                names |= set(re.findall(r"[A-Za-z_][A-Za-z0-9_']*", bare.split(":")[0])); bare = ""
            depth += 1
        if depth > 0:
            cur += ch
        else:
            bare += ch
        if ch in CLOSES:
            depth -= 1
            if depth == 0:
                groups.append(cur); cur = ""
    names |= set(re.findall(r"[A-Za-z_][A-Za-z0-9_']*", bare.split(":")[0]))
    for g in groups:
        inner = g[1:-1]
        if ":" in inner:
            names |= set(re.findall(r"[A-Za-z_][A-Za-z0-9_']*", inner.split(":", 1)[0]))
    return groups, names


def prop_type(g):
    inner = g[1:-1]
    if ":" not in inner:
        return None
    typ = inner.split(":", 1)[1].strip()
    return typ if any(op in typ for op in PROPOP) or re.search(r"\b(Prime|Squarefree|IsContained|Adj|Injective|Coprime|Differentiable|Convex|IsClosed|Odd|Even|Connected|IsAcyclic|Colorable|IndepSetFree|Nonempty)\b", typ) else None


def peel(concl):
    """Return (hypothesis strings, conclusion strings, names bound in the conclusion)."""
    hyps, cons, names, c = [], [], set(), concl.strip()
    for _ in range(50):
        m = re.match(r"^(∀ᶠ|∀|∃!|∃)", c)
        if m:
            q = m.group(1); body = c[len(q):]
            parts = top_split(body, ",")
            if len(parts) < 2:
                break
            prefix, rest = parts[0], ",".join(parts[1:]).strip()
            if q == "∀ᶠ":
                prefix = prefix.split(" in ")[0]
            groups, ns = binder_groups(prefix); names |= ns
            props = [t for t in (prop_type(g) for g in groups) if t]
            bare = prefix
            for g in groups:
                bare = bare.replace(g, " ")
            if any(op in bare for op in ("<", ">", "≤", "≥", "∈", "∉", "⊆", "≠")):
                props.append(prefix.strip())          # bounded quantifier: ∀ C > 0, ∃ ε > 0, ∀ x ∈ S
            if q.startswith("∀"):
                hyps += props
                c = rest
            else:
                cons += props
                conj = top_split(rest, "∧")
                j = 0
                while j < len(conj) - 1 and not re.match(r"^(∀|∃)", conj[j]):
                    j += 1
                cons += conj[:j]
                c = " ∧ ".join(conj[j:])
            continue
        arrows = top_split(c, "→")
        if len(arrows) > 1:
            j = 0
            while j < len(arrows) - 1 and not re.match(r"^(∀|∃)", arrows[j]):
                j += 1
            if j > 0:                                  # a nested ∀/∃ scopes to the end: stop splitting there
                hyps += arrows[:j]; c = " → ".join(arrows[j:]); continue
        conj = top_split(c, "∧")
        if len(conj) > 1:
            j = 0
            while j < len(conj) - 1 and not re.match(r"^(∀|∃)", conj[j]):
                j += 1
            if 0 < j < len(conj) - 1 or (j == len(conj) - 1 and re.match(r"^(∀|∃)", conj[j])):
                cons += conj[:j]; c = " ∧ ".join(conj[j:]); continue
        if c.startswith("(") and c.endswith(")") and len(top_split(c[1:-1], "→")) > 1:
            c = c[1:-1].strip(); continue
        break
    cons.append(c)
    return hyps, cons, names


def sides(statement):
    sig = re.sub(r"^\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|private\s+|protected\s+)*(theorem|lemma|def|abbrev)\s+\S+\s*", "", statement.strip())
    sig = sig.split(":=")[0]
    groups, concl = M.split_binders(sig)
    bh = [t for t in (prop_type(g) for g in groups) if t]
    _, outer_names = binder_groups(" ".join(groups))
    ph, pc, inner_names = peel(concl)
    return bh + ph, pc, outer_names | inner_names


def shape2(statement):
    hs, cs, _ = sides(statement)
    ht = set(M.tokens(" ".join(hs)))
    ctoks = M.tokens(" ".join(cs))
    ct = set(ctoks)
    head = next((t for t in M.tokens(cs[-1]) if t in {"≤", "<", "=", "≠", "∃", "∀", "∣", "IsContained", "Tendsto", "Convex", "IsClosed", "Differentiable"} or (t[:1].isupper() and t != M.PLACE)), "")
    return ht, ct, head


def constants(statement):
    sig = re.sub(r"^\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|private\s+|protected\s+)*(theorem|lemma|def|abbrev)\s+\S+\s*", "", statement.strip()).split(":=")[0]
    _, _, names = sides(statement)
    out = set()
    for t in re.findall(r"[A-Za-z_][A-Za-z0-9_'.]*|[∑∏∫⌊⌈√‖∣]", sig):
        if t in OPS:
            out.add(t); continue
        t = t.strip(".")
        if not t or t in STOP:
            continue
        if "." in t:
            parts = [p for p in t.split(".") if p]
            if parts and parts[0] in names:      # G.Adj, H.edgeSet: field access on a bound name
                out |= {p for p in parts[1:] if len(p) > 1}
            else:
                out.add(t); out |= {p for p in parts if len(p) > 1 and p not in names}
            continue
        if t in names:
            continue
        if (t[:1].isupper() and len(t) > 1) or (len(t) >= 4 and t.isidentifier()):
            out.add(t)
    return out


class Atlas:
    def __init__(self, path):
        H = yaml.safe_load(open(path))["hinges"]
        self.vecs = []
        for h in H:
            st = h.get("statement") or ""
            if st:
                self.vecs.append((h, shape2(st), constants(st)))
        n = len(self.vecs); df = {}
        for _, _, cs in self.vecs:
            for c in cs:
                df[c] = df.get(c, 0) + 1
        self.idf = lambda c: math.log((n + 1) / (df.get(c, 0) + 1)) + 1.0

    def sem(self, a, b):
        u = a | b
        if not u:
            return 0.0
        return sum(self.idf(c) for c in a & b) / sum(self.idf(c) for c in u)

    def score(self, sa, ca, sb, cb):
        return 0.5 * M.score(sa, sb) + 0.5 * self.sem(ca, cb)

    def tau(self):
        best = []
        for h, s, c in self.vecs:
            t = TARGET.get(h["blueprint"])
            vals = [self.score(s, c, s2, c2) for h2, s2, c2 in self.vecs if TARGET.get(h2["blueprint"]) != t]
            if vals:
                best.append(max(vals))
        best.sort()
        k = max(0, math.ceil(0.95 * len(best)) - 1)
        return best[k], len(best)


def main():
    a = sys.argv
    A = Atlas(a[1])
    k = int(a[a.index("--k") + 1]) if "--k" in a else 5
    if "--tau" in a:
        t, n = A.tau()
        print(f"tau = {t:.3f} (95th percentile of {n} best cross-target scores)")
        return
    if "--sides" in a:
        e1 = sum(1 for h, _, _ in A.vecs if not M.shape(h["statement"])[0])
        e2 = sum(1 for _, s, _ in A.vecs if not s[0])
        print(f"empty hypothesis side: v1 {e1}/{len(A.vecs)}, v2 {e2}/{len(A.vecs)}")
        for h, s, _ in A.vecs:
            if not s[0]:
                print(f"  v2 empty: {h['blueprint']}:{h['name']}")
        return
    if "--self" in a:
        same = total = 0
        for h, s, c in A.vecs:
            cands = [(A.score(s, c, s2, c2), h2) for h2, s2, c2 in A.vecs if not (h2["blueprint"] == h["blueprint"] and h2["id"] == h["id"])]
            if not cands:
                continue
            best = max(cands, key=lambda x: x[0])
            total += 1
            same += TARGET.get(best[1]["blueprint"]) == TARGET.get(h["blueprint"])
        print(f"self-consistency: best other match is from the same target for {same}/{total} = {same/total:.2f}")
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
        sq, cq = shape2(qst), constants(qst)
        ranked = sorted(((A.score(sq, cq, s2, c2), h2) for h2, s2, c2 in A.vecs if h2.get("blueprint") not in excl), key=lambda x: -x[0])[:k]
        print(f"\n{qname}:")
        for s, h2 in ranked:
            print(f"  {s:.3f}  {h2['blueprint']:28s} {str(h2['id']):5s} {h2['name']:40s} outcome={h2.get('outcome')}")


if __name__ == "__main__":
    main()
