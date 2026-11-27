#!/usr/bin/env python3
"""Discovered rooms (build 9). usage:
  discovered.py REPO_DIR ARM (--blueprint NODES.yaml | --start START.lean) [--atlas atlas/discovered.yaml]
A discovered room is a declaration in an arm's scored final file that is not in its reference structure (the planner's
blueprint, or the start file for arms that began from an earlier arm's file) and not in the Challenge header. For each:
name, kind, statement (whitespace-normalised), own lines, sorry-free at FINAL (from score.json's sorry_in, which reads
Lean's warnings), and the reference rooms it serves: the reference rooms whose bodies mention it, directly or through
other discovered rooms (transitively, in file order). Writes results/ARM/discovered.yaml and, with --atlas, merges into
the atlas keyed by arm. Prints a count and the parents. Standard library plus PyYAML."""
import json, os, re, sys
import yaml

DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|nonrec\s+)*(theorem|lemma|def|abbrev|instance|structure|inductive)\s+([^\s:({\[]+)", re.M)


def strip_comments(s):
    return re.sub(r"--[^\n]*", "", re.sub(r"/-.*?-/", "", s, flags=re.S))


def decls(text):
    heads = [(m.start(), m.group(2), m.group(1)) for m in DECL.finditer(text)]
    out = []
    for i, (pos, name, kind) in enumerate(heads):
        end = heads[i + 1][0] if i + 1 < len(heads) else len(text)
        body = text[pos:end]
        out.append({"name": name.split(".")[-1], "kind": kind, "body": body, "lines": body.rstrip("\n").count("\n") + 1})
    return out


def main():
    a = sys.argv; repo, arm = a[1], a[2]
    d = os.path.join(repo, "results", arm)
    final = open(os.path.join(d, "final.lean"), encoding="utf-8").read()
    if "--blueprint" in a:
        bp = yaml.safe_load(open(os.path.join(repo, a[a.index("--blueprint") + 1])))
        ref = {str(n.get("name", "")).split(".")[-1] for n in bp["nodes"]} | {str(bp.get("root", "")).split(".")[-1]}
        ref_kind = "blueprint:" + a[a.index("--blueprint") + 1]
    else:
        start = open(os.path.join(repo, a[a.index("--start") + 1]), encoding="utf-8").read()
        ref = {x["name"] for x in decls(start)}
        ref_kind = "start:" + a[a.index("--start") + 1]
    score = json.load(open(os.path.join(d, "score.json")))
    sorry_in = {n.split(".")[-1] for n in score.get("fit", {}).get("sorry_in", [])}
    challenge_names = {"graphRamsey", "S"}   # Challenge-header definitions copied verbatim; never discovered
    ds = decls(final)
    names = [x["name"] for x in ds]
    disc = [x for x in ds if x["name"] not in ref and x["name"] not in challenge_names]
    disc_names = {x["name"] for x in disc}
    # direct mentions: which later declarations use each name
    users = {x["name"]: set() for x in ds}
    for i, x in enumerate(ds):
        body = strip_comments(x["body"])
        for y in ds[:i]:
            if y["name"] != x["name"] and re.search(r"(?<![\w.])" + re.escape(y["name"]) + r"(?![\w'])", body):
                users[y["name"]].add(x["name"])
    def parents(n, seen=None):
        seen = seen or set(); out = set()
        for u in users.get(n, ()):
            if u in ref: out.add(u)
            elif u in disc_names and u not in seen:
                seen.add(u); out |= parents(u, seen)
        return out
    # built_for: the node tag of the earliest logged attempt whose file contains the declaration (helpers built for a hinge
    # that stayed open are mentioned by nothing at FINAL, so "serves" alone misses them)
    tag_of = {}
    try:
        calls = [l.rstrip("\n").split("\t") for l in open(os.path.join(d, "calls.tsv"), encoding="utf-8")]
        for f in calls:
            if len(f) < 4: continue
            path = os.path.join(d, "attempts", f[0] + ".lean")
            if not os.path.exists(path): continue
            text = open(path, encoding="utf-8").read()
            for x in disc:
                if x["name"] not in tag_of and re.search(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|nonrec\s+)*(?:theorem|lemma|def|abbrev)\s+(?:\S+\.)?" + re.escape(x["name"]) + r"\b", text, re.M):
                    tag_of[x["name"]] = f[2]
    except FileNotFoundError:
        pass
    id_to_name = {}
    if "--blueprint" in a:
        id_to_name = {str(n.get("id")): str(n.get("name", "")).split(".")[-1] for n in bp["nodes"]}
    fc = os.path.join(d, "forced.conf")
    if os.path.exists(fc):
        conf = dict(l.rstrip("\n").split("=", 1) for l in open(fc) if "=" in l)
        for i_, nm_ in zip((conf.get("nodes") or conf.get("node", "")).split(","), (conf.get("names") or conf.get("name", "")).split(",")):
            id_to_name[i_] = nm_
    rows = []
    for x in disc:
        ps = sorted(parents(x["name"]))
        stmt = re.sub(r"\s+", " ", strip_comments(x["body"]).split(":=")[0]).strip()
        rows.append({"arm": arm, "reference": ref_kind, "name": x["name"], "kind": x["kind"], "statement": stmt[:600], "own_lines": x["lines"],
                     "sorry_free_at_final": x["name"] not in sorry_in, "serves": ps,
                     "built_for": id_to_name.get(tag_of.get(x["name"], ""), tag_of.get(x["name"])),
                     "serves_outcome": {p: ("open" if p in sorry_in else "proved") for p in ps}})
    yaml.safe_dump({"arm": arm, "reference": ref_kind, "discovered": rows}, open(os.path.join(d, "discovered.yaml"), "w"), sort_keys=False, allow_unicode=True, width=110)
    served = {}
    for r in rows:
        for p in r["serves"] or ([r["built_for"] + " (built for)"] if r.get("built_for") else ["(unattached)"]):
            served[p] = served.get(p, 0) + 1
    print(f"{arm}: {len(rows)} discovered rooms ({sum(1 for r in rows if r['sorry_free_at_final'])} sorry-free); serve: {dict(sorted(served.items(), key=lambda kv: -kv[1]))}")
    if "--atlas" in a:
        ap = os.path.join(repo, a[a.index("--atlas") + 1])
        atlas = yaml.safe_load(open(ap)) if os.path.exists(ap) else {"discovered": []}
        atlas["discovered"] = [r for r in atlas.get("discovered", []) if r.get("arm") != arm] + rows
        yaml.safe_dump(atlas, open(ap, "w"), sort_keys=False, allow_unicode=True, width=110)
        print(f"atlas: {len(atlas['discovered'])} discovered rooms in {a[a.index('--atlas') + 1]}")


if __name__ == "__main__":
    main()
