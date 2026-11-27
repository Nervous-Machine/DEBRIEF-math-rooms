#!/usr/bin/env python3
"""Hinge vectors (build 6). usage: hinges.py REPO_DIR ARM --blueprint NODES_YAML [--predictions PRED_YAML] [--atlas FILE]
For every blueprint room, writes one hinge vector: id, name, kind, join_type, conditionals, consumes, produces,
library_inputs, believed, the planner's prediction (if the sealed file is given), and the outcome from the committed
record: proved (no sorry in its body at the first accepted FINAL, by score.json's rooms_proved), open, or absent;
attempts (non-refused calls tagged with the id or the name); statement sha256 (whitespace-normalised). Writes
results/ARM/hinges.yaml and prints reach by join type (rooms, proved, rate, median attempts). With --atlas, merges the
vectors into that file keyed by arm and id (an atlas across builds). Standard library plus PyYAML."""
import hashlib, json, os, re, statistics, sys
import yaml


def main():
    repo, arm = sys.argv[1], sys.argv[2]
    a = sys.argv
    nodes_path = a[a.index("--blueprint") + 1]
    pred_path = a[a.index("--predictions") + 1] if "--predictions" in a else None
    atlas_path = a[a.index("--atlas") + 1] if "--atlas" in a else None
    d = os.path.join(repo, "results", arm)
    score = json.load(open(os.path.join(d, "score.json")))
    proved = {n.split(".")[-1] for n in score.get("rooms_proved", [])}
    sorry_in = {n.split(".")[-1] for n in score.get("fit", {}).get("sorry_in", [])}
    attempts = {}
    for line in open(os.path.join(d, "calls.tsv"), encoding="utf-8"):
        f = line.rstrip("\n").split("\t")
        if len(f) >= 4 and f[3] != "refused":
            attempts[f[2]] = attempts.get(f[2], 0) + 1
    bp = yaml.safe_load(open(os.path.join(repo, nodes_path), encoding="utf-8"))
    preds = {}
    if pred_path:
        for p in yaml.safe_load(open(os.path.join(repo, pred_path), encoding="utf-8")).get("nodes", []):
            preds[p.get("id")] = p.get("predicted", p)
    vectors = []
    for n in bp.get("nodes", []):
        nid = str(n.get("id"))
        name = str(n.get("name", score.get("root", ""))).split(".")[-1]
        outcome = "proved" if name in proved else ("open" if name in sorry_in else "absent")
        stmt = re.sub(r"\s+", " ", str(n.get("statement", ""))).strip()
        v = {"arm": arm, "id": nid, "name": name, "kind": n.get("kind"), "join_type": n.get("join_type"),
             "conditionals": n.get("conditionals", []), "consumes": n.get("consumes"), "produces": n.get("produces"),
             "library_inputs": n.get("library_inputs", []), "believed": n.get("believed"),
             "predicted": preds.get(nid), "outcome": outcome,
             "attempts": attempts.get(nid, 0) + attempts.get(name, 0),
             "statement_sha256": hashlib.sha256(stmt.encode()).hexdigest()[:16]}
        vectors.append(v)
    yaml.safe_dump({"arm": arm, "blueprint": nodes_path, "hinges": vectors}, open(os.path.join(d, "hinges.yaml"), "w"), sort_keys=False, allow_unicode=True, width=110)
    by_type = {}
    for v in vectors:
        if v["id"] == "ROOT":
            continue
        t = v["join_type"] or "untyped"
        by_type.setdefault(t, []).append(v)
    print(f"{'join_type':26s} rooms proved rate   median_attempts")
    for t, vs in sorted(by_type.items()):
        pr = sum(1 for v in vs if v["outcome"] == "proved")
        med = statistics.median([v["attempts"] for v in vs]) if vs else 0
        print(f"{t:26s} {len(vs):5d} {pr:6d} {pr/len(vs):5.2f}   {med}")
    if atlas_path:
        ap = os.path.join(repo, atlas_path)
        atlas = yaml.safe_load(open(ap)) if os.path.exists(ap) else {"hinges": []}
        keep = [h for h in atlas.get("hinges", []) if h.get("arm") != arm]
        atlas["hinges"] = keep + vectors
        yaml.safe_dump(atlas, open(ap, "w"), sort_keys=False, allow_unicode=True, width=110)
        print(f"atlas: {len(atlas['hinges'])} hinge vectors in {atlas_path}")


if __name__ == "__main__":
    main()
