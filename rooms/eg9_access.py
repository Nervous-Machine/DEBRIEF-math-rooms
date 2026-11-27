#!/usr/bin/env python3
"""EG9 scorer (build 11). usage:
  eg9_access.py REPO_DIR --proof NAME BLUEPRINT PROBE_ARM FORCED_ARM[,FORCED_ARM...] [--proof ...] [--exclude ID,...] [--theta 0.578] [--out FILE]

For each proof: the planner rooms of BLUEPRINT fall into three classes, read mechanically from the arms' files.
  P  closed in the probe arm (outcome proved in results/PROBE_ARM/hinges.yaml)
  F  open after the probe arm, forced, and closed in a forced arm (forced.json forced_rooms: closed_at_first_final)
  U  open after the probe arm, forced, given at least 12 genuine attempts, and still open
  X  forced but open with fewer than 12 genuine attempts (budget ran out): excluded and counted
literature_import rooms and the rooms named in --exclude are not classed.
access(h) is build 9b's measure under the corrected v2.1 reader (rooms/match2_1.py): the best single node's
min(sim to h's hypothesis side, sim to h's conclusion side), sim = 0.5 shape + 0.5 IDF-weighted constants, IDF over
every node of the graph (atlas/hinges.yaml and atlas/discovered.yaml as they stand). Prints per-room rows and, per proof,
median and extremes of access by class and the registered comparisons. Standard library plus PyYAML."""
import json, math, os, statistics, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import match as M  # noqa: E402
import match2_1 as M2  # noqa: E402
import atlas_graph as A  # noqa: E402
import atlas_graph2_1 as G  # noqa: E402  (side_constants)
import yaml  # noqa: E402


def main():
    a = sys.argv; repo = a[1]
    theta = float(a[a.index("--theta") + 1]) if "--theta" in a else 0.578
    out = a[a.index("--out") + 1] if "--out" in a else None
    excl = set(a[a.index("--exclude") + 1].split(",")) if "--exclude" in a else set()
    proofs = []
    i = 0
    while i < len(a):
        if a[i] == "--proof":
            proofs.append((a[i + 1], a[i + 2], a[i + 3], a[i + 4].split(","))); i += 5
        else:
            i += 1
    nodes, _ = A.load_nodes(repo)
    ks = [k for k in nodes if nodes[k]["statement"]]
    sh = {k: M2.shape2(nodes[k]["statement"]) for k in ks}
    cs = {k: M2.constants(nodes[k]["statement"]) for k in ks}
    sides = {}
    for k in ks:
        hs, cc, names = M2.sides(nodes[k]["statement"])
        sides[k] = (G.side_constants(hs, names), G.side_constants(cc, names))
    n = len(ks); df = {}
    for k in ks:
        for c in cs[k]:
            df[c] = df.get(c, 0) + 1
    idf = lambda c: math.log((n + 1) / (df.get(c, 0) + 1)) + 1.0

    def sem(x, y):
        u = x | y
        return sum(idf(c) for c in x & y) / sum(idf(c) for c in u) if u else 0.0

    def access(hk):
        ht, ct, head = sh[hk]
        Hs, Cs = (ht, set(), ""), (set(), ct, head)
        hc, cc = sides[hk]
        best = 0.0
        for k in ks:
            if k == hk:
                continue
            s_h = 0.5 * M.score(sh[k], Hs) + 0.5 * sem(cs[k], hc)
            s_c = 0.5 * M.score(sh[k], Cs) + 0.5 * sem(cs[k], cc)
            best = max(best, min(s_h, s_c))
        return round(best, 3)

    report = {"theta_unused_for_access": theta, "proofs": []}
    for name, bp, probe, forced in proofs:
        bpd = yaml.safe_load(open(os.path.join(repo, bp)))
        rooms = {str(r["id"]): r for r in bpd["nodes"]}
        hv = yaml.safe_load(open(os.path.join(repo, "results", probe, "hinges.yaml")))
        hv = hv["hinges"] if isinstance(hv, dict) else hv
        probe_out = {str(h["id"]): h["outcome"] for h in hv}
        fr = {}
        for arm in forced:
            fj = json.load(open(os.path.join(repo, "results", arm, "forced.json")))
            for r in fj["summary"].get("forced_rooms") or []:
                fr[str(r["node"])] = (arm, r["genuine_attempts"], r["closed_at_first_final"])
        rows = []
        for rid, r in rooms.items():
            if r.get("join_type") == "literature_import" or rid in excl:
                continue
            key = f"{bp}:{r['name']}"
            if probe_out.get(rid) == "proved":
                cls = "P"
            elif rid in fr:
                arm, g, closed = fr[rid]
                cls = "F" if closed else ("U" if g >= 12 else "X")
            else:
                cls = "-"
            acc = access(key) if key in sh else None
            rows.append({"id": rid, "name": r["name"], "class": cls, "access": acc, "hypothesis_side": bool(sh.get(key, (set(),))[0])})
        by = {c: [x["access"] for x in rows if x["class"] == c and x["access"] is not None] for c in "PFUX-"}
        med = {c: (statistics.median(v) if v else None) for c, v in by.items()}
        res = {"proof": name, "counts": {c: len(v) for c, v in by.items()}, "median": med,
               "max_F": max(by["F"]) if by["F"] else None, "min_U": min(by["U"]) if by["U"] else None,
               "informative": bool(by["U"] and by["F"])}
        res["P1_median_U_gt_median_F"] = (med["U"] > med["F"]) if res["informative"] else None
        res["P2_min_U_gt_max_F"] = (res["min_U"] > res["max_F"]) if res["informative"] else None
        res["P3_median_U_gt_median_P"] = (med["U"] > med["P"]) if (by["U"] and by["P"]) else None
        res["rows"] = rows
        report["proofs"].append(res)
        print(f"\n== {name} ({bp}); counts {res['counts']}; informative {res['informative']}")
        for x in sorted(rows, key=lambda x: (x["class"], -(x["access"] or 0))):
            print(f"  {x['class']}  {x['access'] if x['access'] is not None else '-':<6}  {'H' if x['hypothesis_side'] else '-'}  {x['id']:5s} {x['name']}")
        print(f"  median P {med['P']}  F {med['F']}  U {med['U']}  |  max F {res['max_F']}  min U {res['min_U']}")
        print(f"  P1 {res['P1_median_U_gt_median_F']}  P2 {res['P2_min_U_gt_max_F']}  P3 {res['P3_median_U_gt_median_P']}")
    if out:
        json.dump(report, open(os.path.join(repo, out), "w"), indent=1)


if __name__ == "__main__":
    main()
