#!/usr/bin/env python3
"""The atlas as a graph, v2 reader (EG8). usage: atlas_graph2.py REPO_DIR --theta T [--out FILE]
Same nodes, dependency edges, access and shores as rooms/atlas_graph.py (build 9b, left as registered), with the
statement read by rooms/match2.py: hypotheses peeled out of quantified conclusions, and similarity
  sim(a, b) = 0.5 * shape score (match.py formula on the v2 sides) + 0.5 * IDF-weighted Jaccard of constants,
IDF over all nodes of the graph. For a hinge h, its hypothesis side carries the constants of its hypothesis text and its
conclusion side those of its conclusion text. Neighbourhood edges at sim >= theta (registered: theta = tau of
match2.py). Standard library plus PyYAML."""
import json, math, os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import match as M  # noqa: E402
import match2 as M2  # noqa: E402
import atlas_graph as A  # noqa: E402

HINGES = A.__dict__.get("DEFAULT_HINGES") or [
    "start_569B_nodes.yaml:core_ge_three_nonstar", "blueprint_569_nodes.yaml:lemma7", "blueprint_569_nodes.yaml:goddard_kleitman_sidorenko",
    "blueprint_159_nodes.yaml:core_near_extremal", "blueprint_159_nodes.yaml:turan_weak", "blueprint_159_nodes.yaml:c4_free_indep_power",
    "blueprint_159_nodes.yaml:floor_succ_le_power", "blueprint_159_nodes.yaml:card_le_power_of_c4_free", "blueprint_159_nodes.yaml:erdos_159",
    "blueprint_1061_nodes.yaml:lattice_coords", "blueprint_1061_nodes.yaml:local_denominator", "blueprint_1061_nodes.yaml:plane_prime_count",
    "blueprint_1061_nodes.yaml:lattice_reduction", "blueprint_1133_nodes.yaml:signs_prescribed_tolerance", "blueprint_1133_nodes.yaml:finite_degree_error_tradeoff"]


def side_constants(texts, names):
    out = set()
    for t in re.findall(r"[A-Za-z_][A-Za-z0-9_'.]*|[∑∏∫⌊⌈√‖∣]", " ".join(texts)):
        t = t.strip(".")
        if not t or t in M2.STOP or t in names:
            continue
        if t in M2.OPS:
            out.add(t); continue
        if "." in t:
            parts = [p for p in t.split(".") if p]
            if parts and parts[0] in names:
                out |= {p for p in parts[1:] if len(p) > 1}
            else:
                out.add(t); out |= {p for p in parts if len(p) > 1 and p not in names}
            continue
        if (t[:1].isupper() and len(t) > 1) or (len(t) >= 4 and t.isidentifier()):
            out.add(t)
    return out


def main():
    a = sys.argv; repo = a[1]
    theta = float(a[a.index("--theta") + 1])
    out = a[a.index("--out") + 1] if "--out" in a else None
    nodes, edges = A.load_nodes(repo)
    ks = [k for k in nodes if nodes[k]["statement"]]
    sh, cs, sides = {}, {}, {}
    for k in ks:
        st = nodes[k]["statement"]
        sh[k] = M2.shape2(st); cs[k] = M2.constants(st)
        hs, cc, names = M2.sides(st)
        sides[k] = (side_constants(hs, names), side_constants(cc, names))
    n = len(ks); df = {}
    for k in ks:
        for c in cs[k]:
            df[c] = df.get(c, 0) + 1
    idf = lambda c: math.log((n + 1) / (df.get(c, 0) + 1)) + 1.0

    def sem(x, y):
        u = x | y
        return sum(idf(c) for c in x & y) / sum(idf(c) for c in u) if u else 0.0

    def sim(k1, s2, c2):
        return 0.5 * M.score(sh[k1], s2) + 0.5 * sem(cs[k1], c2)

    adj = {k: set() for k in ks}
    for i, k1 in enumerate(ks):
        for k2 in ks[i + 1:]:
            if sim(k1, sh[k2], cs[k2]) >= theta:
                adj[k1].add(k2); adj[k2].add(k1)

    def components(exclude):
        comp, cid = {}, 0
        for k in ks:
            if k == exclude or k in comp:
                continue
            cid += 1; stack = [k]
            while stack:
                x = stack.pop()
                if x in comp or x == exclude:
                    continue
                comp[x] = cid; stack.extend(adj[x] - set(comp))
        return comp

    rows = []
    for hk in HINGES:
        if hk not in sh:
            rows.append({"hinge": hk, "note": "not in atlas"}); continue
        ht, ct, head = sh[hk]
        Hs, Cs = (ht, set(), ""), (set(), ct, head)
        hc, cc = sides[hk]
        best, bn, nh, nc = 0.0, None, (0, None), (0, None)
        for k in ks:
            if k == hk:
                continue
            s_h = sim(k, Hs, hc); s_c = sim(k, Cs, cc)
            acc = min(s_h, s_c)
            if acc > best: best, bn = acc, k
            if s_h > nh[0]: nh = (s_h, k)
            if s_c > nc[0]: nc = (s_c, k)
        comp = components(hk)
        same = nh[1] is not None and nc[1] is not None and comp.get(nh[1]) == comp.get(nc[1])
        rows.append({"hinge": hk, "outcome": nodes[hk]["outcome"], "hypothesis_side_empty": not ht, "access": round(best, 3), "access_node": bn,
                     "nearest_hypothesis_side": nh[1], "nearest_conclusion_side": nc[1], "shores_same_component": same,
                     "degree_in_neighbourhood_graph": len(adj[hk]),
                     "discovered_adjacent": sum(1 for (s, t, _) in edges if t == hk and nodes.get(s, {}).get("kind") == "discovered")})
    comps = components(None)
    targets_by_comp = {}
    for k, c in comps.items():
        t = M2.TARGET.get(nodes[k].get("blueprint") or "")
        if t:
            targets_by_comp.setdefault(c, set()).add(t)
    span4 = sum(1 for v in targets_by_comp.values() if len(v) == 4)
    empty = sum(1 for k in ks if not sh[k][0])
    print(f"nodes {len(ks)}; neighbourhood edges {sum(len(v) for v in adj.values())//2} at theta {theta}; components {len(set(comps.values()))}; components spanning all four targets {span4}; empty hypothesis side {empty}/{len(ks)}")
    print(f"{'hinge':52s} {'outcome':8s} {'H':2s} {'access':7s} {'shores':7s} {'deg':4s} {'disc':4s}")
    for r in rows:
        if "note" in r:
            print(f"{r['hinge']:52s} {r['note']}"); continue
        print(f"{r['hinge']:52s} {str(r['outcome']):8s} {'-' if r['hypothesis_side_empty'] else 'y':2s} {r['access']:<7.3f} {'same' if r['shores_same_component'] else 'DIFF':7s} {r['degree_in_neighbourhood_graph']:<4d} {r['discovered_adjacent']:<4d}")
    if out:
        json.dump({"theta": theta, "nodes": len(ks), "components": len(set(comps.values())), "components_spanning_four": span4,
                   "empty_hypothesis_side": empty, "rows": rows}, open(os.path.join(repo, out), "w"), indent=1)


if __name__ == "__main__":
    main()
