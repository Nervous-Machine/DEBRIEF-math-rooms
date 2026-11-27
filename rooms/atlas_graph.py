#!/usr/bin/env python3
"""The atlas as a graph (build 9b). usage: atlas_graph.py REPO_DIR [--theta 0.45] [--hinge BLUEPRINT:ID ...] [--out FILE]
Nodes: every planner room in atlas/hinges.yaml and every discovered room in atlas/discovered.yaml, keyed by
"<blueprint-or-arm>:<name>". Two kinds of edge: dependency edges (a room's depends_on; a discovered room's serves and
built_for) and neighbourhood edges (two nodes whose statement shapes score at least theta under rooms/match.py).
For a hinge h with hypotheses H and conclusion C (its binder hypotheses and conclusion, by match.py's shape):
  access(h) = max over other nodes n of min(sim(n, H-side shape of h), sim(n, C-side shape of h))
      how close the nearest single node comes to touching both shores at once;
  shores(h) = the components (neighbourhood graph at theta, h removed) of h's nearest hypothesis-side node and nearest
      conclusion-side node; "bridge without access" when they differ.
Prints a table for the hinges named (default: every forced or probed hinge on the record) and writes JSON. Standard
library plus PyYAML."""
import json, os, sys
import yaml
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__))))
import match as M


def load_nodes(repo):
    H = yaml.safe_load(open(os.path.join(repo, "atlas/hinges.yaml")))["hinges"]
    D = yaml.safe_load(open(os.path.join(repo, "atlas/discovered.yaml")))["discovered"]
    nodes, edges = {}, set()
    for h in H:
        key = f"{h['blueprint']}:{h['name']}"
        if key in nodes:
            continue
        nodes[key] = {"key": key, "name": h["name"], "statement": h.get("statement", ""), "kind": "planner", "outcome": h.get("outcome"),
                      "join_type": h.get("join_type"), "join_type_v2": h.get("join_type_v2"), "blueprint": h["blueprint"], "id": h["id"]}
    idname = {}
    for h in H:
        idname[(h["blueprint"], h["id"])] = h["name"]
    for h in H:
        for dep in (h.get("depends_on") or []):
            pass  # hinges.yaml does not carry depends_on; dependency edges for planner rooms are read from the blueprints below
    for bp in {h["blueprint"] for h in H}:
        d = yaml.safe_load(open(os.path.join(repo, bp)))
        for n in d["nodes"]:
            for dep in n.get("depends_on") or []:
                a = idname.get((bp, str(dep))); b = n.get("name") or d.get("root")
                if a and b:
                    edges.add((f"{bp}:{a}", f"{bp}:{str(b).split('.')[-1]}", "depends"))
    arm_bp = {"B3_569_A_full_hold": "blueprint_569_nodes.yaml", "B4_569_F_full_forced": "blueprint_569_nodes.yaml", "B5_C12_full_forced": "start_569B_nodes.yaml", "B5_C36_full_forced": "start_569B_nodes.yaml", "B5_C108_full_forced": "start_569B_nodes.yaml",
              "B3_159_H_full_hold": "blueprint_159_nodes.yaml", "B3_159_H_none_hold": "blueprint_159_nodes.yaml", "B3_159_H_none_plain": "blueprint_159_nodes.yaml", "B4_159_F_full_forced": "blueprint_159_nodes.yaml", "B7_159_none_plain_opus": "blueprint_159_nodes.yaml", "B8_blindhold_full_forced": "blueprint_159_nodes.yaml", "B8_blindplain_full_forced": "blueprint_159_nodes.yaml",
              "B6_1061_A_full_probe": "blueprint_1061_nodes.yaml", "B6_1133_A_full_probe": "blueprint_1133_nodes.yaml"}
    for r in D:
        key = f"{r['arm']}:{r['name']}"
        nodes[key] = {"key": key, "name": r["name"], "statement": r["statement"], "kind": "discovered", "outcome": "proved" if r["sorry_free_at_final"] else "open", "arm": r["arm"], "blueprint": arm_bp.get(r["arm"])}
        bp = arm_bp.get(r["arm"])
        for p in (r.get("serves") or []):
            if bp:
                edges.add((key, f"{bp}:{p}", "serves"))
        if r.get("built_for") and bp:
            edges.add((key, f"{bp}:{r['built_for']}", "built_for"))
    return nodes, edges


def main():
    a = sys.argv; repo = a[1]
    theta = float(a[a.index("--theta") + 1]) if "--theta" in a else 0.45
    out = a[a.index("--out") + 1] if "--out" in a else None
    nodes, edges = load_nodes(repo)
    keys = list(nodes)
    shapes = {k: M.shape(nodes[k]["statement"]) for k in keys if nodes[k]["statement"]}
    # neighbourhood graph
    adj = {k: set() for k in shapes}
    ks = list(shapes)
    for i, k1 in enumerate(ks):
        for k2 in ks[i + 1:]:
            if M.score(shapes[k1], shapes[k2]) >= theta:
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

    default = ["start_569B_nodes.yaml:core_ge_three_nonstar", "blueprint_569_nodes.yaml:lemma7", "blueprint_569_nodes.yaml:goddard_kleitman_sidorenko", "blueprint_159_nodes.yaml:core_near_extremal", "blueprint_159_nodes.yaml:turan_weak", "blueprint_159_nodes.yaml:c4_free_indep_power", "blueprint_159_nodes.yaml:floor_succ_le_power", "blueprint_159_nodes.yaml:card_le_power_of_c4_free", "blueprint_159_nodes.yaml:erdos_159",
               "blueprint_1061_nodes.yaml:lattice_coords", "blueprint_1061_nodes.yaml:local_denominator", "blueprint_1061_nodes.yaml:plane_prime_count", "blueprint_1061_nodes.yaml:lattice_reduction", "blueprint_1133_nodes.yaml:signs_prescribed_tolerance", "blueprint_1133_nodes.yaml:finite_degree_error_tradeoff"]
    hinges = [x for x in a[a.index("--hinge") + 1:] if not x.startswith("--")] if "--hinge" in a else default
    # the 569 core as the statement-only file carved it is not a planner room; add it from the B5 reference if present
    rows = []
    for hk in hinges:
        if hk not in shapes:
            rows.append({"hinge": hk, "note": "not in atlas"}); continue
        ht, ct, head = shapes[hk]
        Hs, Cs = (ht, set(), ""), (set(), ct, head)
        best_access, best_n, nh, nc = 0.0, None, (0, None), (0, None)
        for k in ks:
            if k == hk:
                continue
            sh = M.score(shapes[k], Hs) ; sc = M.score(shapes[k], Cs)
            acc = min(sh, sc)
            if acc > best_access: best_access, best_n = acc, k
            if sh > nh[0]: nh = (sh, k)
            if sc > nc[0]: nc = (sc, k)
        comp = components(hk)
        same = (nh[1] is not None and nc[1] is not None and comp.get(nh[1]) == comp.get(nc[1]))
        rows.append({"hinge": hk, "outcome": nodes[hk]["outcome"], "access": round(best_access, 3), "access_node": best_n,
                     "nearest_hypothesis_side": nh[1], "nearest_conclusion_side": nc[1], "shores_same_component": same,
                     "degree_in_neighbourhood_graph": len(adj[hk]), "discovered_adjacent": sum(1 for (s, t, _) in edges if t == hk and nodes.get(s, {}).get("kind") == "discovered")})
    print(f"nodes {len(nodes)} (planner {sum(1 for n in nodes.values() if n['kind']=='planner')}, discovered {sum(1 for n in nodes.values() if n['kind']=='discovered')}); dependency edges {len(edges)}; neighbourhood edges {sum(len(v) for v in adj.values())//2} at theta {theta}; components {len(set(components(None).values()))}")
    print(f"{'hinge':52s} {'outcome':8s} {'access':7s} {'shores':7s} {'deg':4s} {'disc':4s}")
    for r in rows:
        if "note" in r: print(f"{r['hinge']:52s} {r['note']}"); continue
        print(f"{r['hinge']:52s} {str(r['outcome']):8s} {r['access']:<7.3f} {'same' if r['shores_same_component'] else 'DIFF':7s} {r['degree_in_neighbourhood_graph']:<4d} {r['discovered_adjacent']:<4d}")
    if out:
        json.dump({"theta": theta, "nodes": len(nodes), "dependency_edges": len(edges), "rows": rows,
                   "node_list": [{k: v for k, v in n.items() if k != "statement"} for n in nodes.values()],
                   "edges": sorted(edges)}, open(os.path.join(repo, out), "w"), indent=1)


if __name__ == "__main__":
    main()
