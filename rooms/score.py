#!/usr/bin/env python3
"""Scorer for the rooms experiment. usage: score.py REPO_DIR REGIME [--predictions blueprint_predictions.yaml]
                                           [--control FILE.lean] [--tokens N]

Reads results/REGIME/calls.tsv and results/REGIME/attempts/, the blueprint nodes, the Challenge, and writes
results/REGIME/score.json plus results/REGIME/final.lean (the file as it was at the first FINAL call). Every number
is computed from the log and the files; nothing is typed in. With --predictions (opened after the last regime) it adds
the planner error by node; with --control it scores the control file with the same shape measures; --tokens records
the run's total tokens as reported by the agent harness (the only number that comes from outside the log).

Shape measures follow the archive traces where a one-file development allows it: declarations, dependency edges by
name mention, declarations unused by the root, depth (longest dependency path from the root inside the file), own
lines per declaration (header to next header), and the retry regex of the suffix trace. Standard library plus PyYAML.
"""
import json, math, os, re, statistics, subprocess, sys

try:
    import yaml
except ImportError:
    sys.exit("score.py needs PyYAML")

ROOT = "erdos_766.variants.dirac_erdos"
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|nonrec\s+)*(theorem|lemma|def|abbrev|instance|structure|inductive|example)\s+([^\s:({\[]+)", re.M)
RETRY = re.compile(r"((_alt\d*)+|_(bis|ter|quater)|_(new|old|v\d+|try\d*|attempt\d*|fix\d*|aux\d*|prime|redo|again|final|ok))$")
FIT_TOKENS = {"sorry": re.compile(r"\bsorry\b"), "admit": re.compile(r"\badmit\b"), "axiom": re.compile(r"^\s*axiom\b", re.M),
              "native_decide": re.compile(r"\bnative_decide\b"), "unsafe": re.compile(r"\bunsafe\b"),
              "maxHeartbeats_raised": re.compile(r"maxHeartbeats\s+([5-9]\d{5,}|\d{7,})")}


def norm(s):
    return re.sub(r"\s+", " ", re.sub(r"--[^\n]*", "", s)).strip()


def decls(text):
    """[(name, kind, start_line, end_line, body)] in file order; a declaration runs to the next header."""
    lines = text.split("\n")
    heads = [(m.start(), m.group(2), m.group(1)) for m in DECL.finditer(text)]
    out = []
    for i, (pos, name, kind) in enumerate(heads):
        end = heads[i + 1][0] if i + 1 < len(heads) else len(text)
        body = text[pos:end]
        start_line = text.count("\n", 0, pos) + 1
        end_line = start_line + body.rstrip("\n").count("\n")
        out.append((name, kind, start_line, end_line, body))
    return out


def shape(text):
    ds = decls(text)
    names = [d[0] for d in ds]
    short = {n.split(".")[-1]: n for n in names}
    uses = {}
    for name, kind, s, e, body in ds:
        hdr_end = body.find(":=")
        used = set()
        for other in names:
            if other == name:
                continue
            if re.search(r"(?<![\w.])" + re.escape(other.split(".")[-1]) + r"(?![\w'])", body):
                used.add(other)
        uses[name] = used
    root = next((n for n in names if n.endswith(ROOT.split(".")[-1])), None)
    reach = set()
    if root:
        stack = [root]
        while stack:
            x = stack.pop()
            if x in reach:
                continue
            reach.add(x)
            stack.extend(uses.get(x, ()))
    unused = [n for n in names if n not in reach and n != root]
    memo = {}

    def depth(n, seen=()):
        if n in memo:
            return memo[n]
        if n in seen:
            return 0
        d = 1 + max([depth(u, seen + (n,)) for u in uses.get(n, ())] or [0])
        memo[n] = d
        return d
    own = [e - s + 1 for _, _, s, e, _ in ds]
    joins = [n for n in names if sum(n in uses[m] for m in names) >= 2]
    return {"declarations": len(ds), "unused_by_root": unused, "unused_count": len(unused), "root_found": bool(root),
            "depth": depth(root) if root else None, "own_lines_median": statistics.median(own) if own else None,
            "own_lines": dict(zip(names, own)), "retry_named": [n for n in names if RETRY.search(n.split(".")[-1])],
            "joins": joins, "edges": sum(len(v) for v in uses.values())}


def fit_indicators(final_text, challenge_text, nodes):
    f = {k: len(rx.findall(final_text)) for k, rx in FIT_TOKENS.items()}
    # the root statement and the definitions it uses must appear verbatim (whitespace- and comment-insensitive)
    ch = [d for d in decls(challenge_text) if d[1] in ("def", "theorem", "lemma", "abbrev")]
    fn = {d[0]: d for d in decls(final_text)}
    changed = []
    for name, kind, s, e, body in ch:
        sig = norm(body.split(":=")[0])
        if name not in fn:
            changed.append({"name": name, "how": "missing"})
        elif norm(fn[name][4].split(":=")[0]) != sig:
            changed.append({"name": name, "how": "signature differs"})
        elif kind == "def" and norm(fn[name][4]) != norm(body):
            changed.append({"name": name, "how": "definition body differs"})
    node_changed = []
    for n in nodes or []:
        want = norm(str(n.get("statement", "")).split(":=")[0])
        nm = str(n.get("name", ""))
        have = fn.get(nm) or next((d for k, d in fn.items() if k.endswith("." + nm)), None)
        if have is None:
            node_changed.append({"id": n["id"], "how": "absent"})
        elif norm(have[4].split(":=")[0]) != want:
            node_changed.append({"id": n["id"], "how": "signature differs"})
    f["challenge_changed"] = changed
    f["nodes_changed"] = node_changed
    f["total"] = sum(v for k, v in f.items() if isinstance(v, int)) + len(changed)
    return f


def axioms_in_vm(final_path):
    """Compile the final file plus `#print axioms ROOT` in the pinned project; returns the printed axiom line or the error."""
    try:
        text = open(final_path).read() + f"\n#print axioms Erdos766.{ROOT}\n"
        tmp = final_path + ".axioms.lean"
        open(tmp, "w").write(text)
        subprocess.run(["limactl", "copy", tmp, "primegaps:/home/heidibennett.guest/rooms/project/Rooms/Axioms.lean"], check=True, capture_output=True)
        r = subprocess.run(["limactl", "shell", "primegaps", "--", "sh", "-c", "cd ~/rooms/project && PATH=$HOME/.elan/bin:$PATH timeout 900 lake env lean Rooms/Axioms.lean"], capture_output=True, text=True)
        os.remove(tmp)
        out = r.stdout + r.stderr
        m = re.search(r"depends on axioms: \[([^\]]*)\]", out)
        return {"rc": r.returncode, "axioms": [a.strip() for a in m.group(1).split(",")] if m else None, "tail": out[-800:]}
    except Exception as ex:  # the scorer never fails on this; the absence is recorded
        return {"rc": None, "axioms": None, "tail": f"not run: {ex}"}


def main():
    repo = sys.argv[1]; regime = sys.argv[2]
    args = sys.argv[3:]
    opt = {args[i]: args[i + 1] for i in range(0, len(args) - 1, 2) if args[i].startswith("--")}
    rdir = os.path.join(repo, "results", regime)
    calls = [l.rstrip("\n").split("\t") for l in open(os.path.join(rdir, "calls.tsv"))] if os.path.exists(os.path.join(rdir, "calls.tsv")) else []
    nodes = (yaml.safe_load(open(os.path.join(repo, "blueprint_nodes.yaml"))) or {}).get("nodes", []) if os.path.exists(os.path.join(repo, "blueprint_nodes.yaml")) else []
    kind = {n["id"]: n.get("kind", "leaf") for n in nodes}
    challenge = open(os.path.join(repo, "rooms", "Challenge.lean")).read()
    per_node, refused, finals = {}, 0, []
    for c in calls:
        seq, ts, node, status = c[0], c[1], c[2], c[3]
        if status == "refused":
            refused += 1; continue
        if node == "FINAL":
            finals.append((seq, status)); continue
        d = per_node.setdefault(node, {"attempts": 0, "ok": 0, "error": 0, "timeout": 0, "secs": 0})
        d["attempts"] += 1; d[status if status in d else "error"] += 1
        d["secs"] += int(next((x.split("=")[1] for x in c if x.startswith("secs=")), 0))
    score = {"regime": regime, "calls": len(calls), "refused": refused, "final_calls": finals, "per_node": per_node}
    if finals:
        seq, status = finals[0]
        src = os.path.join(rdir, "attempts", f"{seq}.lean"); dst = os.path.join(rdir, "final.lean")
        open(dst, "w").write(open(src).read())
        text = open(dst).read()
        score["final_status_at_first_FINAL"] = status
        score["shape"] = shape(text)
        score["fit"] = fit_indicators(text, challenge, nodes)
        score["axioms"] = axioms_in_vm(dst) if status == "ok" else {"rc": None, "axioms": None, "tail": "final did not compile clean"}
        std = {"propext", "Classical.choice", "Quot.sound"}
        ax = score["axioms"]["axioms"]
        score["comparator_pass"] = bool(status == "ok" and ax is not None and set(ax) <= std and not score["fit"]["challenge_changed"] and score["shape"]["root_found"])
    att = {n: d["attempts"] for n, d in per_node.items()}
    j = [att[n] for n in att if kind.get(n) == "join"]; l = [att[n] for n in att if kind.get(n) == "leaf"]
    score["attempts_median"] = statistics.median(att.values()) if att else None
    score["attempts_median_joins"] = statistics.median(j) if j else None
    score["attempts_median_leaves"] = statistics.median(l) if l else None
    if "--tokens" in opt:
        score["tokens_total"] = int(opt["--tokens"])
    if "--predictions" in opt and os.path.exists(opt["--predictions"]):
        pred = {n["id"]: n.get("predicted", {}) for n in (yaml.safe_load(open(opt["--predictions"])) or {}).get("nodes", [])}
        err = {}
        for n, a in att.items():
            p = (pred.get(n) or {}).get("attempts")
            if p:
                err[n] = round(math.log2(max(a, 1) / max(p, 1)), 3)
        ej = [err[n] for n in err if kind.get(n) == "join"]; el = [err[n] for n in err if kind.get(n) == "leaf"]
        score["planner_error"] = {"log2_by_node": err, "median_joins": statistics.median(ej) if ej else None, "median_leaves": statistics.median(el) if el else None,
                                  "median_abs_joins": statistics.median(map(abs, ej)) if ej else None, "median_abs_leaves": statistics.median(map(abs, el)) if el else None}
    if "--control" in opt and os.path.exists(opt["--control"]):
        score["control_shape"] = shape(open(opt["--control"]).read())
    json.dump(score, open(os.path.join(rdir, "score.json"), "w"), indent=1, ensure_ascii=False)
    print(json.dumps({k: v for k, v in score.items() if k not in ("per_node", "shape", "fit", "axioms", "control_shape")}, indent=1))
    if "shape" in score:
        s = score["shape"]; print("shape:", {k: s[k] for k in ("declarations", "unused_count", "depth", "own_lines_median", "retry_named", "joins")})
        print("fit:", score["fit"]["total"], score["fit"]["challenge_changed"], score["fit"]["nodes_changed"][:5])
        print("axioms:", score["axioms"]["axioms"], "comparator_pass:", score.get("comparator_pass"))


if __name__ == "__main__":
    main()
