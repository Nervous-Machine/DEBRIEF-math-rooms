#!/usr/bin/env python3
"""Forced-attempt scorer (build 4). usage: forced_score.py REPO_DIR ARM [--tokens N]
Reads results/ARM/forced.conf (node=, name=, allowed=, start=), calls.tsv, attempts/*.lean|.out and writes
results/ARM/forced.json: one row per logged call (refused calls included) with, for compiled attempts, the number of
Lean errors, the declarations new relative to the start file, the forced declaration's own lines, `first |` hedges in
the forced region (the forced declaration plus every new declaration), whether the comment-stripped file equals the
previous attempt at the same node, and the declarations outside the allowed list that carry sorry; plus a summary:
genuine attempts at the forced node, refusals by reason, whether the forced declaration is closed at the first FINAL
(read from Lean's sorry warnings), errors at the first and last genuine attempt, new declarations at FINAL, minutes
from the first call to the first FINAL, and tokens if given. Shape and fit come from score.py as before.
Standard library only."""
import json, os, re, sys

DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|nonrec\s+)*(theorem|lemma|def|abbrev|instance|structure|inductive|example)\s+([^\s:({\[]+)", re.M)
ERR = re.compile(r"^[^\n]*:\d+:\d+: error", re.M)
SORRYW = re.compile(r"^[^\n]*:(\d+):\d+: warning: declaration uses `sorry`", re.M)
HEDGE = re.compile(r"\bfirst\s*\|")


def strip_comments(s):
    return re.sub(r"--[^\n]*", "", re.sub(r"/-.*?-/", "", s, flags=re.S))


def decls(text):
    heads = [(m.start(), m.group(2)) for m in DECL.finditer(text)]
    out = []
    for i, (pos, name) in enumerate(heads):
        end = heads[i + 1][0] if i + 1 < len(heads) else len(text)
        body = text[pos:end]
        start_line = text.count("\n", 0, pos) + 1
        out.append((name, start_line, start_line + body.rstrip("\n").count("\n"), body))
    return out


def main():
    repo, arm = sys.argv[1], sys.argv[2]
    tokens = int(sys.argv[sys.argv.index("--tokens") + 1]) if "--tokens" in sys.argv else None
    d = os.path.join(repo, "results", arm)
    conf = dict(l.rstrip("\n").split("=", 1) for l in open(os.path.join(d, "forced.conf")) if "=" in l)
    # build 8: several forced rooms (nodes=, names=); the summary's forced_node fields refer to the first, and a per-room
    # table is added under "forced_rooms"
    fnodes = (conf.get("nodes") or conf.get("node", "")).split(","); fnames = (conf.get("names") or conf.get("name", "")).split(",")
    fnode, fname = fnodes[0], fnames[0]
    allowed = {l.strip() for l in open(os.path.join(repo, conf["allowed"])) if l.strip()} if os.path.exists(os.path.join(repo, conf["allowed"])) else set()
    start = open(os.path.join(repo, conf["start"]), encoding="utf-8").read()
    start_names = {n for n, *_ in decls(start)}
    rows = []
    prev_by_node = {}
    for line in open(os.path.join(d, "calls.tsv"), encoding="utf-8"):
        f = line.rstrip("\n").split("\t")
        if len(f) < 5:
            continue
        seq, ts, node, status = f[0], f[1], f[2], f[3]
        row = {"seq": seq, "ts": ts, "node": node, "status": status, "detail": f[4] if status == "refused" else " ".join(f[4:])}
        lean = os.path.join(d, "attempts", seq + ".lean")
        if os.path.exists(lean):
            text = open(lean, encoding="utf-8").read()
            ds = decls(text)
            new = [n for n, *_ in ds if n not in start_names]
            forced = [x for x in ds if x[0].split(".")[-1] == fname]
            region = "".join(strip_comments(x[3]) for x in ds if x[0] in new or x[0].split(".")[-1] == fname)
            sorry_outside = [x[0] for x in ds if re.search(r"\bsorry\b", strip_comments(x[3])) and x[0].split(".")[-1] not in allowed]
            key = re.sub(r"\s+", " ", strip_comments(text))
            row.update({"new_declarations": len(new), "new_names": new, "forced_own_lines": (forced[0][2] - forced[0][1] + 1) if forced else None,
                        "hedges_in_forced_region": len(HEDGE.findall(region)), "same_as_previous_at_node": key == prev_by_node.get(node),
                        "sorry_outside_allowed": sorry_outside, "lines": text.count("\n") + 1})
            prev_by_node[node] = key
            out = os.path.join(d, "attempts", seq + ".out")
            if status != "refused" and os.path.exists(out):
                o = open(out, encoding="utf-8", errors="replace").read()
                row["errors"] = len(ERR.findall(o))
                sorry_lines = [int(m.group(1)) for m in SORRYW.finditer(o)]
                row["sorry_declarations_by_lean"] = sorted({x[0] for x in ds for ln in sorry_lines if x[1] <= ln <= x[2]})
        rows.append(row)
    genuine = [r for r in rows if r["node"] == fnode and r["status"] != "refused"]
    refusals = {}
    for r in rows:
        if r["status"] == "refused":
            reason = re.sub(r"\d+ of 12", "k of 12", r["detail"].split(":")[0] + (": sorry in" if "sorry in" in r["detail"] else ""))
            refusals[reason] = refusals.get(reason, 0) + 1
    finals = [r for r in rows if r["node"] == "FINAL" and r["status"] != "refused"]
    first_final = finals[0] if finals else None
    closed = None
    if first_final and "sorry_declarations_by_lean" in first_final:
        closed = first_final["status"] != "error" and not any(n.split(".")[-1] == fname for n in first_final["sorry_declarations_by_lean"])

    def mins(a, b):
        from datetime import datetime
        p = lambda s: datetime.strptime(s, "%Y-%m-%dT%H:%M:%SZ")
        return round((p(b) - p(a)).total_seconds() / 60, 1)

    summary = {"arm": arm, "forced_node": fnode, "forced_name": fname, "allowed_sorry": sorted(allowed), "calls_logged": len(rows),
               "genuine_attempts_at_forced_node": len(genuine), "refusals": refusals,
               "refused_finals": sum(1 for r in rows if r["node"] == "FINAL" and r["status"] == "refused"),
               "forced_closed_at_first_final": closed, "first_final_status": first_final["status"] if first_final else None,
               "errors_first_genuine": genuine[0].get("errors") if genuine else None, "errors_last_genuine": genuine[-1].get("errors") if genuine else None,
               "genuine_statuses": [r["status"] for r in genuine],
               "genuine_with_new_declarations": sum(1 for r in genuine if r.get("new_declarations", 0) > 0),
               "genuine_same_as_previous": sum(1 for r in genuine if r.get("same_as_previous_at_node")),
               "hedges_in_forced_region_at_first_final": first_final.get("hedges_in_forced_region") if first_final else None,
               "new_declarations_at_first_final": first_final.get("new_declarations") if first_final else None,
               "sorry_outside_allowed_at_first_final": first_final.get("sorry_outside_allowed") if first_final else None,
               "minutes_to_first_final": mins(rows[0]["ts"], first_final["ts"]) if rows and first_final else None, "tokens": tokens}
    per_room = []
    for fn, nm in zip(fnodes, fnames):
        g = [r for r in rows if r["node"] == fn and r["status"] != "refused"]
        closed_r = None
        if first_final and "sorry_declarations_by_lean" in first_final:
            closed_r = first_final["status"] != "error" and not any(n.split(".")[-1] == nm for n in first_final["sorry_declarations_by_lean"])
        per_room.append({"node": fn, "name": nm, "genuine_attempts": len(g), "statuses": [r["status"] for r in g], "closed_at_first_final": closed_r})
    summary["forced_rooms"] = per_room
    json.dump({"summary": summary, "calls": rows}, open(os.path.join(d, "forced.json"), "w"), indent=1, ensure_ascii=False)
    print(json.dumps(summary, indent=1, ensure_ascii=False))


if __name__ == "__main__":
    main()
