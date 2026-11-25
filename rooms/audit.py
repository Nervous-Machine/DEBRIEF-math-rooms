#!/usr/bin/env python3
"""Seal audit. usage: audit.py TRANSCRIPT.jsonl  — lists every tool call an agent made (name and command/path),
and flags web, network, git, gh and subagent use, plus any path outside the allowed inputs. Read-only."""
import json, re, sys
from collections import Counter
T = sys.argv[1]
uses = []
for line in open(T):
    try: d = json.loads(line)
    except Exception: continue
    m = d.get("message") or d
    content = m.get("content") if isinstance(m, dict) else None
    if isinstance(content, list):
        for b in content:
            if isinstance(b, dict) and b.get("type") == "tool_use":
                inp = b.get("input", {})
                s = inp.get("command") or inp.get("file_path") or inp.get("query") or inp.get("url") or inp.get("prompt") or json.dumps(inp)[:200]
                uses.append((b.get("name"), str(s).replace("\n", " ")))
print(Counter(n for n, _ in uses))
flags = re.compile(r"\b(curl|wget|gh |git (fetch|clone|pull)|pip |npm |ssh |nc )|WebFetch|WebSearch|KEEP_OUT|sealed|Solution\.lean|fc-palomar", re.I)
for n, s in uses:
    mark = "  <-- FLAG" if (n in ("WebFetch", "WebSearch", "Agent") or flags.search(s)) else ""
    print(f"{n:10s} {s[:200]}{mark}")
