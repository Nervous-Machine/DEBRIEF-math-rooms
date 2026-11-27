#!/usr/bin/env python3
"""Score a blind re-typing (build 8). usage: retype_score.py READER_A.yaml READER_B.yaml ATLAS.yaml ARM
Prints pairwise agreement between the two readers per blueprint, the disagreement pairs, and reach by v2 type using the
consensus type (where the readers agree) against the outcomes recorded in the atlas for the given arm. Standard library
plus PyYAML."""
import sys
from collections import Counter, defaultdict
import yaml

a = yaml.safe_load(open(sys.argv[1])); b = yaml.safe_load(open(sys.argv[2])); atlas = yaml.safe_load(open(sys.argv[3]))["hinges"]; arm = sys.argv[4]
ta, tb = a["types"], b["types"]
ids = [i for i in ta if i in tb]
agree = [i for i in ids if ta[i] == tb[i]]
print(f"{a['blueprint']}: {len(agree)}/{len(ids)} agree = {len(agree)/len(ids):.2f}")
pairs = Counter(tuple(sorted((ta[i], tb[i]))) for i in ids if ta[i] != tb[i])
for p, n in pairs.most_common(): print("   disagreement", p, n)
out = {h["id"]: h["outcome"] for h in atlas if h["arm"] == arm}
by = defaultdict(lambda: [0, 0])
for i in agree:
    if i == "ROOT" or i not in out: continue
    by[ta[i]][0] += 1; by[ta[i]][1] += out[i] == "proved"
print("reach by consensus v2 type (rooms, proved, rate):")
for t, (n, p) in sorted(by.items(), key=lambda x: -(x[1][1] / x[1][0] if x[1][0] else 0)): print(f"   {t:26s} {n:3d} {p:3d} {p/n:.2f}")
