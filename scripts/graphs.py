# usage: python3 -I scripts/graphs.py <workdir with decls.tsv,sizes.tsv,t4.json,t8.json,imp4.json> <outdir>
import sys, json, collections, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from pillars import pillar, RULES
W, OUT = sys.argv[1], sys.argv[2]
P = [r[0] for r in RULES] + ["Other"]
ids = {p: f"P{i}" for i, p in enumerate(P)}
COL = ["#d62728","#9467bd","#1f77b4","#ff7f0e","#bcbd22","#2ca02c","#17becf","#8c564b","#e377c2","#7f7f7f","#aec7e8","#c7c7c7","#dbdb8d","#f7f7f7","#ffffff"]
col = {p: COL[i % len(COL)] for i, p in enumerate(P)}

# whole-repo size per pillar
files = collections.Counter(); lines = collections.Counter()
for l in open(f"{W}/sizes.tsv"):
    m, ln, nd = l.split("\t"); files[pillar(m)] += 1; lines[pillar(m)] += int(ln)

def pillar_graph(tj, tag):
    d = json.load(open(f"{W}/{tj}"))
    nodes = d["nodes"]; cnt = collections.Counter(pillar(v["mod"]) for v in nodes.values())
    E = collections.Counter()
    for a, b in d["edges"]:
        pa, pb = pillar(nodes[a]["mod"]), pillar(nodes[b]["mod"])
        if pa != pb: E[(pa, pb)] += 1
    return cnt, E, nodes, d["edges"]

cnt, E, nodes8, _ = pillar_graph("t8.json", "8")
used = [p for p in P if cnt[p]]
with open(f"{OUT}/pillars.dot", "w") as f:
    f.write('digraph pillars {\n rankdir=TB; node [shape=box, style="rounded,filled", fontname="Helvetica"];\n')
    for p in used:
        f.write(f' {ids[p]} [label="{p}\\n{cnt[p]} decls reached (depth≤8)\\n{files[p]:,} files / {lines[p]:,} lines in repo", fillcolor="{col[p]}"];\n')
    for (a, b), c in E.most_common():
        if c >= 5: f.write(f' {ids[a]} -> {ids[b]} [label="{c}", penwidth={min(1+c/200,6):.1f}];\n')
    f.write("}\n")
with open(f"{OUT}/pillars.mmd", "w") as f:
    f.write("flowchart TD\n")
    for p in used:
        f.write(f'  {ids[p]}["{p}<br/>{cnt[p]} decls reached<br/>{files[p]:,} files"]\n')
    for (a, b), c in E.most_common():
        if c >= 20: f.write(f"  {ids[a]} -->|{c}| {ids[b]}\n")
    for p in used: f.write(f"  style {ids[p]} fill:{col[p]}\n")

# declaration graph to depth 4
d4 = json.load(open(f"{W}/t4.json"))
def short(n): 
    s = n.split("."); return ".".join(s[-2:]) if len(s) > 1 else n
with open(f"{OUT}/decls-depth4.dot", "w") as f:
    f.write('digraph decls {\n rankdir=LR; node [shape=box, style="rounded,filled", fontname="Helvetica", fontsize=9];\n')
    for n, v in d4["nodes"].items():
        f.write(f' "{n}" [label="{short(n)}\\n[{v["kind"]}, d={v["d"]}]", fillcolor="{col[pillar(v["mod"])]}", tooltip="{v["mod"]}"];\n')
    for a, b in d4["edges"]:
        if a in d4["nodes"] and b in d4["nodes"]: f.write(f' "{a}" -> "{b}";\n')
    f.write("}\n")

# import graph 4 levels, aggregated by first 3 path components
imp = json.load(open(f"{W}/imp4.json"))
def grp(m): return ".".join(m.split(".")[:3])
gc = collections.Counter(grp(m) for m in imp["levels"]); gl = {}
for m, l in imp["levels"].items(): gl[grp(m)] = min(gl.get(grp(m), 99), l)
GE = collections.Counter((grp(a), grp(b)) for a, b in imp["edges"] if grp(a) != grp(b))
with open(f"{OUT}/imports-depth4.dot", "w") as f:
    f.write('digraph imports {\n rankdir=LR; node [shape=box, style="rounded,filled", fontname="Helvetica", fontsize=9];\n')
    for g, c in gc.items():
        f.write(f' "{g}" [label="{g}\\n{c} modules, first at level {gl[g]}", fillcolor="{col[pillar(g + ".x")]}"];\n')
    for (a, b), c in GE.items():
        if c >= 3: f.write(f' "{a}" -> "{b}" [label="{c}"];\n')
    f.write("}\n")

summary = {"pillar_decls_reached_depth8": dict(cnt), "pillar_files": dict(files), "pillar_lines": dict(lines),
           "pillar_edges_depth8": {f"{a} -> {b}": c for (a, b), c in E.most_common()},
           "imports_depth4_modules": len(imp["levels"]), "imports_depth4_groups": dict(gc.most_common()),
           "closure_sizes_top": imp["closure"]}
json.dump(summary, open(f"{OUT}/../data/summary.json", "w"), indent=1)
for p in used: print(f"{cnt[p]:6d} {files[p]:7d} {lines[p]:9d}  {p}")
print("edges"); [print(c, a, "->", b) for (a, b), c in E.most_common(30)]
