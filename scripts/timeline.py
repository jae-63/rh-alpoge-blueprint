# Keyword search for the 20 timeline items of the author's note (remark.pdf, p.3-4).
# usage (in work dir): python3 -I timeline.py t12.json > timeline.txt
import re, sys, json, collections
reach = json.load(open(sys.argv[1]))["nodes"]
ITEMS = {
 1: ("Stepanov determinant", r"stepanov|determinant|wronsk"),
 2: ("D^p = 0 on CM curve, invariant derivation", r"invariantderiv|serrederiv|derivation.*cm|cmcurve|ramanujanderiv"),
 3: ("qN = M^k + R, path quadric, Poincaré bundle, sixfold cover", r"quadric|pathquad|poincarebundle|sixfold|parseval"),
 4: ("W(1_S) >= 0 via a determinant", r"weilpositiv|wnonneg|w_nonneg|positivitycriterion|weilcriterion"),
 5: ("smoothed von Mangoldt sum, Guinand-Weil", r"guinand|explicitformula|vonmangoldt"),
 6: ("W(...) >= 0 gives zero-free beyond 1 - eta", r"zerofree"),
 7: ("GGP periods, interlacing", r"ggp|interlac|besselperiod|gangross"),
 8: ("iterated theta lifts U(X0) -> ... -> U(Xm)", r"iteratedlift|iteratedtheta|thetachain|liftchain|chainlift|iterlift"),
 9: ("Chowla-Selberg, Weyl, Siegel mass", r"chowlaselberg|siegelmass|massformula"),
 10: ("divisibility of the m-fold lift", r"divisib"),
 11: ("Iwasawa tower", r"iwasawa"),
 12: ("Seesaw, Bessel period, Rallis", r"seesaw|rallis"),
 13: ("Bost slope inequality", r"bost|slopeineq"),
 14: ("cost of each lift; 2/3; division", r"costwindow|liftcost|twothird|division"),
 15: ("integral structure across Hecke characters (gcd)", r"integralstructure|heckegcd"),
 16: ("relative trace formula, projected Poincaré series", r"relativetrace|poincareseries"),
 17: ("H^1(o_E[1/l], Q_l/Z_l(-e)), weak Vandiver", r"vandiver|shalen|kgroup|lichtenbaum"),
 18: ("covolumes, theta-series index, congruences", r"covol|thetaindex|congruencebetween"),
 19: ("Behrend sets in the Iwasawa tower", r"behrend"),
}
allhits = {k: [] for k in ITEMS}
pats = {k: re.compile(p, re.I) for k, (_, p) in ITEMS.items()}
for l in open("decls.tsv"):
    n, kind, mod, ln = l.rstrip("\n").split("\t")
    key = (n + " " + mod).replace("_", "").replace(".", " ")
    for k, p in pats.items():
        if p.search(key): allhits[k].append((n, kind, mod, ln))
def grp(m, d=4): return ".".join(m.split(".")[:d])
for k, (title, pat) in ITEMS.items():
    H = allhits[k]; R = [h for h in H if h[0] in reach]
    print(f"## {k}. {title}   /{pat}/")
    print(f"   all={len(H)} reached(d<=12)={len(R)}  min depth={min([reach[h[0]]['d'] for h in R], default='-')}")
    for g, c in collections.Counter(grp(h[2]) for h in (R or H)).most_common(4): print(f"   {c:5d} {g}")
    for h in sorted(R, key=lambda h: reach[h[0]]['d'])[:6]: print(f"     d={reach[h[0]]['d']} {h[0]}  [{h[2]}:{h[3]}]")
    if not R:
        for h in H[:3]: print(f"     (unreached) {h[0]}  [{h[2]}:{h[3]}]")
