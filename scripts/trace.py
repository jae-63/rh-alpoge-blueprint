import sys, re, json, collections
# usage (run inside the work dir holding decls.tsv): RH_SRC=<path to rh-alpoge/src> python3 -I trace.py ROOT[,ROOT2] DEPTH OUT.json
import os
S=os.path.join(os.environ.get('RH_SRC','../rh-alpoge/src'),'')
decl={}  # name -> (kind,mod,line)
for l in open('decls.tsv'):
    n,k,m,ln=l.rstrip('\n').split('\t')
    if n not in decl: decl[n]=(k,m,int(ln))
filecache={}
def lines(mod):
    if mod not in filecache:
        if len(filecache)>20000: filecache.clear()
        filecache[mod]=open(S+mod.replace('.','/')+'.lean',encoding='utf-8',errors='replace').read().split('\n')
    return filecache[mod]
top=re.compile(r'^(theorem|lemma|def|abbrev|structure|class|instance|inductive|end\b|namespace|@\[|private|protected|noncomputable|open|section|variable|universe|set_option|attribute|example|macro|notation|local|scoped)')
tok=re.compile(r"[A-Za-z_Ͱ-Ͽᴀ-ᶿ][\w.'!?₀-ₜͰ-Ͽ]*")
def body(n):
    k,m,ln=decl[n]; L=lines(m); out=[L[ln-1]]
    for i in range(ln, len(L)):
        if top.match(L[i]): break
        out.append(L[i])
    return out
def opens(m):
    o=[]; ns=[]
    for x in lines(m):
        if x.startswith('open '): o+= [w for w in x[5:].split() if w[0].isupper()]
        if x.startswith('namespace '): ns.append(x.split()[1])
    return o, ns
def refs(n):
    k,m,ln=decl[n]; txt='\n'.join(body(n)); first=txt.split('\n')[0]
    o,ns=opens(m)
    parts=n.split('.'); prefixes=['.'.join(parts[:i]) for i in range(len(parts)-1,0,-1)]
    for x in ns: prefixes += [x]
    prefixes += o
    found=[]; seen=set()
    for t in tok.findall(txt):
        t=t.rstrip('.')
        if t.startswith('_root_.'): t=t[7:]
        cands=[t]+[p+'.'+t for p in prefixes]
        # also try stripping trailing field projections
        for c in cands:
            cc=c
            hit=None
            while cc:
                if cc in decl: hit=cc; break
                if '.' not in cc: break
                cc=cc.rsplit('.',1)[0]
                if cc.count('.')<1 and cc not in decl: break
            if hit and hit!=n and hit not in seen and '.' in hit:
                seen.add(hit); found.append(hit); break
    return found
roots=sys.argv[1].split(','); depth=int(sys.argv[2])
seen={r:0 for r in roots}; q=collections.deque(roots); edges=[]
while q:
    n=q.popleft(); d=seen[n]
    if d>=depth: continue
    for r in refs(n):
        edges.append((n,r))
        if r not in seen: seen[r]=d+1; q.append(r)
json.dump({'nodes':{n:{'d':d,'kind':decl[n][0],'mod':decl[n][1],'line':decl[n][2],'head':' '.join(body(n)[:3])[:600]} for n,d in seen.items()},'edges':edges}, open(sys.argv[3],'w'), indent=0)
print(len(seen),'nodes',len(edges),'edges', file=sys.stderr)
