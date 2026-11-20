import sys, collections, json
imp=collections.defaultdict(list); size={}
for l in open('imports.tsv'):
    a,b=l.rstrip('\n').split('\t'); imp[a].append(b)
for l in open('sizes.tsv'):
    m,ln,nd=l.split('\t'); size[m]=(int(ln),int(nd))
root=sys.argv[1]; D=int(sys.argv[2])
lvl={root:0}; q=collections.deque([root]); E=[]
while q:
    n=q.popleft()
    if lvl[n]>=D: continue
    for b in imp[n]:
        if b not in size: continue  # Mathlib
        E.append((n,b))
        if b not in lvl: lvl[b]=lvl[n]+1; q.append(b)
# closure sizes
def closure(m):
    s={m}; st=[m]
    while st:
        x=st.pop()
        for b in imp[x]:
            if b in size and b not in s: s.add(b); st.append(b)
    return s
out={'levels':lvl,'edges':E,'closure':{}}
for n in lvl:
    if lvl[n]<=2: out['closure'][n]=len(closure(n))
json.dump(out,open(sys.argv[3],'w'))
for n,v in sorted(lvl.items(),key=lambda x:(x[1],x[0])):
    print(v, n, size[n], out['closure'].get(n,''))
