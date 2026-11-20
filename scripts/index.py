import os, re, sys, json
root = sys.argv[1]; out = sys.argv[2]
imp_re = re.compile(r'^import\s+(.+)$')
decl_re = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*(theorem|lemma|def|abbrev|structure|class|instance|inductive)\s+([^\s:({\[⦃]+)')
ns_re = re.compile(r'^namespace\s+(\S+)')
end_re = re.compile(r'^end(?:\s+(\S+))?\s*$')
sec_re = re.compile(r'^(?:noncomputable\s+)?section(?:\s+(\S+))?')
imports = open(out+'/imports.tsv','w'); decls = open(out+'/decls.tsv','w'); sizes=open(out+'/sizes.tsv','w')
n=0
for dp, dn, fn in os.walk(root):
    dn.sort()
    for f in fn:
        if not f.endswith('.lean'): continue
        p = os.path.join(dp,f); mod = os.path.relpath(p,root)[:-5].replace('/','.')
        stack=[]; lines=0; nd=0
        with open(p, encoding='utf-8', errors='replace') as fh:
            for line in fh:
                lines+=1
                if line.startswith('import'):
                    m=imp_re.match(line)
                    if m:
                        for t in m.group(1).split(): imports.write(f"{mod}\t{t}\n")
                    continue
                if line[0:1] in ' \t\n': continue
                m=ns_re.match(line)
                if m: stack.append(('ns',m.group(1))); continue
                m=sec_re.match(line)
                if m: stack.append(('sec',m.group(1) or '')); continue
                m=end_re.match(line)
                if m:
                    if stack: stack.pop()
                    continue
                m=decl_re.match(line)
                if m:
                    name=m.group(2)
                    pre='.'.join(x[1] for x in stack if x[0]=='ns')
                    if name.startswith('_root_.'): full=name[7:]
                    elif pre: full=pre+'.'+name
                    else: full=name
                    decls.write(f"{full}\t{m.group(1)}\t{mod}\t{lines}\n"); nd+=1
        sizes.write(f"{mod}\t{lines}\t{nd}\n")
        n+=1
        if n%20000==0: print(n, file=sys.stderr)
print("files",n)
