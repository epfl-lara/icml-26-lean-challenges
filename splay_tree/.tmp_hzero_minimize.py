import importlib.util, random
from pathlib import Path
SPEC=importlib.util.spec_from_file_location("b", Path(".tmp_pair_certificate_search.py"))
base=importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(base)
spl,splay,N,E=base.path_len,base.splay,base.N,base.E
def keys(t): return [] if not t else keys(t[0])+[t[1]]+keys(t[2])
def gap_seq(init,q,s):
    a=init;r=init;best=0;bp=None
    for k in range(len(s)-1):
        i=s[k]; a2=splay(a,i); r2=splay(splay(r,i),q) if i<q else r
        if i<q:
            for z in s[k+1:]:
                if z<q:
                    g=max(0,spl(a2,z)+spl(splay(a2,z),q)-spl(a2,q)-spl(r2,z)-spl(splay(r2,z),q))
                    if g>best: best=g;bp=k
                    break
        a,r=a2,r2
    return best,bp
def witness_gap(init,q,s):
    g,_=gap_seq(init,q,s); return g
random.seed(2)
# find smallest-q witness via random search at small q
found=None
import time;t0=time.time()
while time.time()-t0<40 and not found:
    q=random.choice([6,7,8,9,10])
    shape=random.choice(("left","balanced","right","random"))
    init=base.rooted_tree(q,0,shape)
    if keys(init)!=list(range(q+1)): continue
    s=[v for v in base.random_avoiding_seq(0,q,random.choice([2*q,3*q,4*q])) if v<q]
    if len(s)<3 or not base.avoids231(s): continue
    if witness_gap(init,q,s)>0:
        found=(q,shape,init,s)
if not found:
    print("no small witness in time"); raise SystemExit
q,shape,init,s=found
# greedily shrink s (keep avoiding + gap>0)
changed=True
while changed:
    changed=False
    for idx in range(len(s)):
        t=s[:idx]+s[idx+1:]
        if len(t)>=2 and base.avoids231(t) and witness_gap(init,q,t)>0:
            s=t;changed=True;break
g,bp=gap_seq(init,q,s)
print(f"MINIMAL witness: q={q} (root key {q}), tree shape '{shape}', leftKeys={keys(init)}")
print(f"  seq={s}  (231-avoiding: {base.avoids231(s)}, all< q: {all(v<q for v in s)})")
print(f"  gap_after_lower>0 at pos={bp}: done={s[:bp]} i={s[bp]} future={s[bp+1:]}  gap={g}")
