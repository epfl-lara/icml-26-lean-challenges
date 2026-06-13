import importlib.util, random
from itertools import product
from pathlib import Path
SPEC=importlib.util.spec_from_file_location("b", Path(".tmp_pair_certificate_search.py"))
base=importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(base)
spl,splay,N,E=base.path_len,base.splay,base.N,base.E
def keys(t): return [] if not t else keys(t[0])+[t[1]]+keys(t[2])
def gap_at(a,r,q,future):
    for z in future:
        if z<q:
            return max(0, spl(a,z)+spl(splay(a,z),q)-spl(a,q)-spl(r,z)-spl(splay(r,z),q))
    return 0
def scan(init,q,s):
    """incremental: return max gap_after_lower over all positions of avoiding seq s."""
    a=init; r=init; mx=0; witpos=None
    for k in range(len(s)-1):
        i=s[k]
        a2=splay(a,i)
        r2=splay(splay(r,i),q) if i<q else r
        if i<q:
            g=gap_at(a2,r2,q,s[k+1:])
            if g>mx: mx=g; witpos=k
        a,r=a2,r2
    return mx,witpos
random.seed(1)
# exhaustive q<=6 already known 0; go straight to heavy random, efficient
best=0; wit=None; n=0
import time; t0=time.time()
while time.time()-t0<70:
    q=random.choice([8,13,21,34,40])
    init=base.rooted_tree(q,0,random.choice(("left","balanced","right","random")))
    if keys(init)!=list(range(q+1)): continue
    s=[v for v in base.random_avoiding_seq(0,q,random.choice([q,2*q,3*q])) if v<q]
    if len(s)<2 or not base.avoids231(s): continue
    n+=1
    g,p=scan(init,q,s)
    if g>best: best=g; wit=(q,s,p)
print(f"random avoiding seqs tested: {n}")
print(f"max gap_after_lower = {best}")
if wit and best>0:
    q,s,p=wit; print(f"WITNESS q={q} seq={s} pos={p} done={s[:p]} i={s[p]} future={s[p+1:]}")
print("CONCLUSION:", "FALSE - kernel needed" if best>0 else "gap==0 on all tested avoiding seqs -> hzero route viable")
