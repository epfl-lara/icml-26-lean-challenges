# hlower clean reduction test (q AT ROOT, correct for hlower):
#   pivotResetLowerPathSum(t,xs)  vs  splayPathSum(t,xs)  [both on same q-rooted t]
# If reset <= plain + C*N with bounded C, then hlower <= hupper + O(N): clean, no recursion.
import importlib.util, random
from itertools import product
from pathlib import Path
SPEC=importlib.util.spec_from_file_location("b", Path(".tmp_pair_certificate_search.py"))
base=importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(base)
spl,splay,N,E=base.path_len,base.splay,base.N,base.E
def keys(t): return [] if not t else keys(t[0])+[t[1]]+keys(t[2])
def reset_lower(t,q,xs):
    s=0
    for x in xs: s+=spl(t,x); t=splay(splay(t,x),q)
    return s
def plain(t,xs):
    s=0
    for x in xs: s+=spl(t,x); t=splay(t,x)
    return s
random.seed(0); worst={}
def upd(q,v):
    if q not in worst or v>worst[q]: worst[q]=v
# exhaustive small: t = node(L,q,R), q at root, accesses<q
for total in range(1,7):
    for q in range(1,total+1):
        for L in base.trees(0,q):
            for R in base.trees(q+1,total-q):
                t=base.N(L,q,R)
                for length in range(1,6):
                    for xs in product(range(q),repeat=length):
                        if not base.avoids231(list(xs)): continue
                        xs=list(xs)
                        upd(q,(reset_lower(t,q,xs)-plain(t,xs))/len(xs))
# structured large q (q at root)
import time;t0=time.time()
while time.time()-t0<40:
    q=random.choice([8,13,21,34,55,89])
    t=base.rooted_tree(q,random.choice([0,1,q]),random.choice(("left","balanced","right","random")))
    if t[1]!=q: continue   # ensure q at root
    for seq in (list(range(q)),list(reversed(range(q))),base.random_avoiding_seq(0,q,random.choice([8,16,32]))):
        xs=[v for v in seq if v<q]
        if len(xs)<1 or not base.avoids231(xs): continue
        upd(q,(reset_lower(t,q,xs)-plain(t,xs))/len(xs))
print(" q :  max (reset_lower - plain_splayPathSum)/len   [bounded => hlower <= hupper + O(N)]")
for q in sorted(worst): print(f"  {q:>3}: {worst[q]:+.2f}")
print("VERDICT:", "BOUNDED -> hlower <= hupper + O(N), clean" if max(worst.values())<6 else "grows -> recurses into core")
