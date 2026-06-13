# Is hstrict true with a small constant K?  splayPathSumWithFinal / boundaryBudget bounded?
# Plain splaying of all-below-q 231-avoiding accesses + final q-access.
import importlib.util, random
from itertools import product
from pathlib import Path
SPEC=importlib.util.spec_from_file_location("b", Path(".tmp_pair_certificate_search.py"))
base=importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(base)
spl,splay,N,E=base.path_len,base.splay,base.N,base.E
def keys(t): return [] if not t else keys(t[0])+[t[1]]+keys(t[2])
def pathsum_with_final(t,q,xs):
    s=0.0
    for x in xs:
        s+=spl(t,x); t=splay(t,x)
    return s+spl(t,q)               # final access to q
def bb(t,xs,q):
    hull=set(base.search_path_keys(t,q))
    for x in xs: hull.update(base.search_path_keys(t,x))
    return len(xs)+len(hull)
random.seed(0)
worst={}
# exhaustive tiny q (q anywhere in tree, all xs<q)
for q in range(1,6):
    for total in range(q+1, q+4):     # trees containing q, with some keys > q too
        for L in base.trees(0,q):
            for R in base.trees(q+1, total-q-1):
                t0=N(L,q,R)
                for length in range(1,6):
                    for xs in product(range(q),repeat=length):
                        if not base.avoids231(list(xs)): continue
                        xs=list(xs)
                        r=pathsum_with_final(t0,q,xs)/bb(t0,xs,q)
                        if r>worst.get(q,0): worst[q]=r
# structured large q
import time;t0=time.time()
while time.time()-t0<40:
    q=random.choice([8,13,21,34,55,89])
    init=base.rooted_tree(q,0,random.choice(("left","balanced","right","random")))  # keys 0..q
    if keys(init)!=list(range(q+1)): continue
    xs=[v for v in base.random_avoiding_seq(0,q,random.choice([q,2*q,3*q])) if v<q]
    if len(xs)<1 or not base.avoids231(xs): continue
    r=pathsum_with_final(init,q,xs)/bb(init,xs,q)
    if r>worst.get(q,0): worst[q]=r
    # also descending and sequential
    for xs in (list(reversed(range(q))), list(range(q))):
        if base.avoids231(xs):
            r=pathsum_with_final(init,q,xs)/bb(init,xs,q)
            if r>worst.get(q,0): worst[q]=r
print(" q : max(splayPathSumWithFinal / boundaryBudget)")
for q in sorted(worst): print(f"  {q:>3}: {worst[q]:.3f}")
print("VERDICT:", "hstrict TRUE with small K (bounded ratio)" if max(worst.values())<6 else "ratio grows - investigate")
