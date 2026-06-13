# Diagnostic: on the spine killer (access deep min), which Lean-definable features
# DROP by ~depth (to pay for the access cost ~depth)? bb drops only O(1) -> need better.
import importlib.util
from pathlib import Path
SPEC=importlib.util.spec_from_file_location("b", Path(".tmp_pair_certificate_search.py"))
base=importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(base)
spl,splay,N,E=base.path_len,base.splay,base.N,base.E
spk=base.search_path_keys
def keys(t): return [] if not t else keys(t[0])+[t[1]]+keys(t[2])
def leftdepth(t,x):           # number of left-turns on search path to x
    d=0
    while t:
        l,k,r=t
        if x<k: d+=1; t=l
        elif k<x: t=r
        else: break
    return d
def hull(t,xs,q):
    h=set(spk(t,q))
    for x in xs: h.update(spk(t,x))
    return h
def feats(t,xs,q):
    distinct=set(xs)
    return {
        "bb": len(xs)+len(hull(t,xs,q)),
        "sumdepth": sum(spl(t,x) for x in distinct),
        "sumleft": sum(leftdepth(t,x) for x in distinct),
        "nfut": len(distinct),
        "activehull": len(set().union(*[set(spk(t,x)) for x in xs]) if xs else set()),
        "qpath": spl(t,q),
    }
def spine(q):  # left spine keys 0..q, q at root
    t=E
    for k in range(q+1): t=N(t,k,E)
    return t
print("Spine 0..q, access the deep MIN (x=0). cost=search_path. Feature BEFORE/AFTER/Δ (xs=future).")
for q in [6,10,16,24]:
    t=spine(q); x=0
    xs=list(range(1,q))          # future = 1..q-1 (ascending, 231-avoiding)
    cost=spl(t,x)
    fb=feats(t,xs+[x] if False else xs,q)   # before: remaining includes... use x::xs
    fb=feats(t,[x]+xs,q); fa=feats(splay(t,x),xs,q)
    print(f"\nq={q}  cost(access min)={cost}")
    for k in fb:
        print(f"   {k:10s} before={fb[k]:4d} after={fa[k]:4d}  Δ={fa[k]-fb[k]:+4d}")
