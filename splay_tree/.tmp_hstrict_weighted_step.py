# hstrict per-step kernel (PLAIN splay, no reset):
#   search_path(t,x) + A*bb(splay(t,x), xs, q)  <=  C + A*bb(t, x::xs, q)
# for t a BST CONTAINING q (q anywhere), x<q, all of (x::xs)<q, 231-avoiding.
# Telescopes to hstrict with Ks = A + C.  Q: does minimal C stay constant as q grows?
import importlib.util, random
from itertools import product
from pathlib import Path
SPEC=importlib.util.spec_from_file_location("b", Path(".tmp_pair_certificate_search.py"))
base=importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(base)
spl,splay,N,E=base.path_len,base.splay,base.N,base.E
def keys(t): return [] if not t else keys(t[0])+[t[1]]+keys(t[2])
def bb(t,xs,q):
    hull=set(base.search_path_keys(t,q))
    for x in xs: hull.update(base.search_path_keys(t,x))
    return len(xs)+len(hull)
def need(t,q,x,xs,A):
    return spl(t,x) + A*bb(splay(t,x),xs,q) - A*bb(t,[x]+xs,q)
def trees_containing_q(total,q):
    # all BSTs on {0..total} that contain q (q in 0..total)
    out=[]
    for l in base.trees(0,q):
        for r in base.trees(q+1,total-q):
            out.append(base.N(l,q,r))
    return out
random.seed(0)
As=[1.0,2.0,3.0]
best={A:{} for A in As}
def upd(A,q,v):
    if q not in best[A] or v>best[A][q]: best[A][q]=v
# exhaustive small: total nodes up to 6, q in middle, accesses<q
for total in range(1,7):
    for q in range(1,total+1):
        for t in trees_containing_q(total,q):
            for length in range(1,6):
                for xs in product(range(q),repeat=length):
                    if not base.avoids231(list(xs)): continue
                    xs=list(xs); x=xs[0]; rest=xs[1:]
                    for A in As: upd(A,q,need(t,q,x,rest,A))
import time;t0=time.time()
while time.time()-t0<45:
    q=random.choice([8,13,21,34,55,89])
    # tree on 0..(q+r) with q somewhere; use rooted_tree variants
    init=base.rooted_tree(q,random.choice([0,1,q//2]),random.choice(("left","balanced","right","random")))
    ks=keys(init)
    if q not in ks: continue
    for seq in ([0]*8, list(range(min(8,q))), list(reversed(range(min(8,q)))),
                base.random_avoiding_seq(0,q,random.choice([8,13,21]))):
        xs=[v for v in seq if v<q]
        if len(xs)<1 or not base.avoids231(xs): continue
        x=xs[0]; rest=xs[1:]
        for A in As: upd(A,q,need(init,q,x,rest,A))
for A in As:
    print(f"== plain-splay weighted step A={A}: minimal C by q ==")
    for q in sorted(best[A]): print(f"   q={q:>3}: C={best[A][q]:+.1f}")
