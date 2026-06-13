# Decisive: does ANY constant A make the plain-splay weighted step's required C bounded,
# on the worst-case family (left spine + sequential/descending), as q grows?
import importlib.util
from pathlib import Path
SPEC=importlib.util.spec_from_file_location("b", Path(".tmp_pair_certificate_search.py"))
base=importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(base)
spl,splay,N,E=base.path_len,base.splay,base.N,base.E
def keys(t): return [] if not t else keys(t[0])+[t[1]]+keys(t[2])
def bb(t,xs,q):
    hull=set(base.search_path_keys(t,q))
    for x in xs: hull.update(base.search_path_keys(t,x))
    return len(xs)+len(hull)
def spine_incr(ks):  # foldl node t k empty over ks -> left spine, max at root
    t=E
    for k in ks: t=N(t,k,E)
    return t
def step_need(t,q,x,xs,A): return spl(t,x)+A*bb(splay(t,x),xs,q)-A*bb(t,[x]+xs,q)
# For each q, tree = left spine on 0..q (q at root). Try worst over single-step splits of
# sequential/descending/zigzag 231-avoiding sequences. Report min C needed per A.
As=[2.0,3.0,4.0,5.0,6.0]
print(" q :  minimal C needed for the weighted step, per A")
print("      " + "  ".join(f"A={int(a)}" for a in As))
for q in [6,8,10,13,16,20,26,34,44,55,70,89]:
    init=spine_incr(list(range(q+1)))           # keys 0..q, q at root, left spine
    assert keys(init)==list(range(q+1))
    cands=[]
    cands.append(list(range(q)))                # ascending 0..q-1
    cands.append(list(reversed(range(q))))      # descending
    cands.append([v for i in range(q) for v in ([i] if i%1==0 else [])])
    # all single accesses from the spine (worst single step over xs=[x])
    worst={A:-1e9 for A in As}
    # single-step: done has built some state; emulate by taking prefixes of a base seq
    for base_seq in cands:
        base_seq=[v for v in base_seq if v<q]
        if not base.avoids231(base_seq): continue
        t=init
        for pos in range(len(base_seq)):
            x=base_seq[pos]; xs=base_seq[pos+1:]
            for A in As:
                worst[A]=max(worst[A], step_need(t,q,x,xs,A))
            t=splay(t,x)
    print(f"  {q:>3}:  " + "  ".join(f"{worst[A]:+5.1f}" for A in As))
