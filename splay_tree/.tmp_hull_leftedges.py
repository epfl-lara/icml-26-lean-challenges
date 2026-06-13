import importlib.util
from pathlib import Path
SPEC=importlib.util.spec_from_file_location("b", Path(".tmp_pair_certificate_search.py"))
base=importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(base)
spl,splay,N,E=base.path_len,base.splay,base.N,base.E
spk=base.search_path_keys
def keys(t): return [] if not t else keys(t[0])+[t[1]]+keys(t[2])
def left_turn_nodes(t,x):
    """parent keys k where the search path to x turns LEFT (x<k)."""
    s=set()
    while t:
        l,k,r=t
        if x<k: s.add(k); t=l
        elif k<x: t=r
        else: break
    return s
def hull_left_edges(t,xs,q):   # distinct nodes where SOME path (to xs or q) turns left
    s=set()
    for x in list(xs)+[q]:
        s|=left_turn_nodes(t,x)
    return len(s)
def bb(t,xs,q):
    h=set(spk(t,q))
    for x in xs: h.update(spk(t,x))
    return len(xs)+len(h)
def spine(q):
    t=E
    for k in range(q+1): t=N(t,k,E)
    return t
print("Spine, access deep MIN. hullLeftEdges vs bb (want: hLE drops ~depth, hLE<=bb).")
for q in [6,10,16,24,40]:
    t=spine(q); x=0; xs=list(range(1,q))
    cost=spl(t,x)
    hb=hull_left_edges(t,[x]+xs,q); ha=hull_left_edges(splay(t,x),xs,q)
    bbb=bb(t,[x]+xs,q)
    print(f" q={q:3d} cost={cost:3d}  hullLeftEdges before={hb:3d} after={ha:3d} Δ={ha-hb:+4d}   (bb_before={bbb}, hLE/bb={hb/bbb:.2f})")
# Also test the per-step on full sequential run with Φ = a*bb + b*hullLeftEdges
def run_need(q, a, b):
    """worst per-step C for Φ=a*bb+b*hullLeftEdges over sequential access 0..q-1 on spine."""
    t=spine(q); seq=list(range(q)); worst=-1e9
    for pos in range(len(seq)):
        x=seq[pos]; xs=seq[pos+1:]
        before=a*bb(t,[x]+xs,q)+b*hull_left_edges(t,[x]+xs,q)
        t2=splay(t,x)
        after=a*bb(t2,xs,q)+b*hull_left_edges(t2,xs,q)
        worst=max(worst, spl(t,x)+after-before)
        t=t2
    return worst
print("\nPer-step worst C for Φ=a*bb+b*hullLeftEdges, sequential on spine:")
for (a,b) in [(1,0),(0,1),(1,1),(2,1),(1,2),(0,2),(2,2)]:
    print(f"  a={a} b={b}: maxC over q in [8,16,32,64] = "+
          ", ".join(f"q{q}:{run_need(q,a,b):+.0f}" for q in [8,16,32,64]))
