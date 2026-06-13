import importlib.util
from pathlib import Path
SPEC=importlib.util.spec_from_file_location("b", Path(".tmp_pair_certificate_search.py"))
base=importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(base)
spl,splay,N,E=base.path_len,base.splay,base.N,base.E
spk=base.search_path_keys
def keys(t): return [] if not t else keys(t[0])+[t[1]]+keys(t[2])
def turn_nodes(t,x):
    L=set(); R=set()
    while t:
        l,k,r=t
        if x<k: L.add(k); t=l
        elif k<x: R.add(k); t=r
        else: break
    return L,R
def hull_lr(t,xs,q):
    Ls=set(); Rs=set()
    for x in list(xs)+[q]:
        l,r=turn_nodes(t,x); Ls|=l; Rs|=r
    return len(Ls),len(Rs)
def bb(t,xs,q):
    h=set(spk(t,q))
    for x in xs: h.update(spk(t,x))
    return len(xs)+len(h)
def spine(q):
    t=E
    for k in range(q+1): t=N(t,k,E)
    return t
print("Spine min-access: does (hullLeft - hullRight) drop ~full cost?")
for q in [6,10,16,24,40]:
    t=spine(q); x=0; xs=list(range(1,q))
    lb,rb=hull_lr(t,[x]+xs,q); la,ra=hull_lr(splay(t,x),xs,q)
    print(f" q={q:3d} cost={spl(t,x):3d}  (L-R) before={lb-rb:+4d} after={la-ra:+4d} Δ={(la-ra)-(lb-rb):+4d}")
# per-step worst C over sequential run, Φ = a*bb + b*max(0, hullLeft - hullRight)
def run_need(q,a,b):
    t=spine(q); seq=list(range(q)); worst=-1e9
    for pos in range(len(seq)):
        x=seq[pos]; xs=seq[pos+1:]
        lb,rb=hull_lr(t,[x]+xs,q); 
        before=a*bb(t,[x]+xs,q)+b*max(0,lb-rb)
        t2=splay(t,x); la,ra=hull_lr(t2,xs,q)
        after=a*bb(t2,xs,q)+b*max(0,la-ra)
        worst=max(worst,spl(t,x)+after-before); t=t2
    return worst
print("\nPer-step worst C, Φ=a*bb + b*max(0,hullLeft-hullRight), sequential on spine:")
for (a,b) in [(1,0),(0,1),(1,1),(2,1),(1,2),(2,2),(0,2)]:
    print(f"  a={a} b={b}: "+", ".join(f"q{q}:{run_need(q,a,b):+.0f}" for q in [8,16,32,64,128]))
