# Test the Levy-Tarjan global potential on ACCESS-splaying (the repo's operation):
#   touched = keys accessed so far; sub-root = UNtouched node whose parent IS touched;
#   Φ = 2 * #(touched nodes that are ancestors of >=1 sub-root).  Φ0=Φn=0.
#   Per access x: cost=search_path_len; mark x touched; splay x; check cost+ΔΦ <= C.
import importlib.util, random
from pathlib import Path
SPEC=importlib.util.spec_from_file_location("b", Path(".tmp_pair_certificate_search.py"))
base=importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(base)
spl,splay,N,E=base.path_len,base.splay,base.N,base.E
def keys(t): return [] if not t else keys(t[0])+[t[1]]+keys(t[2])
def subtree_keys(t): return set(keys(t))
def phi(t, touched):
    # returns 2 * count of touched nodes that are ancestors of some sub-root.
    # sub-root: untouched node whose PARENT is touched.
    # first collect sub-root keys, then count touched nodes whose subtree contains a sub-root.
    subroots=set()
    def find_sub(t, parent_touched):
        if not t: return
        l,k,r=t
        is_t = k in touched
        if (not is_t) and parent_touched:
            subroots.add(k)
        find_sub(l, is_t); find_sub(r, is_t)
    find_sub(t, False)  # root's parent = none (untouched-ish); root has no parent so not a sub-root
    if not subroots: return 0
    cnt=0
    def count(t):
        # returns set of keys in subtree; increments cnt if node touched & subtree has a subroot
        if not t: return set()
        l,k,r=t
        sk=count(l) | {k} | count(r)
        if (k in touched) and (sk & subroots): cnt_inc(k)
        return sk
    found=[0]
    def count2(t):
        if not t: return False
        l,k,r=t
        lh=count2(l); rh=count2(r)
        has = lh or rh or (k in subroots)
        if (k in touched) and has: found[0]+=1
        return has
    count2(t)
    return 2*found[0]
def run(init, seq):
    t=init; touched=set(); worst=-1e9
    for x in seq:
        c=spl(t,x)
        p0=phi(t,touched)
        touched=touched | {x}
        t2=splay(t,x)
        p1=phi(t2,touched)
        worst=max(worst, c+p1-p0)
        t=t2
    return worst
def bst_insert(t,k):
    if not t: return N(E,k,E)
    l,x,r=t; return N(bst_insert(l,k),x,r) if k<x else (N(l,x,bst_insert(r,k)) if x<k else t)
def rand_bst(ks):
    ks=ks[:]; random.shuffle(ks); t=E
    for k in ks: t=bst_insert(t,k)
    return t
def spine_left(m):
    t=E
    for k in range(m): t=N(t,k,E)
    return t
random.seed(0)
print(" SEQUENTIAL access, Levy-Tarjan touched/sub-root Φ: worst per-step C by n")
for m in [8,16,32,64,128,256]:
    ks=list(range(m)); worst=-1e9
    for init in [spine_left(m)]+[rand_bst(ks) for _ in range(4)]:
        if keys(init)!=ks: continue
        worst=max(worst, run(init,list(range(m))))
    print(f"   n={m:>4}: C={worst:+.0f}")
print("\n GENERAL 231-avoiding access (random), worst C by n:")
for m in [16,32,64,128]:
    ks=list(range(m)); worst=-1e9
    for _ in range(20):
        init=rand_bst(ks)
        seq=[v for v in base.random_avoiding_seq(0,m,2*m) if v<m]
        if not base.avoids231(seq): continue
        worst=max(worst, run(init,seq))
    print(f"   n={m:>4}: C={worst:+.0f}")
