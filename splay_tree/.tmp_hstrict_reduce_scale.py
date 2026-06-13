# Validate at scale: hstrict reduction constants, q ANYWHERE (random BSTs), incl small q + large tree.
import importlib.util, random
from pathlib import Path
SPEC=importlib.util.spec_from_file_location("b", Path(".tmp_pair_certificate_search.py"))
base=importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(base)
spl,splay,N,E=base.path_len,base.splay,base.N,base.E
def keys(t): return [] if not t else keys(t[0])+[t[1]]+keys(t[2])
def bst_insert(t,k):
    if not t: return N(E,k,E)
    l,x,r=t
    if k<x: return N(bst_insert(l,k),x,r)
    if x<k: return N(l,x,bst_insert(r,k))
    return t
def rand_bst(M):
    ks=list(range(M+1)); random.shuffle(ks); t=E
    for k in ks: t=bst_insert(t,k)
    return t
def pswf(t,q,xs):
    s=0
    for x in xs: s+=spl(t,x); t=splay(t,x)
    return s+spl(t,q)
def pathsum(t,xs):
    s=0
    for x in xs: s+=spl(t,x); t=splay(t,x)
    return s
random.seed(1)
import time;t0=time.time()
worst_pswf={}; worst_d1={}
def upd(d,k,v):
    if k not in d or v>d[k]: d[k]=v
while time.time()-t0<55:
    M=random.choice([10,20,40,80,160])
    t=rand_bst(M)
    root=t[1]
    # choose q anywhere (incl small q with large tree) ; ensure NOT root sometimes
    q=random.choice([1,2,M//4,M//2,3*M//4,M])
    if q<1 or q>M: continue
    tr=splay(t,q)
    for seq in (list(reversed(range(q))), list(range(q)), base.random_avoiding_seq(0,q,random.choice([8,16,32]))):
        xs=[v for v in seq if v<q]
        if len(xs)<1 or not base.avoids231(xs): continue
        bucket=(M, q)
        upd(worst_pswf,bucket,(pswf(t,q,xs)-pswf(tr,q,xs))/len(xs))
        upd(worst_d1,bucket,(pswf(t,q,xs)-pathsum(tr,xs))/len(xs))
print("(M,q) : (pswf(t)-pswf(splay(t,q)))/len ,  (pswf(t)-pathsum(splay(t,q)))/len")
for k in sorted(worst_pswf):
    print(f"  M={k[0]:>3} q={k[1]:>3}:  dPswf/len={worst_pswf[k]:+.2f}   d1/len={worst_d1[k]:+.2f}")
print()
print("max dPswf/len =", round(max(worst_pswf.values()),2), " | max d1/len =", round(max(worst_d1.values()),2))
