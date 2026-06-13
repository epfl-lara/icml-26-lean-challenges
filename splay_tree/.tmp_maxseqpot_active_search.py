# B3: per-step bound for Φ = maxSeqPot + δ*activeBudget (line 31719 reduction).
#   cost + Φ(after,future) <= C + Φ(before, i::future)
# activeBudget(t,future)=len(future)+|union of search_path_keys(t,k) for k in future|.
import importlib.util, random
from pathlib import Path
SPEC=importlib.util.spec_from_file_location("b", Path(".tmp_pair_certificate_search.py"))
base=importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(base)
spl,splay,N,E=base.path_len,base.splay,base.N,base.E
spk=base.search_path_keys
def left_edges(t):
    if not t: return 0
    l,k,r=t; return (1 if l else 0)+left_edges(l)+left_edges(r)
def right_edges(t):
    if not t: return 0
    l,k,r=t; return (1 if r else 0)+right_edges(l)+right_edges(r)
def maxseqpot(t):
    L=left_edges(t); R=right_edges(t); return max(10*L+5*R,10*R+5*L)
def activebudget(t,future):
    h=set()
    for k in future: h.update(spk(t,k))
    return len(future)+len(h)
def keys(t): return [] if not t else keys(t[0])+[t[1]]+keys(t[2])
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
def balanced(lo,hi):
    if lo>hi: return E
    mid=(lo+hi)//2; return N(balanced(lo,mid-1),mid,balanced(mid+1,hi))
random.seed(0)
DELTAS=[1.0,2.0,4.0,8.0]
worst={d:{} for d in DELTAS}
def upd(d,m,v,info):
    if m not in worst[d] or v>worst[d][m][0]: worst[d][m]=(v,info)
import time;t0=time.time()
for m in [4,8,16,32,64,128,256]:
    ks=list(range(m))
    inits=[spine_left(m),balanced(0,m-1)]+[rand_bst(ks) for _ in range(5)]
    seqs=[list(range(m)),list(reversed(range(m)))]+[base.random_avoiding_seq(0,m,random.choice([m,2*m])) for _ in range(6)]
    for init in inits:
        if keys(init)!=ks: continue
        for seq in seqs:
            seq=[v for v in seq if 0<=v<m]
            if not seq or not base.avoids231(seq): continue
            cur=init
            for pos in range(len(seq)):
                x=seq[pos]; fut=seq[pos+1:]
                aft=splay(cur,x)
                base_need=spl(cur,x)+maxseqpot(aft)-maxseqpot(cur)
                dab=activebudget(cur,seq[pos:])-activebudget(aft,fut)  # before - after
                for d in DELTAS:
                    upd(d,m,base_need-d*dab,f"x={x} pos{pos} seqhd={seq[:3]}")
                cur=aft
    if time.time()-t0>140: break
for d in DELTAS:
    print(f"== Φ=maxSeqPot+{d:.0f}*activeBudget : worst-case C by n ==")
    for m in sorted(worst[d]):
        v,info=worst[d][m]; print(f"   n={m:>4}: C={v:+.0f}  @ {info}")
    vals=[worst[d][m][0] for m in sorted(worst[d])]
    print(f"   -> {'BOUNDED' if vals[-1]<40 else 'grows'} (last={vals[-1]:+.0f})\n")
