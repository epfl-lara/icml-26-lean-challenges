# B1 decision gate: does the per-step bound
#   search_path_len(cur,Xi) + maxSeqPot(splay cur Xi) <= C + maxSeqPot(cur)
# hold over genuine 231-avoiding reachable states, with C bounded (flat in n)?
# maxSeqPot t = max(10L+5R, 10R+5L) = 5(n-1)+5*max(L,R), L=leftEdges,R=rightEdges.
import importlib.util, random
from pathlib import Path
SPEC=importlib.util.spec_from_file_location("b", Path(".tmp_pair_certificate_search.py"))
base=importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(base)
spl,splay,N,E=base.path_len,base.splay,base.N,base.E

def left_edges(t):
    if not t: return 0
    l,k,r=t
    return (1 if l else 0)+left_edges(l)+left_edges(r)
def right_edges(t):
    if not t: return 0
    l,k,r=t
    return (1 if r else 0)+right_edges(l)+right_edges(r)
def maxseqpot(t):
    L=left_edges(t); R=right_edges(t)
    return max(10*L+5*R, 10*R+5*L)
def keys(t): return [] if not t else keys(t[0])+[t[1]]+keys(t[2])
def bst_insert(t,k):
    if not t: return N(E,k,E)
    l,x,r=t
    return N(bst_insert(l,k),x,r) if k<x else (N(l,x,bst_insert(r,k)) if x<k else t)
def rand_bst(ks):
    ks=ks[:]; random.shuffle(ks); t=E
    for k in ks: t=bst_insert(t,k)
    return t
def spine_left(m):
    t=E
    for k in range(m): t=N(t,k,E)   # left spine 0..m-1, max at root
    return t
def step_need(cur,x):
    return spl(cur,x)+maxseqpot(splay(cur,x))-maxseqpot(cur)

def run_seq(init,seq):
    cur=init; worst=-1e9; witx=None
    for x in seq:
        nd=step_need(cur,x)
        if nd>worst: worst=nd; witx=x
        cur=splay(cur,x)
    return worst,witx

random.seed(0)
worst_by_m={}
def upd(m,v,info):
    if m not in worst_by_m or v>worst_by_m[m][0]: worst_by_m[m]=(v,info)

import time; t0=time.time()
# exhaustive-ish small m + adversarial families; random large m
for m in [4,8,12,16,24,32,48,64,96,128,192,256]:
    ks=list(range(m))
    inits=[spine_left(m)]
    for _ in range(6): inits.append(rand_bst(ks))
    # balanced
    def balanced(lo,hi):
        if lo>hi: return E
        mid=(lo+hi)//2; return N(balanced(lo,mid-1),mid,balanced(mid+1,hi))
    inits.append(balanced(0,m-1))
    seqs=[list(range(m)),                       # sorted (sequential access)
          list(reversed(range(m)))]             # reverse sorted
    for _ in range(8):
        seqs.append(base.random_avoiding_seq(0,m,random.choice([m,2*m])))
    for init in inits:
        if keys(init)!=ks: continue
        for seq in seqs:
            seq=[v for v in seq if 0<=v<m]
            if not seq or not base.avoids231(seq): continue
            w,wx=run_seq(init,seq)
            upd(m,w,f"len{len(seq)} seq[:4]={seq[:4]} x*={wx}")
    if time.time()-t0>120: break

print(" n :  worst-case required C (per-step maxSeqPot bound)")
for m in sorted(worst_by_m):
    v,info=worst_by_m[m]
    print(f"  {m:>4}:  C={v:+.0f}   @ {info}")
vals=[worst_by_m[m][0] for m in worst_by_m]
print("\nVERDICT:", "BOUNDED -> Route B viable, go to B2" if max(vals)<40 and (len(vals)<3 or vals[-1]-vals[len(vals)//2]<8) else "GROWS with n -> need B3/activeBudget")
