# Discover per-step potential by coordinate-descent minimax (no numpy).
# Features = sums of node-local indicators (Lean-definable) + spine lengths.
import importlib.util, random
from pathlib import Path
SPEC=importlib.util.spec_from_file_location("b", Path(".tmp_pair_certificate_search.py"))
base=importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(base)
spl,splay,N,E=base.path_len,base.splay,base.N,base.E
FEATS=["hasL","hasR","L_hasR","R_hasL","L_hasL","R_hasR","two","leftspine","rightspine"]
def feats(t):
    f=dict.fromkeys(FEATS,0)
    def rec(t,side):
        if not t: return
        l,k,r=t; hasL=1 if l else 0; hasR=1 if r else 0
        f["hasL"]+=hasL; f["hasR"]+=hasR; f["two"]+=hasL*hasR
        if side==1: f["L_hasR"]+=hasR; f["L_hasL"]+=hasL
        if side==2: f["R_hasL"]+=hasL; f["R_hasR"]+=hasR
        rec(l,1); rec(r,2)
    rec(t,0)
    a=t; d=0
    while a and a[0]: d+=1; a=a[0]
    f["leftspine"]=d
    a=t; d=0
    while a and a[2]: d+=1; a=a[2]
    f["rightspine"]=d
    return [f[k] for k in FEATS]
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
random.seed(0)
rows=[]
def collect(init,seq):
    cur=init
    for x in seq:
        c=spl(cur,x); aft=splay(cur,x)
        fb=feats(cur); fa=feats(aft)
        rows.append((c,[fa[i]-fb[i] for i in range(len(FEATS))]))
        cur=aft
for m in [8,16,32,48,64]:
    ks=list(range(m))
    for init in [spine_left(m)]+[rand_bst(ks) for _ in range(4)]:
        if keys(init)!=ks: continue
        collect(init,list(range(m))); collect(init,list(reversed(range(m))))
F=len(FEATS)
def obj(c): return max(cost+sum(c[i]*df[i] for i in range(F)) for cost,df in rows)
def ternary_min_coord(c,i):
    lo,hi=0.0,200.0
    for _ in range(60):
        m1=lo+(hi-lo)/3; m2=hi-(hi-lo)/3
        c[i]=m1; v1=obj(c); c[i]=m2; v2=obj(c)
        if v1<v2: hi=m2
        else: lo=m1
    c[i]=(lo+hi)/2; return obj(c)
c=[0.0]*F
print(f"{len(rows)} sequential/reverse steps, {F} features. Coordinate-descent minimax:")
best=obj(c)
for it in range(40):
    for i in range(F): ternary_min_coord(c,i)
    v=obj(c)
    if abs(best-v)<1e-4 and it>3: break
    best=v
print(f"\nbest max per-step C = {best:.2f}")
print("coefficients:")
for name,coef in zip(FEATS,c):
    if abs(coef)>1e-4: print(f"   {name:12s}: {coef:+.3f}")
print("\nVERDICT:", "FOUND a per-step potential for sequential!" if best<10 else "no constant per-step potential in this feature space")
