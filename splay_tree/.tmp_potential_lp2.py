import importlib.util, random
from pathlib import Path
SPEC=importlib.util.spec_from_file_location("b", Path(".tmp_pair_certificate_search.py"))
base=importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(base)
spl,splay,N,E=base.path_len,base.splay,base.N,base.E
def lspine(t):
    d=0
    while t and t[0]: d+=1; t=t[0]
    return d
def rspine(t):
    d=0
    while t and t[2]: d+=1; t=t[2]
    return d
FEATS=["hasL","hasR","two","L_hasR","R_hasL",
       "leftspine","rightspine",          # root spines
       "staircase_L","staircase_R",       # sum over R-spine of lspine(left), sum over L-spine of rspine(right)
       "sum_lspine_Rchildren"]            # sum over right-children v of lspine(v.left)
def feats(t):
    f=dict.fromkeys(FEATS,0)
    def rec(t,side):
        if not t: return
        l,k,r=t; hasL=1 if l else 0; hasR=1 if r else 0
        f["hasL"]+=hasL; f["hasR"]+=hasR; f["two"]+=hasL*hasR
        if side==1: f["L_hasR"]+=hasR
        if side==2:
            f["R_hasL"]+=hasL
            f["sum_lspine_Rchildren"]+=lspine(l)
        rec(l,1); rec(r,2)
    rec(t,0)
    f["leftspine"]=lspine(t); f["rightspine"]=rspine(t)
    # staircase_L: walk right spine, sum lspine(left subtree) at each
    a=t
    while a:
        f["staircase_L"]+=lspine(a[0]); a=a[2]
    a=t
    while a:
        f["staircase_R"]+=rspine(a[2]); a=a[0]
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
F=len(FEATS)
def make_rows(ms,nrand):
    rows=[]
    for m in ms:
        ks=list(range(m))
        for init in [spine_left(m)]+[rand_bst(ks) for _ in range(nrand)]:
            if keys(init)!=ks: continue
            for seq in [list(range(m)),list(reversed(range(m)))]:
                cur=init
                for x in seq:
                    c=spl(cur,x); aft=splay(cur,x)
                    fb=feats(cur); fa=feats(aft)
                    rows.append((c,[fa[i]-fb[i] for i in range(F)]))
                    cur=aft
    return rows
train=make_rows([8,16,32,48,64],3)
def obj(rows,c): return max(cost+sum(c[i]*df[i] for i in range(F)) for cost,df in rows)
def tern(rows,c,i):
    lo,hi=0.0,300.0
    for _ in range(50):
        m1=lo+(hi-lo)/3; m2=hi-(hi-lo)/3
        c[i]=m1; v1=obj(rows,c); c[i]=m2; v2=obj(rows,c)
        if v1<v2: hi=m2
        else: lo=m1
    c[i]=(lo+hi)/2; return obj(rows,c)
c=[0.0]*F; best=obj(train,c)
for it in range(60):
    for i in range(F): tern(train,c,i)
    v=obj(train,c)
    if abs(best-v)<1e-4 and it>5: break
    best=v
print(f"train(m<=64): best per-step C = {best:.2f}")
print("coefficients:")
for nm,co in zip(FEATS,c):
    if abs(co)>1e-3: print(f"   {nm:20s}: {co:+.3f}")
# HELD-OUT scaling test with the found c
print("\nHeld-out scaling (same Φ, larger m): worst per-step C")
for m in [64,128,256,512]:
    rows=make_rows([m],2)
    print(f"   m={m:>4}: C={obj(rows,c):+.1f}")
