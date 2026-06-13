import importlib.util
from pathlib import Path
SPEC=importlib.util.spec_from_file_location("b", Path(".tmp_pair_certificate_search.py"))
base=importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(base)
spl,splay,N,E=base.path_len,base.splay,base.N,base.E
spk=base.search_path_keys
def turn_nodes(t,x):
    L=set();R=set()
    while t:
        l,k,r=t
        if x<k: L.add(k);t=l
        elif k<x: R.add(k);t=r
        else: break
    return L,R
def hull_lr(t,xs,q):
    Ls=set();Rs=set()
    for x in list(xs)+[q]:
        l,r=turn_nodes(t,x);Ls|=l;Rs|=r
    return len(Ls),len(Rs)
def bb(t,xs,q):
    h=set(spk(t,q))
    for x in xs: h.update(spk(t,x))
    return len(xs)+len(h)
def spine(q):
    t=E
    for k in range(q+1): t=N(t,k,E)
    return t
q=24; a=2.0; b=2.0
t=spine(q); seq=list(range(q))
print(f"q={q}, Φ=a*bb+b*(L-R) NO clip, a={a} b={b}. Per-step C = cost+Φafter-Φbefore:")
worst=(-1e9,None)
for pos in range(len(seq)):
    x=seq[pos]; xs=seq[pos+1:]
    lb,rb=hull_lr(t,[x]+xs,q); before=a*bb(t,[x]+xs,q)+b*(lb-rb)
    t2=splay(t,x); la,ra=hull_lr(t2,xs,q); after=a*bb(t2,xs,q)+b*(la-ra)
    C=spl(t,x)+after-before
    if C>worst[0]: worst=(C,pos)
    if pos<6 or C>5:
        print(f"  step {pos:2d} access {x:2d}: cost={spl(t,x):2d}  (L-R)b={lb-rb:+3d} (L-R)a={la-ra:+3d}  C={C:+.0f}")
    t=t2
print("worst C:",worst)
