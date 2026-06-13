# Does actualResetLowerPairGapAt(done++[i], j) > 2 ever hold with:
#   Y j < Y i (descent), Y i<q, all<q, 231-avoiding, and Codex's barrier:
#   forall a in done: Y a <= Y j  OR  Y i <= Y a
import importlib.util, random
from pathlib import Path
SPEC=importlib.util.spec_from_file_location("b", Path(".tmp_pair_certificate_search.py"))
base=importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(base)
spl,splay,N,E=base.path_len,base.splay,base.N,base.E
def keys(t): return [] if not t else keys(t[0])+[t[1]]+keys(t[2])
def sa(t,seq):
    for x in seq: t=splay(t,x)
    return t
def ra(t,seq,q):
    for x in seq:
        if x<q: t=splay(splay(t,x),q)
    return t
def gapAt(init,q,donei,j):   # actualResetLowerPairGapAt at state donei, key j
    a=sa(init,donei); r=ra(init,donei,q)
    return max(0, spl(a,j)+spl(splay(a,j),q)-spl(a,q)-spl(r,j)-spl(splay(r,j),q))
random.seed(0); worst=0; wit=None
import time;t0=time.time()
while time.time()-t0<55:
    q=random.choice([8,13,21,34,55])
    init=base.rooted_tree(q,0,random.choice(("left","balanced","right","random")))
    if keys(init)!=list(range(q+1)): continue
    s=[v for v in base.random_avoiding_seq(0,q,random.choice([q,2*q,3*q])) if v<q]
    if len(s)<2 or not base.avoids231(s): continue
    for pos in range(len(s)-1):
        done=s[:pos]; i=s[pos]; j=s[pos+1]
        if not (j<i): continue            # descent only
        # barrier on done:
        if not all(a<=j or i<=a for a in done): continue
        g=gapAt(init,q,done+[i],j)
        if g>worst: worst=g; wit=(q,s,pos,done,i,j,g)
print("max actualResetLowerPairGapAt over descent+barrier cases:", worst)
if wit and worst>2:
    q,s,pos,done,i,j,g=wit
    print(f"  >2 WITNESS (refutes gap<=2): q={q} done={done} i={i} j={j} gap={g}")
    print(f"  seq={s}")
print("Codex hdesc_gap_barrier (gap<=2):", "FALSE - constant must be >=%d"%worst if worst>2 else "holds (<=2) on all tested")
