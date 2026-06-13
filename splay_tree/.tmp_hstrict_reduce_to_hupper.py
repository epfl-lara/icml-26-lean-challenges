# Leveraged reduction test for hstrict:
#  Is  splayPathSumWithFinal(t,q,xs)  [plain on t, q ANYWHERE, all<q]
#      <=  splayPathSum(splay(t,q), xs) + final  +  C*(len)   ?
# RHS_base = plain process on q-ROOTED tree splay(t,q) (what hupper bounds).
# If (LHS - RHS_base)/len is bounded as q grows -> hstrict <= hupper + O(N): cheap reuse.
import importlib.util, random
from itertools import product
from pathlib import Path
SPEC=importlib.util.spec_from_file_location("b", Path(".tmp_pair_certificate_search.py"))
base=importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(base)
spl,splay,N,E=base.path_len,base.splay,base.N,base.E
def keys(t): return [] if not t else keys(t[0])+[t[1]]+keys(t[2])
def pswf(t,q,xs):           # splayPathSumWithFinal (plain)
    s=0.0
    for x in xs: s+=spl(t,x); t=splay(t,x)
    return s+spl(t,q)
def trees_containing_q(total,q):
    return [base.N(l,q,r) for l in base.trees(0,q) for r in base.trees(q+1,total-q)]
random.seed(0)
worst={}
def upd(q,v):
    if q not in worst or v>worst[q]: worst[q]=v
# exhaustive small (q anywhere)
for total in range(1,7):
    for q in range(1,total+1):
        for t in trees_containing_q(total,q):
            tr=splay(t,q)                       # q-rooted version
            for length in range(1,6):
                for xs in product(range(q),repeat=length):
                    if not base.avoids231(list(xs)): continue
                    xs=list(xs)
                    lhs=pswf(t,q,xs); rhs=pswf(tr,q,xs)
                    upd(q,(lhs-rhs)/len(xs))
# structured large q, q anywhere (use right_n>0 so q not at root)
import time;t0=time.time()
while time.time()-t0<40:
    q=random.choice([8,13,21,34,55])
    t=base.rooted_tree(q,random.choice([1,q//2,q]),random.choice(("left","balanced","right","random")))
    if q not in keys(t): continue
    tr=splay(t,q)
    for seq in (list(range(q)), list(reversed(range(q))), base.random_avoiding_seq(0,q,random.choice([8,13,21]))):
        xs=[v for v in seq if v<q]
        if len(xs)<1 or not base.avoids231(xs): continue
        lhs=pswf(t,q,xs); rhs=pswf(tr,q,xs)
        upd(q,(lhs-rhs)/len(xs))
print(" q :  max (hstrict_on_t - process_on_qrooted)/len   [bounded => hstrict <= hupper + O(N)]")
for q in sorted(worst): print(f"  {q:>3}: {worst[q]:+.2f}")
vals=list(worst.values())
print("VERDICT:", "BOUNDED -> cheap reuse of hupper viable" if max(vals)<8 else "grows -> no cheap reduction")
