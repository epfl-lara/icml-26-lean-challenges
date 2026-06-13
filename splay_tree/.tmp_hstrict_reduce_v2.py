# CORRECT test (q genuinely anywhere, incl. not root):
# reduction hstrict <= hupper-on-splay(t,q) + O(N)?
#   D1 = pswf(t,q,xs) - pathsum(splay(t,q), xs)      (want D1 <= C*N)
#   also report final-access part pswf(t)-pathsum(t).
import importlib.util, random
from itertools import product
from pathlib import Path
SPEC=importlib.util.spec_from_file_location("b", Path(".tmp_pair_certificate_search.py"))
base=importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(base)
spl,splay,N,E=base.path_len,base.splay,base.N,base.E
def keys(t): return [] if not t else keys(t[0])+[t[1]]+keys(t[2])
def pswf(t,q,xs):
    s=0
    for x in xs: s+=spl(t,x); t=splay(t,x)
    return s+spl(t,q)
def pathsum(t,xs):
    s=0
    for x in xs: s+=spl(t,x); t=splay(t,x)
    return s
random.seed(0)
worstD1={}; worstFinal={}; rootcount={"qroot":0,"qnonroot":0}
def upd(d,q,v):
    if q not in d or v>d[q]: d[q]=v
# exhaustive: ALL BSTs on 0..M (q NOT forced to root), all q in 1..M-? , accesses<q
for M in range(2,7):                       # keys 0..M
    for t in base.trees(0,M+1):
        ks=keys(t)
        for q in range(1,M+1):             # q in tree, with keys both sides possible
            if q not in ks: continue
            if t[1]==q: rootcount["qroot"]+=1
            else: rootcount["qnonroot"]+=1
            tr=splay(t,q)
            for length in range(1,5):
                for xs in product(range(q),repeat=length):
                    if not base.avoids231(list(xs)): continue
                    xs=list(xs)
                    upd(worstD1,q,(pswf(t,q,xs)-pathsum(tr,xs))/len(xs))
                    upd(worstFinal,q,(pswf(t,q,xs)-pathsum(t,xs)))   # final access cost (absolute)
print(" trees tested with q at root vs not:", rootcount)
print(" q :  max D1/len (pswf(t) - pathsum(splay(t,q)))/len     max final-access cost")
for q in sorted(worstD1):
    print(f"  {q:>3}:   D1/len={worstD1[q]:+.2f}      final<= {worstFinal[q]:.0f}")
print("VERDICT:", "D1/len BOUNDED -> hstrict <= hupper + O(N) viable" if max(worstD1.values())<6 else "grows")
