# DECISIVE: does the budget kernel / hlt_step hold when q is NOT at the root of init?
# (Needed for the tree-size recursion that avoids the 2x wall.)
# hlt_step slack needed:  actual.spl(x)+splay(actual,x).spl(q) + Psi(after) - [reset-pair + Psi(before)]
# with Psi = 3*bb(reset,future,q) + 1*gapPot + 2*qpath(actual).  q ANYWHERE in init.
import importlib.util, random
from itertools import product
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
def bb(t,xs,q):
    h=set(base.search_path_keys(t,q))
    for x in xs: h.update(base.search_path_keys(t,x))
    return len(xs)+len(h)
def first_lower_pair_gap(init,q,done,future):
    z=next((v for v in future if v<q),None)
    if z is None: return 0.0
    a=sa(init,done); r=ra(init,done,q)
    return float(max(0, spl(a,z)+spl(splay(a,z),q)-spl(a,q)-spl(r,z)-spl(splay(r,z),q)))
def psi(init,q,done,future,A,G,H):
    a=sa(init,done); r=ra(init,done,q)
    return A*bb(r,future,q)+G*first_lower_pair_gap(init,q,done,future)+H*spl(a,q)
def hlt_need(init,q,done,x_idx_val,future,A,G,H):
    # done, future are value-lists; x is a lower value
    a=sa(init,done); r=ra(init,done,q)
    lhs=spl(a,x_idx_val)+spl(splay(a,x_idx_val),q)+psi(init,q,done+[x_idx_val],future,A,G,H)
    rhs=spl(a,q)+spl(r,x_idx_val)+spl(splay(r,x_idx_val),q)+psi(init,q,done,[x_idx_val]+future,A,G,H)
    return lhs-rhs
random.seed(0)
A,G,H=3.0,1.0,2.0
worst_root={}; worst_nonroot={}
def upd(d,q,v):
    if q not in d or v>d[q]: d[q]=v
# exhaustive small: ALL BSTs on 0..M (q anywhere), accesses<q, 231-avoiding
for M in range(2,7):
    for t in base.trees(0,M+1):
        ks=keys(t); root=t[1]
        for q in range(1,M+1):
            if q not in ks: continue
            for length in range(1,5):
                for seq in product(range(q),repeat=length):
                    if not base.avoids231(list(seq)): continue
                    seq=list(seq)
                    for pos in range(length):
                        v=hlt_need(t,q,seq[:pos],seq[pos],seq[pos+1:],A,G,H)
                        if root==q: upd(worst_root,M,v)
                        else: upd(worst_nonroot,M,v)
print("hlt_step worst slack needed (A,G,H=3,1,2), q AT ROOT vs q NOT AT ROOT:")
print(" M :  q-at-root     q-NOT-at-root")
for M in sorted(set(worst_root)|set(worst_nonroot)):
    print(f"  {M}:  {worst_root.get(M,float('nan')):+.1f}        {worst_nonroot.get(M,float('nan')):+.1f}")
print("\nq-NOT-at-root max:", round(max(worst_nonroot.values()),1) if worst_nonroot else "n/a",
      " (D=3 available; bounded & <=3 => kernel works q-anywhere)")
