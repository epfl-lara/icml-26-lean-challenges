import importlib.util
from functools import lru_cache
spec=importlib.util.spec_from_file_location('e','.tmp_traverse_enum.py')
e=importlib.util.module_from_spec(spec); spec.loader.exec_module(e)

@lru_cache(None)
def av231_tuple(vals):
    vals=list(vals)
    if not vals: return [()]
    m=vals[-1]; rest=vals[:-1]
    out=[]
    for k in range(len(rest)+1):
        left=tuple(rest[:k]); right=tuple(rest[k:])
        for L in av231_tuple(left):
            for R in av231_tuple(right):
                out.append(L+(m,)+R)
    return out

for n in range(1,12):
    perms=av231_tuple(tuple(range(n)))
    maxc=0; arg=None
    for p in perms:
        c,_=e.seqcost(e.right_spine(n),p)
        if c>maxc: maxc=c; arg=p
    print(n,len(perms),maxc,maxc/n,arg)
