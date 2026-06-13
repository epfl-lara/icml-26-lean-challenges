import importlib.util, random
spec=importlib.util.spec_from_file_location('e','.tmp_traverse_enum.py')
e=importlib.util.module_from_spec(spec); spec.loader.exec_module(e)

def gen_231(vals):
    # vals sorted list; choose split: left smaller, right larger, max at middle? For max M, left values must all < right values.
    m=vals[-1]
    rest=vals[:-1]
    if not rest: return [m]
    k=random.randrange(len(rest)+1) # left size, smallest k before max
    left=rest[:k]
    right=rest[k:]
    return gen_231(left)+[m]+gen_231(right) if left and right else (gen_231(left)+[m] if left else [m]+gen_231(right) if right else [m])

# verify generation
for n in [5,10]:
  for _ in range(1000):
    p=gen_231(list(range(n)))
    if not e.avoids231(p): print('bad',p); raise SystemExit
print('gen ok')
for n in [10,20,50,100,200,500,1000]:
    maxc=0; arg=None
    for _ in range(5000):
        seq=gen_231(list(range(n)))
        c,_=e.seqcost(e.right_spine(n),seq)
        if c>maxc: maxc=c; arg=seq
    print(n,maxc,maxc/n)
