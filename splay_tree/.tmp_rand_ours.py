import importlib.util, random
spec=importlib.util.spec_from_file_location('e','.tmp_traverse_enum.py')
e=importlib.util.module_from_spec(spec); spec.loader.exec_module(e)
for n in [10,20,50,100,200]:
    maxc=0; arg=None
    for _ in range(1000):
        seq=[random.randrange(n) for _ in range(n)]
        c,_=e.seqcost(e.right_spine(n),seq)
        if c>maxc: maxc=c; arg=seq
    print(n,maxc,maxc/n)
