import importlib.util, itertools, random
spec=importlib.util.spec_from_file_location('e','.tmp_traverse_enum.py')
e=importlib.util.module_from_spec(spec); spec.loader.exec_module(e)
for kind,treefun in [('right',e.right_spine),('bal',lambda n:e.balanced(list(range(n))))]:
    print('TREE',kind)
    for n in range(1,8):
        maxc=-1; arg=None
        for seq in itertools.product(range(n), repeat=n):
            c,_=e.seqcost(treefun(n),seq)
            if c>maxc: maxc=c; arg=seq
        print(n,maxc,maxc/n,arg)
