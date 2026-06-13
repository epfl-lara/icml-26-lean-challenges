import importlib.util, random
spec=importlib.util.spec_from_file_location('s','.tmp_alt_sim.py')
s=importlib.util.module_from_spec(spec)
spec.loader.exec_module(s)
for n in [10,20,50,100]:
    maxc=0; arg=None
    for _ in range(2000):
        seq=[random.randrange(n) for _ in range(n)]
        c,_=s.seq_cost(s.right_spine(n),seq)
        if c>maxc:
            maxc=c; arg=seq
    print('n',n,'max',maxc,'ratio',maxc/n)
