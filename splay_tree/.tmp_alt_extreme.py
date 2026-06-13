import importlib.util
spec=importlib.util.spec_from_file_location('e','.tmp_traverse_enum.py')
e=importlib.util.module_from_spec(spec); spec.loader.exec_module(e)
for n in [10,20,50,100,200,500]:
  seq=[n-1 if i%2==0 else 0 for i in range(n)]
  print(n, e.avoids231(seq), e.seqcost(e.right_spine(n),seq)[0], e.seqcost(e.left_spine(n),seq)[0])
