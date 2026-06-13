exec(open('.tmp_splay.py').read())

def min_key(t):
    while isinstance(t.l,N): t=t.l
    return t.k
def delmin(t): return splay(t,min_key(t)).r

def L(t):
    if t==E: return 0
    return (1 if isinstance(t.l,N) else 0)+L(t.l)+L(t.r)
def R(t):
    if t==E: return 0
    return (1 if isinstance(t.r,N) else 0)+R(t.l)+R(t.r)
def two(t):
    if t==E: return 0
    return (1 if isinstance(t.l,N) and isinstance(t.r,N) else 0)+two(t.l)+two(t.r)
def NE(t): return int(t!=E)
for Pcoef in [(3,2,-1),(4,3,-2),(5,4,-3),(3,1,0),(4,2,0),(4,2,-1),(5,3,-1)]:
 for B in range(0,8):
  maxam=-999
  for n in range(1,9):
   for t in gen(0,n):
    F=lambda x: Pcoef[0]*L(x)+Pcoef[1]*R(x)+Pcoef[2]*two(x)
    am=cost(t,min_key(t))+F(delmin(t))+B*NE(delmin(t))-F(t)
    maxam=max(maxam,am)
  if maxam<=2:
   print('P',Pcoef,'B',B,'max',maxam)
print('done')
