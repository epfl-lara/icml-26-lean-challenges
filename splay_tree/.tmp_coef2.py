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
for a in range(0,8):
 for b in range(0,8):
  for c in range(-3,4):
   maxam=-999
   for n in range(1,9):
    for t in gen(0,n):
     F=lambda x: a*L(x)+b*R(x)+c*two(x)
     am=cost(t,min_key(t))+F(delmin(t))-F(t)
     maxam=max(maxam,am)
   if maxam<=2:
    print('coeff',a,b,c,'max',maxam); raise SystemExit
print('none')
