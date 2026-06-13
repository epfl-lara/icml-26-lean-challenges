exec(open('.tmp_splay.py').read())

def min_key(t):
    while isinstance(t.l,N): t=t.l
    return t.k

def L(t): return 0 if t==E else (t.l!=E)+L(t.l)+L(t.r)
def R(t): return 0 if t==E else (t.r!=E)+R(t.l)+R(t.r)
def two(t): return 0 if t==E else ((t.l!=E) and (t.r!=E))+two(t.l)+two(t.r)
for coeff in [(2,1,0),(3,2,-1),(5,3,-1),(1,0,0)]:
 maxam=-999; bad=None
 for n in range(1,9):
  for t in gen(0,n):
   F=lambda x: coeff[0]*L(x)+coeff[1]*R(x)+coeff[2]*two(x)
   am=cost(t,min_key(t))+F(splay(t,min_key(t)))-F(t)
   if am>maxam: maxam=am; bad=(n,am,cost(t,min_key(t)),F(t),F(splay(t,min_key(t))),t)
 print(coeff,maxam,bad[:5])
