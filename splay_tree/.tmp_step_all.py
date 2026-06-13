exec(open('.tmp_splay.py').read())

def L(t): return 0 if t==E else (t.l!=E)+L(t.l)+L(t.r)
def R(t): return 0 if t==E else (t.r!=E)+R(t.l)+R(t.r)
def two(t): return 0 if t==E else ((t.l!=E) and (t.r!=E))+two(t.l)+two(t.r)
for coeff in [(2,1,0),(3,2,-1),(5,3,-1),(10,5,0)]:
  maxam=-999; bad=None
  for n in range(1,9):
    for t in gen(0,n):
      for q in range(n):
        F=lambda x: coeff[0]*L(x)+coeff[1]*R(x)+coeff[2]*two(x)
        am=cost(t,q)+F(splay(t,q))-F(t)
        if am>maxam: maxam=am; bad=(n,q,am,cost(t,q),F(t),F(splay(t,q)),t)
  print(coeff, maxam,bad[:6])
