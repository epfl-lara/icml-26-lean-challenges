exec(open('.tmp_splay.py').read())

def L(t): return 0 if t==E else (t.l!=E)+L(t.l)+L(t.r)
def R(t): return 0 if t==E else (t.r!=E)+R(t.l)+R(t.r)
def two(t): return 0 if t==E else ((t.l!=E) and (t.r!=E))+two(t.l)+two(t.r)
features=[L,R,two]
for coeff in [(2,1,0),(3,2,-1),(5,3,-1),(1,0,0),(0,1,0),(4,2,0),(6,4,-2)]:
  maxam=-999; bad=None
  for n in range(1,9):
    for t0 in gen(0,n):
      t=t0
      for i in range(n):
        F=lambda x: coeff[0]*L(x)+coeff[1]*R(x)+coeff[2]*two(x)
        am=cost(t,i)+F(splay(t,i))-F(t)
        if am>maxam: maxam=am; bad=(n,i,am,cost(t,i),F(t),F(splay(t,i)),t)
        t=splay(t,i)
  print(coeff, maxam,bad[:6])
