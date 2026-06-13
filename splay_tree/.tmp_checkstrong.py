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
def F(t): return 2*L(t)+R(t)
def NE(t): return 1 if isinstance(t,N) else 0
for n in range(1,10):
 for t in gen(0,n):
  d=delmin(t)
  am=cost(t,min_key(t))+F(d)+2*NE(d)-F(t)
  if am>2:
    print('bad',n,am,cost(t,min_key(t)),F(t),F(d),NE(d),t,d); raise SystemExit
print('ok')
