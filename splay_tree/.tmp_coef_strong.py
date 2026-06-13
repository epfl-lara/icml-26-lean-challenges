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
def NE(t): return 1 if isinstance(t,N) else 0
features=[L,R,two]
for a in range(0,6):
 for b in range(0,6):
  for c in range(-3,4):
   for B in range(0,5):
    maxam=-999
    bad=False
    for n in range(1,8):
     for t in gen(0,n):
      F=lambda x: a*L(x)+b*R(x)+c*two(x)
      am=cost(t,min_key(t))+F(delmin(t))+B*NE(delmin(t))-F(t)
      maxam=max(maxam,am)
      if am>2: bad=True; break
     if bad: break
    if not bad:
     print('coeff',a,b,c,'B',B,'maxam',maxam); raise SystemExit
print('none')
