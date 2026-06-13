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
for cond in ['all','bnon','bempty']:
 maxv=-999; bad=None
 for n in range(1,9):
  for t in gen(0,n):
   b=delmin(t)
   if cond=='bnon' and b==E: continue
   if cond=='bempty' and b!=E: continue
   v=cost(t,min_key(t))+F(b)-F(t)
   if v>maxv: maxv=v; bad=(n,v,cost(t,min_key(t)),F(t),F(b),t,b)
 print(cond,maxv,bad[:5])
