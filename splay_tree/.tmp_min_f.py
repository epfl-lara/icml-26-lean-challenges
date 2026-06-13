exec(open('.tmp_splay.py').read())

def min_key(t):
    while isinstance(t.l,N): t=t.l
    return t.k
def rest(t): return splay(t,min_key(t)).r

def L(t): return 0 if t==E else (t.l!=E)+L(t.l)+L(t.r)
def NE(t): return int(t!=E)
for B in range(0,5):
 maxv=-999
 for n in range(1,9):
  for t in gen(0,n):
   v=cost(t,min_key(t))+L(rest(t))-L(t)+B*NE(rest(t))
   maxv=max(maxv,v)
 print(B,maxv)
