exec(open('.tmp_splay.py').read())

def min_key(t):
    while isinstance(t.l,N): t=t.l
    return t.k
def rest(t): return splay(t,min_key(t)).r

def L(t): return 0 if t==E else (t.l!=E)+L(t.l)+L(t.r)
def NE(t): return int(t!=E)
for A in range(0,8):
 for C in range(0,10):
  ok=True; maxam=-999
  for n in range(1,9):
   for t in gen(0,n):
    am=cost(t,min_key(t))+L(rest(t))+A*NE(rest(t))-L(t)
    maxam=max(maxam,am)
    if am>C: ok=False; break
   if not ok: break
  if ok:
   print('A',A,'C',C,'max',maxam); break
