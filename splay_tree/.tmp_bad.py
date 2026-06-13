exec(open('.tmp_splay.py').read())

def min_key(t):
    while isinstance(t.l,N): t=t.l
    return t.k
def delmin(t):
    q=min_key(t); st=splay(t,q); return st.r

def left_edges(t):
    if t==E: return 0
    return (1 if isinstance(t.l,N) else 0)+left_edges(t.l)+left_edges(t.r)

def show(t,indent=0):
    if t==E: return 'E'
    return f'({show(t.l)} {t.k} {show(t.r)})'
for n in range(1,9):
  for t in gen(0,n):
    am=cost(t,min_key(t))+left_edges(delmin(t))-left_edges(t)
    if am>=4:
      print('n',n,'am',am,'cost',cost(t,min_key(t)),'L',left_edges(t),'La',left_edges(delmin(t)), show(t),'after',show(delmin(t)))
      raise SystemExit
