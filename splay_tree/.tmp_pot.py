exec(open('.tmp_splay.py').read())

def min_key(t):
    assert t!=E
    while isinstance(t.l,N): t=t.l
    return t.k
def delete_root_after_splay_min(t):
    if t==E: return E
    q=min_key(t); st=splay(t,q)
    assert isinstance(st,N)
    return st.r

def left_edges(t):
    if t==E: return 0
    return (1 if isinstance(t.l,N) else 0)+left_edges(t.l)+left_edges(t.r)
def right_edges(t):
    if t==E: return 0
    return (1 if isinstance(t.r,N) else 0)+right_edges(t.l)+right_edges(t.r)
def left_spine(t):
    c=0
    while isinstance(t,N):
      if isinstance(t.l,N): c+=1
      t=t.l
    return c

def weighted_left_depth(t,d=0):
    if t==E: return 0
    return d + weighted_left_depth(t.l,d+1)+weighted_left_depth(t.r,d)
def sum_depth(t,d=0):
    if t==E: return 0
    return d+sum_depth(t.l,d+1)+sum_depth(t.r,d+1)
def count_zigzag(t):
    return 0
features=[left_edges,right_edges,left_spine,weighted_left_depth,sum_depth]
for f in features:
  print('feature',f.__name__)
  for A in range(0,10):
    maxam=0; bad=None
    for n in range(1,9):
      for t in gen(0,n):
        c=cost(t,min_key(t))
        a=delete_root_after_splay_min(t)
        am=c + A*f(a)-A*f(t)
        if am>maxam: maxam=am; bad=(n,t,c,f(t),f(a),am)
    print(A,maxam,bad[:1]+bad[2:] if bad else None)
  print()
