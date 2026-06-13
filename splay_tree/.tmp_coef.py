exec(open('.tmp_splay.py').read())

def min_key(t):
    while isinstance(t.l,N): t=t.l
    return t.k
def delmin(t):
    st=splay(t,min_key(t)); return st.r

def left_edges(t):
    if t==E: return 0
    return (1 if isinstance(t.l,N) else 0)+left_edges(t.l)+left_edges(t.r)
def right_edges(t):
    if t==E: return 0
    return (1 if isinstance(t.r,N) else 0)+right_edges(t.l)+right_edges(t.r)
def nodes_with_two(t):
    if t==E: return 0
    return (1 if isinstance(t.l,N) and isinstance(t.r,N) else 0)+nodes_with_two(t.l)+nodes_with_two(t.r)
def left_spine(t):
    if t==E: return 0
    return (1 if isinstance(t.l,N) else 0)+left_spine(t.l)
features=[left_edges,right_edges,nodes_with_two,left_spine]
for coeffs in [(a,b,c,d) for a in range(0,5) for b in range(-2,5) for c in range(-2,5) for d in range(-2,5)]:
  def F(t,cs=coeffs): return sum(c*f(t) for c,f in zip(cs,features))
  # require F bounded below maybe >= -2n? skip; max abs coeff linear.
  maxam=-999
  for n in range(1,8):
    for t in gen(0,n):
      am=cost(t,min_key(t))+F(delmin(t))-F(t)
      if am>maxam: maxam=am
  if maxam<=2 and coeffs[0]+coeffs[1]+coeffs[2]+abs(coeffs[3])<=8:
    print('coeff',coeffs,'maxam',maxam)
    break
