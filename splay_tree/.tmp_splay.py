from dataclasses import dataclass
E=()
@dataclass(frozen=True)
class N:
    l: object; k:int; r:object

def num(t): return 0 if t==E else 1+num(t.l)+num(t.r)
def inorder(t): return [] if t==E else inorder(t.l)+[t.k]+inorder(t.r)
def rotR(t):
    if isinstance(t,N) and isinstance(t.l,N):
        a,x,b=t.l.l,t.l.k,t.l.r; y=t.k; c=t.r
        return N(a,x,N(b,y,c))
    return t
def rotL(t):
    if isinstance(t,N) and isinstance(t.r,N):
        a,x,b=t.l,t.k,t.r.l; y=t.r.k; c=t.r.r
        return N(N(a,x,b),y,c)
    return t
def rotate(t,rt):
    if rt=='zigZig': return rotR(rotR(t))
    if rt=='zagZag': return rotL(rotL(t))
    if rt=='zigZag':
        if isinstance(t,N): return rotR(N(rotL(t.l),t.k,t.r))
        return t
    if rt=='zagZig':
        if isinstance(t,N): return rotL(N(t.l,t.k,rotR(t.r)))
        return t
    if rt=='zig': return rotR(t)
    if rt=='zag': return rotL(t)

def splay(t,q):
    if t==E: return E
    l,k,r=t.l,t.k,t.r
    if q==k: return t
    elif q<k:
      if l==E: return t
      ll,lk,lr=l.l,l.k,l.r
      if q<lk:
        if ll==E: return rotate(t,'zig')
        else: return rotate(N(N(splay(ll,q),lk,lr),k,r),'zigZig')
      elif lk<q:
        if lr==E: return rotate(t,'zig')
        else: return rotate(N(N(ll,lk,splay(lr,q)),k,r),'zigZag')
      else: return rotate(t,'zig')
    else:
      if r==E: return t
      rl,rk,rr=r.l,r.k,r.r
      if q<rk:
        if rl==E: return rotate(t,'zag')
        else: return rotate(N(l,k,N(splay(rl,q),rk,rr)),'zagZig')
      elif rk<q:
        if rr==E: return rotate(t,'zag')
        else: return rotate(N(l,k,N(rl,rk,splay(rr,q))),'zagZag')
      else: return rotate(t,'zag')
def cost(t,q):
    if t==E: return 0
    l,k,r=t.l,t.k,t.r
    if q==k: return 0
    elif q<k:
      if l==E: return 0
      ll,lk,lr=l.l,l.k,l.r
      if q<lk:
        if ll==E: return 1
        else: return cost(ll,q)+2
      elif lk<q:
        if lr==E: return 1
        else: return cost(lr,q)+2
      else: return 1
    else:
      if r==E: return 0
      rl,rk,rr=r.l,r.k,r.r
      if q<rk:
        if rl==E: return 1
        else: return cost(rl,q)+2
      elif rk<q:
        if rr==E: return 1
        else: return cost(rr,q)+2
      else: return 1
def seq(t,n):
    c=0
    for i in range(n):
        c += cost(t,i)
        t = splay(t,i)
    return c,t

def gen(lo,n):
    if n==0: return [E]
    res=[]
    for leftn in range(n):
        rightn=n-1-leftn
        k=lo+leftn
        for l in gen(lo,leftn):
          for r in gen(k+1,rightn):
            res.append(N(l,k,r))
    return res

def leftspine(t):
    d=0
    while isinstance(t,N): d+=1; t=t.l
    return d
for n in range(0,11):
    vals=[]
    max_t=None
    for t in gen(0,n):
        v=seq(t,n)[0]
        if not vals or v>max(vals): max_t=t
        vals.append(v)
    print(n, max(vals) if vals else 0, 'ratio', (max(vals)/n if n else 0), 'count',len(vals))
    #print(max_t)
