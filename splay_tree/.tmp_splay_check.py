from itertools import product, combinations
from functools import lru_cache

class T:
    __slots__=('l','k','r')
    def __init__(self,l,k,r): self.l=l; self.k=k; self.r=r
    def __repr__(self): return f'({self.l},{self.k},{self.r})'

def rotR(t):
    if t and t.l:
        a,x,b=t.l.l,t.l.k,t.l.r; y=t.k; c=t.r
        return T(a,x,T(b,y,c))
    return t

def rotL(t):
    if t and t.r:
        a,x=t.l,t.k; b,y,c=t.r.l,t.r.k,t.r.r
        return T(T(a,x,b),y,c)
    return t

def rotate(s,rt):
    if rt=='zigZig': return rotR(rotR(s))
    if rt=='zigZag':
        if s: return rotR(T(rotL(s.l),s.k,s.r))
        return s
    if rt=='zagZag': return rotL(rotL(s))
    if rt=='zagZig':
        if s: return rotL(T(s.l,s.k,rotR(s.r)))
        return s
    if rt=='zig': return rotR(s)
    if rt=='zag': return rotL(s)

def cost(t,q):
    if t is None: return 0
    l,k,r=t.l,t.k,t.r
    if q==k: return 0
    elif q<k:
        if l is None: return 0
        ll,lk,lr=l.l,l.k,l.r
        if q<lk:
            return 1 if ll is None else cost(ll,q)+2
        elif lk<q:
            return 1 if lr is None else cost(lr,q)+2
        else: return 1
    else:
        if r is None: return 0
        rl,rk,rr=r.l,r.k,r.r
        if q<rk:
            return 1 if rl is None else cost(rl,q)+2
        elif rk<q:
            return 1 if rr is None else cost(rr,q)+2
        else: return 1

def splay(t,q):
    if t is None: return None
    l,k,r=t.l,t.k,t.r
    if q==k: return t
    elif q<k:
        if l is None: return t
        ll,lk,lr=l.l,l.k,l.r
        if q<lk:
            if ll is None: return rotate(T(l,k,r),'zig')
            tp=T(splay(ll,q),lk,lr); return rotate(T(tp,k,r),'zigZig')
        elif lk<q:
            if lr is None: return rotate(T(l,k,r),'zig')
            tp=T(ll,lk,splay(lr,q)); return rotate(T(tp,k,r),'zigZag')
        else: return rotate(t,'zig')
    else:
        if r is None: return t
        rl,rk,rr=r.l,r.k,r.r
        if q<rk:
            if rl is None: return rotate(T(l,k,r),'zag')
            tp=T(splay(rl,q),rk,rr); return rotate(T(l,k,tp),'zagZig')
        elif rk<q:
            if rr is None: return rotate(T(l,k,r),'zag')
            tp=T(rl,rk,splay(rr,q)); return rotate(T(l,k,tp),'zagZag')
        else: return rotate(t,'zag')

def seqcost(t,X):
    c=0
    for q in X:
        c += cost(t,q)
        t=splay(t,q)
    return c

@lru_cache(None)
def shapes(keys):
    keys=tuple(keys)
    if not keys: return [None]
    res=[]
    for i,k in enumerate(keys):
        for l in shapes(keys[:i]):
            for r in shapes(keys[i+1:]):
                res.append(T(l,k,r))
    return res

def contains_pat(seq, pat):
    m=len(pat); n=len(seq)
    for idx in combinations(range(n),m):
        ok=True
        for a in range(m):
            for b in range(m):
                if (pat[a]<pat[b]) != (seq[idx[a]]<seq[idx[b]]):
                    ok=False; break
            if not ok: break
        if ok: return True
    return False

def avoids(seq,pat): return not contains_pat(seq,pat)
for n in range(1,8):
    maxc=-1; arg=None; count=0
    for X in product(range(n), repeat=n):
        if avoids(X,(2,1,3)) and avoids(X,(2,3,1)):
            count+=1
            for t in shapes(tuple(range(n))):
                c=seqcost(t,X)
                if c>maxc:
                    maxc=c; arg=(X,t)
    print(n, count, len(shapes(tuple(range(n)))), 'max', maxc, 'ratio', maxc/n, 'arg', arg[0] if arg else None)
