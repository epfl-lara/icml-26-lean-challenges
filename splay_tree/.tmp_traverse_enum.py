from functools import lru_cache
from itertools import product, permutations

class E: pass
E=()
def N(l,k,r): return (l,k,r)
def num(t): return 0 if t==() else 1+num(t[0])+num(t[2])
def right_spine(n):
    t=()
    for k in reversed(range(n)):
        t=N((),k,t)
    return t
def left_spine(n):
    t=()
    for k in range(n):
        t=N(t,k,())
    return t
def balanced(vals):
    if not vals: return ()
    m=len(vals)//2
    return N(balanced(vals[:m]), vals[m], balanced(vals[m+1:]))
def rotR(t):
    if t and t[0]:
        a,x,b=t[0]
        y=t[1]; c=t[2]
        return N(a,x,N(b,y,c))
    return t
def rotL(t):
    if t and t[2]:
        a=t[0]; x=t[1]
        b,y,c=t[2]
        return N(N(a,x,b),y,c)
    return t
def rotate(s,rt):
    if rt=='zigZig': return rotR(rotR(s))
    if rt=='zagZag': return rotL(rotL(s))
    if rt=='zig': return rotR(s)
    if rt=='zag': return rotL(s)
    if rt=='zigZag':
        if s:
            l,k,r=s; return rotR(N(rotL(l),k,r))
        return s
    if rt=='zagZig':
        if s:
            l,k,r=s; return rotL(N(l,k,rotR(r)))
        return s

def splay(t,q):
    if not t: return ()
    l,k,r=t
    if q==k: return t
    elif q<k:
        if not l: return t
        ll,lk,lr=l
        if q<lk:
            if not ll: return rotate(N(l,k,r),'zig')
            else:
                tp=N(splay(ll,q),lk,lr)
                return rotate(N(tp,k,r),'zigZig')
        elif lk<q:
            if not lr: return rotate(N(l,k,r),'zig')
            else:
                tp=N(ll,lk,splay(lr,q))
                return rotate(N(tp,k,r),'zigZag')
        else: return rotate(t,'zig')
    else:
        if not r: return t
        rl,rk,rr=r
        if q<rk:
            if not rl: return rotate(N(l,k,r),'zag')
            else:
                tp=N(splay(rl,q),rk,rr)
                return rotate(N(l,k,tp),'zagZig')
        elif rk<q:
            if not rr: return rotate(N(l,k,r),'zag')
            else:
                tp=N(rl,rk,splay(rr,q))
                return rotate(N(l,k,tp),'zagZag')
        else: return rotate(t,'zag')

def cost(t,q):
    if not t: return 0
    l,k,r=t
    if q==k: return 0
    elif q<k:
        if not l: return 0
        ll,lk,lr=l
        if q<lk:
            if not ll: return 1
            else: return cost(ll,q)+2
        elif lk<q:
            if not lr: return 1
            else: return cost(lr,q)+2
        else: return 1
    else:
        if not r: return 0
        rl,rk,rr=r
        if q<rk:
            if not rl: return 1
            else: return cost(rl,q)+2
        elif rk<q:
            if not rr: return 1
            else: return cost(rr,q)+2
        else: return 1

def seqcost(t,seq):
    c=0
    for q in seq:
        c+=cost(t,q); t=splay(t,q)
    return c,t

def avoids231(seq):
    n=len(seq)
    for i in range(n):
        for j in range(i+1,n):
            for k in range(j+1,n):
                if seq[k] < seq[i] < seq[j]:
                    return False
    return True

for kind,treefun in [('right',right_spine),('left',left_spine),('bal',lambda n: balanced(list(range(n))))]:
    print('TREE',kind)
    for n in range(1,9):
        maxc=-1; arg=None; cnt=0
        # all functions n^n for n<=7 maybe; for n=8 too huge skip, use permutations for unique
        if n<=6:
            it=product(range(n), repeat=n)
        else:
            it=permutations(range(n))
        for seq in it:
            if avoids231(seq):
                cnt+=1
                c,_=seqcost(treefun(n),seq)
                if c>maxc:
                    maxc=c; arg=seq
        print(n, 'cnt',cnt,'max',maxc,'ratio',maxc/n,'arg',arg)
    print()
