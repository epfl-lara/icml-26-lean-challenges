from itertools import combinations, product
from functools import lru_cache
import time, argparse, random

class E: pass
E=()
def node(l,k,r): return (l,k,r)
def keys(t):
    if t==(): return []
    l,k,r=t; return keys(l)+[k]+keys(r)
def root(t): return None if t==() else t[1]
def path(t,x):
    if t==(): return 0
    l,k,r=t
    if x<k: return 1+path(l,x)
    if k<x: return 1+path(r,x)
    return 1
def rotR(t):
    if t==(): return t
    l,k,r=t
    if l==(): return t
    a,y,b=l
    return (a,y,(b,k,r))
def rotL(t):
    if t==(): return t
    l,k,r=t
    if r==(): return t
    b,y,c=r
    return ((l,k,b),y,c)
def splay(t,x):
    if t==(): return t
    l,k,r=t
    if x<k:
        if l==(): return t
        ll,lk,lr=l
        if x<lk:
            newl=splay(ll,x)
            return rotR(rotR(((newl,lk,lr),k,r)))
        elif lk<x:
            newlr=splay(lr,x)
            return rotR((ll,lk,rotL((newlr,k,r))))
        else:
            return rotR(t)
    elif k<x:
        if r==(): return t
        rl,rk,rr=r
        if x<rk:
            newrl=splay(rl,x)
            return rotL((l,k,rotR((newrl,rk,rr))))
        elif rk<x:
            newr=splay(rr,x)
            return rotL(rotL(((l,k,rl),rk,newr)))
        else:
            return rotL(t)
    else:
        return t
@lru_cache(None)
def bsts_tuple(vals):
    vals=tuple(vals)
    if not vals: return ((),)
    out=[]
    for idx,k in enumerate(vals):
        for l in bsts_tuple(vals[:idx]):
            for r in bsts_tuple(vals[idx+1:]):
                out.append((l,k,r))
    return tuple(out)
def bst(n): return bsts_tuple(tuple(range(n)))
def pair_gap(actual,reset,q,x):
    return path(actual,x)+path(splay(actual,x),q) - path(actual,q)-path(reset,x)-path(splay(reset,x),q)

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--n',type=int,default=9); ap.add_argument('--slack',type=int,default=0); ap.add_argument('--seconds',type=float,default=60)
    args=ap.parse_args(); start=time.time(); count=0; best=(-999,None)
    for n in range(2,args.n+1):
      arr=bst(n)
      for q in range(n):
       for x in range(q):
        for actual in arr:
         ra=root(actual)
         if ra is None or ra>x: continue
         for reset in arr:
          if root(reset)!=q: continue
          # assume current fixed pair bound with slack?
          if pair_gap(actual,reset,q,x) > args.slack: continue
          for y in range(x+1):
           actual2=splay(actual,y)
           reset2=splay(splay(reset,y),q)
           gap=pair_gap(actual2,reset2,q,x)
           count+=1
           if gap>best[0]: best=(gap,(n,q,x,y,actual,reset,actual2,reset2))
           if gap>args.slack:
            print('CE', 'n',n,'q',q,'x',x,'y',y,'gap',gap,'best',best)
            print('actual',actual,'reset',reset)
            return
           if count%500000==0:
            print('progress',count,'best',best[0], 'n',n, 'elapsed',time.time()-start, flush=True)
           if time.time()-start>args.seconds:
            print('timeout count',count,'best',best); return
      print('done n',n,'count',count,'best',best[0], flush=True)
    print('ok count',count,'best',best)
main()
