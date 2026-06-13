from functools import lru_cache
import argparse,time
E=()
def root(t): return None if t==() else t[1]
def keys(t):
 if t==(): return []
 l,k,r=t; return keys(l)+[k]+keys(r)
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
 a,y,b=l; return (a,y,(b,k,r))
def rotL(t):
 if t==(): return t
 l,k,r=t
 if r==(): return t
 b,y,c=r; return ((l,k,b),y,c)
def splay(t,x):
 if t==(): return t
 l,k,r=t
 if x==k: return t
 if x<k:
  if l==(): return t
  ll,lk,lr=l
  if x<lk:
   if ll==(): return rotR(t)
   return rotR(rotR(((splay(ll,x),lk,lr),k,r)))
  if lk<x:
   if lr==(): return rotR(t)
   return rotR((ll,lk,rotL((splay(lr,x),k,r))))
  return rotR(t)
 else:
  if r==(): return t
  rl,rk,rr=r
  if x<rk:
   if rl==(): return rotL(t)
   return rotL((l,k,rotR((splay(rl,x),rk,rr))))
  if rk<x:
   if rr==(): return rotL(t)
   return rotL(rotL(((l,k,rl),rk,splay(rr,x))))
  return rotL(t)
@lru_cache(None)
def bsts(vals):
 vals=tuple(vals)
 if not vals: return ((),)
 out=[]
 for i,k in enumerate(vals):
  for l in bsts(vals[:i]):
   for r in bsts(vals[i+1:]): out.append((l,k,r))
 return tuple(out)
def inv(actual,reset,q,lo,slack):
 if root(reset)!=q or keys(actual)!=keys(reset): return False
 for z in range(lo,q):
  if path(actual,z)>path(reset,z)+slack:
   return False
 return True
def main():
 ap=argparse.ArgumentParser(); ap.add_argument('--n',type=int,default=8); ap.add_argument('--slack',type=int,default=2); ap.add_argument('--seconds',type=float,default=120)
 args=ap.parse_args(); start=time.time(); count=0; best=(-999,None)
 for n in range(2,args.n+1):
  arr=bsts(tuple(range(n)))
  for q in range(1,n):
   for lo in range(q):
    for actual in arr:
     for reset in arr:
      if not inv(actual,reset,q,lo,args.slack): continue
      for y in range(lo+1):
       actual2=splay(actual,y); reset2=splay(splay(reset,y),q)
       for z in range(lo,q):
        gap=path(actual2,z)-path(reset2,z); count+=1
        if gap>best[0]: best=(gap,(n,q,lo,y,z,actual,reset,actual2,reset2))
        if gap>args.slack:
         print('CE', 'n',n,'q',q,'lo',lo,'y',y,'z',z,'gap',gap,'best',best); print('actual',actual,'reset',reset); return
       if count%1000000==0: print('progress',count,'best',best[0], 'elapsed',time.time()-start, flush=True)
       if time.time()-start>args.seconds: print('timeout',count,'best',best); return
  print('done n',n,'count',count,'best',best[0], flush=True)
 print('ok',count,'best',best)
main()
