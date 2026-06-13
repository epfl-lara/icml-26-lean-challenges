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
def main():
 ap=argparse.ArgumentParser(); ap.add_argument('--n',type=int,default=9); ap.add_argument('--slack',type=int,default=2); ap.add_argument('--seconds',type=float,default=60)
 args=ap.parse_args(); start=time.time(); count=0; best=(-999,None)
 for n in range(2,args.n+1):
  arr=bsts(tuple(range(n)))
  for q in range(n):
   for x in range(q):
    for actual in arr:
     ra=root(actual)
     if ra is None or ra>x: continue
     for reset in arr:
      if root(reset)!=q: continue
      if keys(actual)!=keys(reset): continue
      if path(actual,x)>path(reset,x)+args.slack: continue
      for y in range(x+1):
       actual2=splay(actual,y); reset2=splay(splay(reset,y),q)
       gap=path(actual2,x)-path(reset2,x)
       count+=1
       if gap>best[0]: best=(gap,(n,q,x,y,actual,reset,actual2,reset2))
       if gap>args.slack:
        print('CE',n,q,x,y,'gap',gap,'best',best); print(actual,reset); return
       if count%1000000==0: print('progress',count,'best',best[0], 'elapsed',time.time()-start, flush=True)
       if time.time()-start>args.seconds: print('timeout',count,'best',best); return
  print('done n',n,'count',count,'best',best[0], flush=True)
 print('ok',count,'best',best)
main()
