def node(l,k,r): return (l,k,r)
def isE(t): return t == ()
def right_spine(n):
    t=()
    for k in range(n-1,-1,-1):
        t=node((),k,t)
    return t

def num(t): return 0 if isE(t) else 1+num(t[0])+num(t[2])
def rotateRight(x):
    if not isE(x) and not isE(x[0]):
        a,xk,b=x[0]
        y=x[1]; c=x[2]
        return node(a,xk,node(b,y,c))
    return x
def rotateLeft(x):
    if not isE(x) and not isE(x[2]):
        a=x[0]; xk=x[1]
        b,yk,c=x[2]
        return node(node(a,xk,b),yk,c)
    return x
def rotate(s,rt):
    if rt=='zigZig': return rotateRight(rotateRight(s))
    if rt=='zigZag':
        if not isE(s): return rotateRight(node(rotateLeft(s[0]),s[1],s[2]))
        return s
    if rt=='zagZag': return rotateLeft(rotateLeft(s))
    if rt=='zagZig':
        if not isE(s): return rotateLeft(node(s[0],s[1],rotateRight(s[2])))
        return s
    if rt=='zig': return rotateRight(s)
    if rt=='zag': return rotateLeft(s)

def splay(t,q):
    if isE(t): return ()
    l,k,r=t
    if q==k: return t
    if q<k:
        if isE(l): return t
        ll,lk,lr=l
        if q<lk:
            if isE(ll): return rotate(node(l,k,r),'zig')
            t1=splay(ll,q)
            return rotate(node(node(t1,lk,lr),k,r),'zigZig')
        elif lk<q:
            if isE(lr): return rotate(node(l,k,r),'zig')
            t1=splay(lr,q)
            return rotate(node(node(ll,lk,t1),k,r),'zigZag')
        else: return rotate(t,'zig')
    else:
        if isE(r): return t
        rl,rk,rr=r
        if q<rk:
            if isE(rl): return rotate(node(l,k,r),'zag')
            t1=splay(rl,q)
            return rotate(node(l,k,node(t1,rk,rr)),'zagZig')
        elif rk<q:
            if isE(rr): return rotate(node(l,k,r),'zag')
            t1=splay(rr,q)
            return rotate(node(l,k,node(rl,rk,t1)),'zagZag')
        else: return rotate(t,'zag')

def cost(t,q):
    if isE(t): return 0
    l,k,r=t
    if q==k: return 0
    if q<k:
        if isE(l): return 0
        ll,lk,lr=l
        if q<lk:
            if isE(ll): return 1
            return cost(ll,q)+2
        elif lk<q:
            if isE(lr): return 1
            return cost(lr,q)+2
        else: return 1
    else:
        if isE(r): return 0
        rl,rk,rr=r
        if q<rk:
            if isE(rl): return 1
            return cost(rl,q)+2
        elif rk<q:
            if isE(rr): return 1
            return cost(rr,q)+2
        else: return 1

def inorder(t): return [] if isE(t) else inorder(t[0])+[t[1]]+inorder(t[2])
def depth(t,q,d=0):
    if isE(t): return None
    l,k,r=t
    if q==k: return d
    return depth(l,q,d+1) if q<k else depth(r,q,d+1)
def seq_cost(t,seq):
    c=0
    for q in seq:
        c+=cost(t,q)
        t=splay(t,q)
    return c,t
for n in [3,4,5,6,8,10,20,50]:
    t=right_spine(n)
    seq=[0 if i%2==0 else n-1 for i in range(n)]
    c,tf=seq_cost(t,seq)
    print(n,c, c/n, 'd0', depth(tf,0), 'dlast', depth(tf,n-1))
