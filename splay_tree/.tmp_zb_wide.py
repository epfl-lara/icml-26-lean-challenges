import importlib.util, random, sys
from pathlib import Path
sys.setrecursionlimit(1000000)
spec = importlib.util.spec_from_file_location("alt", str(Path("/localhome/milikic/icml_epflemma_projects/splay_tree/.tmp_alt_sim.py")))
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
node, isE, splay = m.node, m.isE, m.splay
src=open('/tmp/lambda_hunt2.py').read()
helpers=src[src.index("def left_spine_t"):src.index("def run(")]
exec(helpers)
src2=open('/tmp/crossing_decay.py').read()
exec(src2[src2.index("def gen_runs_s"):src2.index("print(")])
src3=open('/tmp/v_adversary.py').read()
exec(src3[src3.index("def right_spine_t"):src3.index("def test_both")])
def gen_collapse(n,seed):
    random.seed(seed)
    lo,hi=0,n-1; out=[]; sides=[]
    for _ in range(n):
        if lo>hi: lo=hi=(lo+hi)//2
        r=random.random()
        if r<0.35: v=random.randint(lo,min(hi,lo+3)); s=0; lo=v
        elif r<0.7: v=random.randint(max(lo,hi-3),hi); s=1; hi=v
        elif r<0.85: v=random.randint(lo,min(hi,lo+2)); s=1; hi=v
        else: v=random.randint(max(lo,hi-2),hi); s=0; lo=v
        out.append(v); sides.append(s)
    return out,sides
def spath(t,q):
    out=[]
    while not isE(t):
        out.append(t[1])
        if q==t[1]: break
        t=t[0] if q<t[1] else t[2]
    return out
def shared_split(Pv,Pq):
    nn=0
    for a,b in zip(Pv,Pq):
        if a==b: nn+=1
        else: break
    return Pv[:nn],Pv[nn:]

KAP=9
def run_kernel(init,X,sides):
    """Track EXACTLY the Lean kernel quantity: at each step i, for b' in {0,1},
    j = first index >= i+1 with sides[j]==b'; suffix = divergeSuffix(X[j], X[i], t_i);
    zlb = #{z in suffix : touched_i(z) and b_i(z) <= 1}."""
    n=len(X)
    t=init; touched=set()
    b={}; worst=0
    for i,x in enumerate(X):
        for bp in (0,1):
            j=next((j for j in range(i+1,n) if sides[j]==bp),None)
            if j is None or X[j]==X[i]: continue
            sh,suf=shared_split(spath(t,X[j]),spath(t,x))
            z1=len([z for z in suf if z in touched and b.get(z,0)<=1])
            worst=max(worst,z1)
        s=sides[i]
        P=spath(t,x); c=len(P)-1
        Pset=set(P); fresh=len(Pset-touched)
        draw=max(0.0,2*c-2*KAP*(1+fresh))
        avail=sum(b.get(z,0) for z in Pset)
        rem=min(draw,avail); shortfall=max(0.0,draw-avail)
        for z in P:
            if rem<=0: break
            d=min(b.get(z,0),rem)
            if d>0: b[z]-=d; rem-=d
        t2=splay(t,x)
        posn={z:idx for idx,z in enumerate(P)}
        def kd2(z):
            d=1; u=t2
            while not isE(u):
                if u[1]==z: return d
                u=u[0] if z<u[1] else u[2]
                d+=1
            return 10**9
        keys=[z for z in P if (z>=x if s==0 else z<=x)]
        budget=c+2-shortfall
        for z in keys:
            if 2*kd2(z) <= posn[z]+5 and budget>=2:
                b[z]=b.get(z,0)+2; budget-=2
        if s==0: b={z:v for z,v in b.items() if z>=x}
        else: b={z:v for z,v in b.items() if z<=x}
        touched|=Pset
        t=t2
    return worst

def gen_rand_seeded(n,seed):
    random.seed(seed)
    lo,hi=0,n-1; out=[]; sides=[]
    for _ in range(n):
        if lo>hi: lo=hi=(lo+hi)//2
        if random.random()<0.5:
            v=random.randint(lo,min(hi,lo+random.randint(0,6))); s=0; lo=v
        else:
            v=random.randint(max(lo,hi-random.randint(0,6)),hi); s=1; hi=v
        out.append(v); sides.append(s)
    return out,sides

worst=0; rows=0; worst_case=None
for n in [32,64,128,256]:
    fams=[('alt',gen_runs_s(n,1)),('runs2',gen_runs_s(n,2)),('runs4',gen_runs_s(n,4)),('runs8',gen_runs_s(n,8))]
    fams=[(nm,(v[0],v[2]) if len(v)==3 else (v[0],v[1])) for nm,v in fams]
    for sd in range(40):
        fams.append((f'rand{sd}',gen_rand_seeded(n,sd)))
        fams.append((f'coll{sd}',gen_collapse(n,sd)))
    fams.append(('x20like',([0]+[1]*(n-1),[0]+[1]*(n-1))))
    for name,(X,sides) in fams:
        for iname,init in [('spine',left_spine_t(list(range(n)))),('rand',rand_bst(list(range(n)))),('V',v_tree(n)),('W',w_tree(n))]:
            w=run_kernel(init,X,sides)
            rows+=1
            if w>worst: worst=w; worst_case=(name,iname,n)
print(f"kernel-shape sweep: rows={rows} worst zlb(b<=1) at consumption = {worst} (need <= 9); worst case: {worst_case}")
