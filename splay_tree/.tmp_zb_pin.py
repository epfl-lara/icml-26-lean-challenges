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
def pairs_of(sides,n):
    """C3: consecutive same-side pairs; C4: (j, first-opp-after-j)."""
    out=[]
    for j in range(n):
        # next same-side k
        k=next((k for k in range(j+1,n) if sides[k]==sides[j]),None)
        if k is not None: out.append(('C3',j,k))
        k=next((k for k in range(j+1,n) if sides[k]!=sides[j]),None)
        if k is not None: out.append(('C4',j,k))
    return out

def run(init,X,sides):
    n=len(X)
    t=init; touched=set()
    D=0.0; b={}
    prs=pairs_of(sides,n)
    # per-pair zlb history: pairkey -> list of (i, zb0, zlb1)
    hist={p:[] for p in prs}
    stats={'zb0_all':0,'zlb1_all':0,'zb0_cons':0,'zlb1_cons':0}
    for i,x in enumerate(X):
        for (kind,j,k) in prs:
            if j<i: continue
            if X[k]==X[j]:
                z0=z1=0
            else:
                sh,suf=shared_split(spath(t,X[k]),spath(t,X[j]))
                z0=len([z for z in suf if z in touched and b.get(z,0)==0])
                z1=len([z for z in suf if z in touched and b.get(z,0)<=1])
            hist[(kind,j,k)].append((i,z0,z1))
            stats['zb0_all']=max(stats['zb0_all'],z0)
            stats['zlb1_all']=max(stats['zlb1_all'],z1)
            if j==i:
                stats['zb0_cons']=max(stats['zb0_cons'],z0)
                stats['zlb1_cons']=max(stats['zlb1_cons'],z1)
        # the atomic step (verbatim from zb_final.py)
        s=sides[i]
        P=spath(t,x); c=len(P)-1
        Pset=set(P); fresh=len(Pset-touched)
        draw=max(0.0,2*c-2*KAP*(1+fresh))
        D=D-min(D,draw)+c+2
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
    return stats,hist

allstats={'zb0_all':0,'zlb1_all':0,'zb0_cons':0,'zlb1_cons':0}
# inductivity: for candidate Z, a violation is a transition zlb_i<=Z but zlb_{i+1}>Z
worst_jump=[]  # (delta, name, pair, i, z_i, z_{i+1})
ind_viol={Z:0 for Z in range(0,13)}
rows=0
for n in [20,64,128]:
    fams=[('alt',gen_runs_s(n,1)),('runs4',gen_runs_s(n,4)),('rand2',gen_rand_s(n,23)),('rand4',gen_rand_s(n,5)),
          ('collapse1',gen_collapse(n,7)),('collapse2',gen_collapse(n,99))]
    fams=[(nm,(v[0],v[2]) if len(v)==3 else (v[0],v[1])) for nm,v in fams]
    fams.append(('x20like',([0]+[1]*(n-1),[0]+[1]*(n-1))))
    for name,(X,sides) in fams:
        for iname,init in [('spine',left_spine_t(list(range(n)))),('rand',rand_bst(list(range(n)))),('V',v_tree(n)),('W',w_tree(n))]:
            st,hist=run(init,X,sides)
            rows+=1
            for kk in allstats: allstats[kk]=max(allstats[kk],st[kk])
            for p,h in hist.items():
                for a,bb in zip(h,h[1:]):
                    (i0,z00,z10),(i1,z01,z11)=a,bb
                    d=z11-z10
                    if d>0: worst_jump.append((d,name,iname,p,i0,z10,z11))
                    for Z in ind_viol:
                        if z10<=Z and z11>Z: ind_viol[Z]+=1
print("rows:",rows)
print("MAX zb0 over all pairs/steps:",allstats['zb0_all'])
print("MAX zlb1 (b<=1) over all pairs/steps:",allstats['zlb1_all'])
print("MAX zb0 at consumption (j==i):",allstats['zb0_cons'])
print("MAX zlb1 at consumption (j==i):",allstats['zlb1_cons'])
print("inductivity violations by Z:",{Z:v for Z,v in ind_viol.items()})
worst_jump.sort(reverse=True)
print("worst single-step zlb1 jumps:",worst_jump[:6])
