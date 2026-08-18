"""Global verification of the two e-window extrema (heavy numerics)."""
import json, os, sys
import numpy as np
from scipy.optimize import minimize
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
ROOT = os.path.dirname(HERE)
from quartic_common import crit_points, g_of

def bcd(x):
    x1,x2,x3=x
    return -4.0*(x1+x2+x3)/3.0, 2.0*(x1*x2+x1*x3+x2*x3), -4.0*x1*x2*x3
def gx(xi,x):
    b,c,d=bcd(x); return (((xi+b)*xi+c)*xi+d)*xi
CONS=([{"type":"ineq","fun":lambda v,j=j: 1.0-bcd(v)[j]} for j in range(3)]
     +[{"type":"ineq","fun":lambda v,j=j: bcd(v)[j]+1.0} for j in range(3)]
     +[{"type":"ineq","fun":lambda v: v[1]-v[0]},{"type":"ineq","fun":lambda v: v[2]-v[1]}])
def feas(v): return all(c["fun"](v)>-1e-9 for c in CONS)

# ---------- many feasible starts: sample (b,c,d) in the region, take its roots
rng=np.random.default_rng(11)
starts=[]
while len(starts)<4000:
    b=rng.random(60000)*2-1; c=rng.random(60000)*2-1; d=rng.random(60000)*2-1
    x1,x2,x3=crit_points(b,c,d); ok=np.isfinite(x1)
    for v in np.stack([x1[ok],x2[ok],x3[ok]],axis=1): starts.append(v)
starts=starts[:4000]
print(len(starts),"feasible starts",flush=True)

def run(obj,tag):
    best=(np.inf,None)
    for kk,x0 in enumerate(starts):
        if kk%1000==0: print(f"   [{tag}] {kk}/{len(starts)} best={best[0]:.12f}",flush=True)
        r=minimize(obj,x0,method="SLSQP",constraints=CONS,options={"maxiter":300,"ftol":1e-16})
        if feas(r.x):
            v=obj(r.x)
            if v<best[0]: best=(float(v),r.x.copy())
    print(f"{tag}: {best[0]:.15f}  roots={best[1]}  (b,c,d)={bcd(best[1])}",flush=True)
    return best

bG=run(lambda x:-gx(x[1],x), "max g(x2)  [reported as -value]")
bH=run(lambda x: max(gx(x[0],x),gx(x[2],x)), "min max(g1,g3)")
print("\n max g(x2)      =", -bG[0], "   candidate 0.284002434302530330")
print(" min max(g1,g3) =",  bH[0], "   candidate -25/64 =", -25/64)

# ---------- fine cube grid corroboration
n=500
ax=np.linspace(-1,1,n); bestG=-np.inf; bestH=np.inf; aG=aH=None
for i0 in range(0,n,25):
    bb=ax[i0:i0+25]
    B,C,D=np.meshgrid(bb,ax,ax,indexing="ij")
    x1,x2,x3=crit_points(B,C,D)
    g1=g_of(x1,B,C,D); g2=g_of(x2,B,C,D); g3=g_of(x3,B,C,D)
    G=np.where(np.isfinite(g2),g2,-np.inf); H=np.where(np.isfinite(g2),np.maximum(g1,g3),np.inf)
    k=int(np.argmax(G))
    if G.flat[k]>bestG: bestG=float(G.flat[k]); i=np.unravel_index(k,G.shape); aG=(float(B[i]),float(C[i]),float(D[i]))
    k=int(np.argmin(H))
    if H.flat[k]<bestH: bestH=float(H.flat[k]); i=np.unravel_index(k,H.shape); aH=(float(B[i]),float(C[i]),float(D[i]))
print(f"\ngrid {n}^3: max g(x2)={bestG:.12f} at {aG}",flush=True)
print(f"grid {n}^3: min max(g1,g3)={bestH:.12f} at {aH}")
json.dump({"slsqp_max_g_x2":-bG[0],"slsqp_min_maxg13":bH[0],
           "slsqp_argmax_bcd":list(map(float,bcd(bG[1]))),
           "slsqp_argmin_bcd":list(map(float,bcd(bH[1]))),
           "grid_n":n,"grid_max_g_x2":bestG,"grid_min_maxg13":bestH,
           "grid_argmax":list(aG),"grid_argmin":list(aH)},
          open(os.path.join(ROOT,"results","quartic_ebounds_global.json"),"w"),indent=2)
print("wrote results/quartic_ebounds_global.json")
