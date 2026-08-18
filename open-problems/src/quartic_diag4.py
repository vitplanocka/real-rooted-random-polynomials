"""Forensics round 2: argument-order / parameter-swap style bugs."""
import os, sys, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from quartic_common import crit_points, d_band, g_of
from scipy.integrate import quad
TARGET = 0.05020062770699262
tol = 1e-9

def L_of(d,b,c):
    x1,x2,x3 = crit_points(b,c,d)
    if not np.isfinite(x1): return 0.0
    return float(g_of(x2,b,c,d) - max(g_of(x1,b,c,d), g_of(x3,b,c,d)))

def inner_d_ok(c,b,tol):
    dl,dh = d_band(b,c)
    if not np.isfinite(dl): return 0.0
    lo,hi = max(-1.0,float(dl)), min(1.0,float(dh))
    if hi<=lo: return 0.0
    ds = b*c/2.0 - b**3/8.0
    pts=[lo,hi] if not (lo<ds<hi) else [lo,ds,hi]
    return sum(quad(L_of,a,z,args=(b,c),epsabs=tol,epsrel=tol,limit=200)[0] for a,z in zip(pts[:-1],pts[1:]))

# H1: inner_d declared (b,c,tol) -> quad binds integration var to 'b'
def inner_d_swap(bv,c,tol):
    return inner_d_ok(c,bv,tol)   # i.e. d_band(bv_as_b?, ...) -- emulate: roles swapped
def mid_H1(b,tol):
    return quad(lambda x: inner_d_ok(b, x, tol), -1.0, 3.0*b*b/8.0, epsabs=tol,epsrel=tol,limit=200)[0]

# H2: L_of args swapped inside inner (args=(c,b))
def inner_H2(c,b,tol):
    dl,dh = d_band(b,c)
    if not np.isfinite(dl): return 0.0
    lo,hi = max(-1.0,float(dl)), min(1.0,float(dh))
    if hi<=lo: return 0.0
    return quad(L_of,lo,hi,args=(c,b),epsabs=tol,epsrel=tol,limit=200)[0]
def mid_H2(b,tol):
    return quad(inner_H2,-1.0,3.0*b*b/8.0,args=(b,tol),epsabs=tol,epsrel=tol,limit=200)[0]

# H3: c-band upper limit 3b/8 (typo b instead of b^2)
def mid_H3(b,tol):
    hi = 3.0*b/8.0
    if hi<=-1.0: return 0.0
    return quad(inner_d_ok,-1.0,hi,args=(b,tol),epsabs=tol,epsrel=tol,limit=200)[0]

# H4: d-clip applied as [dl,dh] intersect [0,1] (sign slip)  -- unlikely, cheap
# H5: L integrated over d in [-1,1] with L=0 outside band, single quad, no splits
def mid_H5(b,tol):
    def inn(c,b,tol):
        return quad(L_of,-1.0,1.0,args=(b,c),epsabs=tol,epsrel=tol,limit=200)[0]
    return quad(inn,-1.0,3.0*b*b/8.0,args=(b,tol),epsabs=tol,epsrel=tol,limit=200)[0]

bk=0.6143021014162962
segs=[(-1.0,-bk),(-bk,0.0),(0.0,bk),(bk,1.0)]
for name,mid in [("H1 inner_d arg-order swap (b<->c)",mid_H1),
                 ("H2 L_of args=(c,b) swapped",mid_H2),
                 ("H3 c-upper = 3b/8 typo",mid_H3),
                 ("H5 d over [-1,1], no band, no splits",mid_H5)]:
    try:
        tot=sum(quad(mid,a,z,args=(tol,),epsabs=tol,epsrel=tol,limit=200)[0] for a,z in segs)
        print(f"  {name:42s} I16={tot:.14f} {'*** MATCH' if abs(tot-TARGET)<1e-8 else ''}", flush=True)
    except Exception as ex:
        print(f"  {name:42s} FAILED {ex}", flush=True)
