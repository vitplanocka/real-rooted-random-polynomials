"""Forensics: which plausible earlier variant of quartic_quad_direct.py yields
I16 = 0.05020062770699262 ?"""
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

def L_g3(d,b,c):
    x1,x2,x3 = crit_points(b,c,d)
    if not np.isfinite(x1): return 0.0
    return float(g_of(x2,b,c,d) - g_of(x3,b,c,d))

def L_g1(d,b,c):
    x1,x2,x3 = crit_points(b,c,d)
    if not np.isfinite(x1): return 0.0
    return float(g_of(x2,b,c,d) - g_of(x1,b,c,d))

def make_inner(split=True, clip_d=True, Lfun=L_of):
    def inner(c,b,tol):
        dl,dh = d_band(b,c)
        if not np.isfinite(dl): return 0.0
        lo,hi = (max(-1.0,float(dl)), min(1.0,float(dh))) if clip_d else (float(dl),float(dh))
        if hi<=lo: return 0.0
        ds = b*c/2.0 - b**3/8.0
        pts=[lo,hi] if not (split and lo<ds<hi) else [lo,ds,hi]
        return sum(quad(Lfun,a,z,args=(b,c),epsabs=tol,epsrel=tol,limit=200)[0]
                   for a,z in zip(pts[:-1],pts[1:]))
    return inner

def run(name, inner, chi=None, bsplit=None):
    def mid(b,tol):
        hi = 3.0*b*b/8.0 if chi is None else chi
        return quad(inner,-1.0,hi,args=(b,tol),epsabs=tol,epsrel=tol,limit=200)[0]
    bk=0.6143021014162962
    segs = bsplit if bsplit is not None else [(-1.0,-bk),(-bk,0.0),(0.0,bk),(bk,1.0)]
    tot=sum(quad(mid,a,z,args=(tol,),epsabs=tol,epsrel=tol,limit=200)[0] for a,z in segs)
    print(f"  {name:52s} I16={tot:.14f}  {'*** MATCH' if abs(tot-TARGET)<1e-8 else ''}")
    return tot

print("candidate variants (target %.14f):"%TARGET)
run("current code (reference)", make_inner())
run("no dstar split in d", make_inner(split=False))
run("no d clipping to [-1,1]", make_inner(clip_d=True) if False else make_inner(split=True, clip_d=False))
run("c upper limit = 1 instead of 3b^2/8", make_inner(), chi=1.0)
run("no b-kink split (single quad -1..1)", make_inner(), bsplit=[(-1.0,1.0)])
run("b split only at 0", make_inner(), bsplit=[(-1.0,0.0),(0.0,1.0)])
run("L = g2-g3 only (no max)", make_inner(Lfun=L_g3))
run("L = g2-g1 only (no max)", make_inner(Lfun=L_g1))
run("c upper=1 AND no bkink", make_inner(), chi=1.0, bsplit=[(-1.0,1.0)])
run("c upper=1, no dstar split", make_inner(split=False), chi=1.0)
run("no dstar split + no bkink", make_inner(split=False), bsplit=[(-1.0,1.0)])
