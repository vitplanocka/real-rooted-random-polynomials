"""Diagnostics: compare quartic_quad_direct's nested-quad pieces against
brute-force fine quadrature."""
import os, sys
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from quartic_common import crit_points, d_band, g_of
from numpy.polynomial.legendre import leggauss
import quartic_quad_direct as QD

def Lvec(d, b, c):
    x1,x2,x3 = crit_points(np.full_like(d,b), np.full_like(d,c), d)
    g1=g_of(x1,b,c,d); g2=g_of(x2,b,c,d); g3=g_of(x3,b,c,d)
    L = g2 - np.maximum(g1,g3)
    return np.where(np.isfinite(L), np.maximum(L,0.0), 0.0)

def inner_bf(b, c, npan=400, n=40):
    dl, dh = d_band(b,c)
    if not np.isfinite(dl): return 0.0
    lo=max(-1.0,float(dl)); hi=min(1.0,float(dh))
    if hi<=lo: return 0.0
    xg,wg=leggauss(n); tot=0.0
    edges=np.linspace(lo,hi,npan+1)
    for a,z in zip(edges[:-1],edges[1:]):
        mid,half=0.5*(a+z),0.5*(z-a)
        tot += half*np.dot(wg, Lvec(mid+half*xg,b,c))
    return tot

print("=== inner d-integral: quad_direct vs brute force ===")
for b,c in [(0.0,-0.5),(0.3,-0.2),(0.9,-0.9),(-0.7,0.1),(0.5,0.0),(0.2,0.1),(-0.95,-0.95),(0.61,-0.3)]:
    a = QD.inner_d(c, b, 1e-10)
    bf = inner_bf(b,c)
    print(f"  b={b:+.3f} c={c:+.3f}: quad={a:.12e}  bf={bf:.12e}  rel={0 if bf==0 else (a-bf)/bf:+.3e}")

print("\n=== middle c-integral: quad_direct vs brute force ===")
def mid_bf(b, npan=300, n=40):
    lo,hi=-1.0, 3.0*b*b/8.0
    xg,wg=leggauss(n); tot=0.0
    edges=np.linspace(lo,hi,npan+1)
    for a,z in zip(edges[:-1],edges[1:]):
        mid,half=0.5*(a+z),0.5*(z-a)
        tot += half*sum(w*inner_bf(b,float(x),npan=60,n=24) for x,w in zip(mid+half*xg,wg))
    return tot
for b in [0.0,0.3,0.9,-0.7]:
    a=QD.mid_c(b,1e-10); bf=mid_bf(b, npan=60, n=24)
    print(f"  b={b:+.3f}: quad={a:.10e}  bf={bf:.10e}  rel={(a-bf)/bf:+.3e}")
