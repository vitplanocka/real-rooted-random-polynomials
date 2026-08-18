import os, sys, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import quartic_quad_direct as QD
from numpy.polynomial.legendre import leggauss
from scipy.integrate import quad

tol=1e-10
print("symmetry check mid_c(b) vs mid_c(-b):")
for b in [0.3,0.7,0.9,0.5]:
    p=QD.mid_c(b,tol); m=QD.mid_c(-b,tol)
    print(f"  b={b}: {p:.12e}  {m:.12e}  rel {(p-m)/p:+.2e}")

print("\nouter integral: composite GL over b vs nested quad")
bk=0.6143021014162962
xg,wg=leggauss(24)
tot=0.0
for a,z in [(-1.0,-bk),(-bk,0.0),(0.0,bk),(bk,1.0)]:
    mid,half=0.5*(a+z),0.5*(z-a)
    v=half*sum(w*QD.mid_c(float(x),tol) for x,w in zip(mid+half*xg,wg))
    print(f"  GL   b in [{a:+.4f},{z:+.4f}] -> {v:.12f}")
    tot+=v
print(f"  GL total = {tot:.12f}   PB={tot/16:.9f}")

tot2=0.0
for a,z in [(-1.0,-bk),(-bk,0.0),(0.0,bk),(bk,1.0)]:
    v,err=quad(QD.mid_c,a,z,args=(tol,),epsabs=tol,epsrel=tol,limit=200)
    print(f"  quad b in [{a:+.4f},{z:+.4f}] -> {v:.12f}  err={err:.1e}")
    tot2+=v
print(f"  quad total = {tot2:.12f}  PB={tot2/16:.9f}")
