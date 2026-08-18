"""float64 prototype of the two C_clip routes, to validate the formulas."""
import numpy as np
from scipy.optimize import brentq
from scipy.integrate import quad
from numpy.polynomial.legendre import leggauss

TAU_C = 8.0/(3.0*np.sqrt(3.0))
def M(b): return (3.0*b*b+8.0)/16.0

# --- b* : tau_1(b) = tau_c
def tau1(b): return (1.0 - b**3/8.0 - b/2.0)/M(b)**1.5
BSTAR = brentq(lambda b: tau1(b)-TAU_C, 0.3, 0.999, xtol=1e-16, rtol=8.9e-16)
print("b* =", repr(BSTAR))

# --- v(z): root in [0,1] of v^3+3v^2 = 27 z^2/16
def v_of(z):
    rhs = 27.0*z*z/16.0
    if rhs<=0: return 0.0
    if rhs>=4.0: return 1.0
    return brentq(lambda v: v**3+3*v**2-rhs, 0.0, 1.0, xtol=1e-17, rtol=8.9e-16)
def T_of(z):
    if z>=TAU_C: return 0.0
    u = 1.0-v_of(z)
    return (4.0/105.0)*u**2.5*(21.0-5.0*u)

# --- tau(y)
def tau_of_y(y): return 4.0*(1.0-y*y)*np.sqrt(4.0-y*y)/(3.0*np.sqrt(3.0))
# --- y1(b)
def y1_of(b):
    t1 = tau1(b)
    if t1>=TAU_C: return 0.0
    return np.sqrt(1.0 - v_of(t1))
# --- n0(b,tau): positive root of tau n^3 + b n^2 - (1+b^3/16)
def n0_of(b, tau):
    K = 1.0+b**3/16.0
    f = lambda n: tau*n**3 + b*n*n - K
    hi = max(1.0, (K/tau)**(1/3.0)*2)
    while f(hi)<0: hi*=2
    return brentq(f, 0.0, hi, xtol=1e-17, rtol=8.9e-16)

# ============ METHOD B: exact m-integral ============
xg,wg = leggauss(80)
def inner_B(b):
    y1 = y1_of(b)
    if y1<=0: return 0.0
    M9 = M(b)**4.5
    s = 0.5*(1+xg); w = 0.5*wg          # s in [0,1]
    tot=0.0
    for si,wi in zip(s,w):
        y = y1*si
        n0 = n0_of(b, tau_of_y(y))
        tot += wi*(3.0-y*y)*y**4*(M9-n0**9)
    return tot*y1
# outer with b = BSTAR + t^2
Tmax = np.sqrt(1.0-BSTAR)
tot=0.0
for npan in (8,16,32):
    tot=0.0
    edges=np.linspace(0,Tmax,npan+1)
    for a,z in zip(edges[:-1],edges[1:]):
        mid,half=0.5*(a+z),0.5*(z-a)
        for x,wt in zip(mid+half*xg, wg):
            t=x; b=BSTAR+t*t
            tot += half*wt*2*t*inner_B(b)
    CB = (32.0/27.0)*tot
    print(f"METHOD B npan={npan:3d}  C_clip = {CB:.16f}")

# ============ METHOD A: exact tau-integral ============
def inner_A(b):
    Mb=M(b)
    # m0: root of 1+b^3/16-b m = tau_c m^{3/2}  -> n0 at tau=tau_c
    n0 = n0_of(b, TAU_C); m0 = n0*n0
    if m0>=Mb: return 0.0
    D=Mb-m0
    tot=0.0
    s=0.5*(1+xg); w=0.5*wg
    for si,wi in zip(s,w):
        m = m0 + D*si*si
        z = (1.0+b**3/16.0-b*m)/m**1.5
        tot += wi*2*si*m**3.5*T_of(z)
    return tot*D
for npan in (8,16,32):
    tot=0.0
    edges=np.linspace(0,Tmax,npan+1)
    for a,z in zip(edges[:-1],edges[1:]):
        mid,half=0.5*(a+z),0.5*(z-a)
        for x,wt in zip(mid+half*xg, wg):
            t=x; b=BSTAR+t*t
            tot += half*wt*2*t*inner_A(b)
    CA = 4.0*tot
    print(f"METHOD A npan={npan:3d}  C_clip = {CA:.16f}")

import mpmath as mp
mp.mp.dps=40
UNC = mp.sqrt(3)*mp.asinh(mp.sqrt(6)/4)/90 + 7013*mp.sqrt(11)/302400
print("\nunclipped 16P_B =", mp.nstr(UNC,25))
print("16P_B (B) =", mp.nstr(UNC-CB,20), "  P_B =", mp.nstr((UNC-CB)/16,20))
print("16P_B (A) =", mp.nstr(UNC-CA,20), "  P_B =", mp.nstr((UNC-CA)/16,20))
print("raw nested-quad float64 16P_B = 0.087429285456   PB = 0.005464330341")
