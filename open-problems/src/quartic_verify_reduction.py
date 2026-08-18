"""INDEPENDENT verification of the (b,m,tau) reduction claims.

Claims checked (all against quartic_common.crit_points / g_of, i.e. the
already-validated raw machinery):
  (1) m := 3b^2/16 - c/2 > 0  and |tau| < tau_c := 8/(3 sqrt3)  <=>  3 real crit pts
      where tau := delta/m^{3/2},  delta := d - bc/2 + b^3/8.
  (2) L(b,c,d) = m^2 * Lambda(tau)
  (3) Lambda(tau) = S (4-3S^2)^{3/2}  where tau = 4S(S^2-1), S in [1,2/sqrt3]
  (4) K := int Lambda dtau = 128/105
  (5) T(z) := int_z^{tau_c} Lambda dtau = (4/105) u^{5/2} (21-5u),
      u in [0,1] the root of 16(1-u)^2(4-u) = 27 z^2.
  (6) db dc dd = 2 m^{3/2} db dm dtau
  (7) unclipped 16 P_B = (4K/9) 2^-18 int_{-1}^1 (3b^2+8)^{9/2} db
"""
import os, sys
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from quartic_common import crit_points, g_of, d_band

rng = np.random.default_rng(20260818)
TAU_C = 8.0/(3.0*np.sqrt(3.0))

N = 2_000_000
b = rng.random(N)*2-1; c = rng.random(N)*2-1; d = rng.random(N)*2-1
x1,x2,x3 = crit_points(b,c,d)
g1=g_of(x1,b,c,d); g2=g_of(x2,b,c,d); g3=g_of(x3,b,c,d)
L = g2 - np.maximum(g1,g3)
ok_raw = np.isfinite(L)

m = 3*b*b/16 - c/2
delta = d - b*c/2 + b**3/8
with np.errstate(invalid='ignore', divide='ignore'):
    tau = delta/np.power(np.abs(m), 1.5)*np.sign(m)**0  # only used where m>0
    tau = np.where(m>0, delta/np.power(np.where(m>0,m,1.0),1.5), np.nan)
ok_new = (m>0) & (np.abs(tau) < TAU_C)
print("(1) region test: mismatches =", int(np.count_nonzero(ok_raw ^ ok_new)), "of", N)

sel = ok_raw
Lam_emp = L[sel]/m[sel]**2
t = tau[sel]
# (3) Lambda closed form: solve tau=4S(S^2-1) for S in [1,2/sqrt3] (use |tau|)
at = np.abs(t)
# S from the u-cubic: 27 tau^2 = 16(1-u)^2(4-u), u=4-3S^2 in [0,1]; v=1-u solves v^3+3v^2=27tau^2/16
def v_of(z):
    rhs = 27.0*z*z/16.0
    v = np.full_like(rhs, 0.5)
    for _ in range(80):
        f = v**3 + 3*v**2 - rhs
        fp = 3*v**2 + 6*v
        v = np.clip(v - f/np.where(fp==0,1e-300,fp), 0.0, 1.0)
    return v
v = v_of(at); u = 1.0-v
S = np.sqrt((4.0-u)/3.0)
Lam_cf = S*np.power(4.0-3.0*S*S, 1.5)
print("(2)+(3) max |L/m^2 - S(4-3S^2)^{3/2}| =", float(np.max(np.abs(Lam_emp-Lam_cf))),
      "  max rel =", float(np.max(np.abs(Lam_emp-Lam_cf)/np.maximum(Lam_emp,1e-12))))
# also check tau = 4S(S^2-1) round trip
print("    max |4S(S^2-1) - |tau|| =", float(np.max(np.abs(4*S*(S*S-1)-at))))

# (4)(5) exact integrals vs numeric
from scipy.integrate import quad
def Lam_of_tau(z):
    z=abs(z); rhs=27*z*z/16
    from scipy.optimize import brentq
    vv=brentq(lambda v: v**3+3*v**2-rhs, 0.0, 1.0, xtol=1e-15, rtol=1e-15)
    uu=1-vv; SS=np.sqrt((4-uu)/3)
    return SS*(4-3*SS*SS)**1.5
K_num = quad(Lam_of_tau, -TAU_C, TAU_C, limit=400, epsabs=1e-13, epsrel=1e-13)[0]
print("(4) K numeric =", K_num, "  128/105 =", 128/105, "  diff =", K_num-128/105)

def T_num(z):
    return quad(Lam_of_tau, z, TAU_C, limit=400, epsabs=1e-14, epsrel=1e-14)[0]
def T_cf(z):
    rhs=27*z*z/16
    from scipy.optimize import brentq
    vv=brentq(lambda v: v**3+3*v**2-rhs, 0.0, 1.0, xtol=1e-16, rtol=1e-15)
    uu=1-vv
    return (4/105)*uu**2.5*(21-5*uu)
print("(5) T closed form vs numeric:")
for z in [0.0,0.2,0.5,0.9,1.2,1.5,1.5395]:
    print(f"    z={z:.4f}  num={T_num(z):.15f}  cf={T_cf(z):.15f}  diff={T_num(z)-T_cf(z):+.2e}")

# (6) Jacobian: numeric determinant of (b,c,d)->(b,m,tau)
import numpy.linalg as la
for _ in range(3):
    b0,c0,d0 = rng.random()*2-1, -rng.random(), rng.random()*2-1
    def F(v):
        bb,cc,dd = v
        mm = 3*bb*bb/16-cc/2
        dl = dd - bb*cc/2 + bb**3/8
        return np.array([bb, mm, dl/mm**1.5])
    h=1e-6; J=np.zeros((3,3)); v0=np.array([b0,c0,d0])
    for j in range(3):
        e=np.zeros(3); e[j]=h
        J[:,j]=(F(v0+e)-F(v0-e))/(2*h)
    mm = 3*b0*b0/16-c0/2
    print(f"(6) b={b0:+.3f} c={c0:+.3f} d={d0:+.3f}: 1/|det J| = {1/abs(la.det(J)):.12f}   2 m^{{3/2}} = {2*mm**1.5:.12f}")

# (7) unclipped closed form
val = quad(lambda x: (3*x*x+8)**4.5, -1, 1, epsabs=1e-14, epsrel=1e-14, limit=200)[0]
unc = (4*(128/105)/9)*2**-18*val
import mpmath as mp
mp.mp.dps=40
cf = mp.sqrt(3)*mp.asinh(mp.sqrt(6)/4)/90 + 7013*mp.sqrt(11)/302400
print("(7) unclipped 16P_B numeric =", repr(unc), "  claimed closed form =", mp.nstr(cf,25),
      "  diff =", float(unc-cf))
