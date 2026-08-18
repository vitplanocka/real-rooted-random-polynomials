"""High-precision quadrature for P_B via the (b, u, s) reduction.

  16 P_B = (1/7077888) Int_{-1}^{1} db Int_0^{Umax(b)} u^8 [Psi(s_hi)-Psi(s_lo)] du

  Umax(b) = sqrt(9b^2+24),   d* = b(3b^2-u^2)/48,
  R_hi = 216(1-d*)/u^3,  R_lo = 216(-1-d*)/u^3,   (R_hi>0>R_lo always)
  s_hi = min( pi/6, arcsin(min(1,R_hi))/3 ),  s_lo = max(-pi/6, arcsin(max(-1,R_lo))/3)

  Psi(sig) = Int_0^sig G,  G even,
  G(s) = (512 sqrt3/27) cos^3(s+pi/3) sin(s+pi/3) cos(s) (2 cos 2s - 1), s>=0.

G is a degree-7 trigonometric polynomial => Psi is elementary and is used exactly.
The only non-smoothness in the (b,u) plane is where the |d|<=1 clipping switches
on: the curves R_hi=1 and R_lo=-1.  Those are located exactly (roots of cubics in
u) and used as panel edges, as are the b-values where they leave [0,Umax].
"""

import json
import os
import sys

import numpy as np
import sympy as sp
from numpy.polynomial.legendre import leggauss
from scipy.optimize import brentq

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PI6 = np.pi / 6.0
CONST = 7077888.0     # 12 * 8^4 * 144

# --------------------------------------------------------------- exact Psi
_s = sp.symbols("s", real=True)
_G = (sp.Rational(512, 27) * sp.sqrt(3) * sp.cos(_s + sp.pi / 3) ** 3
      * sp.sin(_s + sp.pi / 3) * sp.cos(_s) * (2 * sp.cos(2 * _s) - 1))
_Gf = sp.expand_trig(sp.expand(_G))
_Psi_sym = sp.expand(sp.integrate(_Gf, _s))
_Psi_sym = _Psi_sym - _Psi_sym.subs(_s, 0)
Psi = sp.lambdify(_s, _Psi_sym, "numpy")
G_np = sp.lambdify(_s, _Gf, "numpy")


def _self_test():
    """Check G(s) against its definition through Lam(w), and Psi against G."""
    ss = np.linspace(0.0, PI6, 977)
    w = 2 * np.sin(ss)
    q = np.sqrt((4 - w * w) / 3.0)
    Lam = (q - np.abs(w)) ** 3 * (3.0 * q + np.abs(w)) / 3.0
    Gdef = Lam * (1 - w * w) * 2 * np.cos(ss)
    err1 = np.max(np.abs(Gdef - G_np(ss)))
    # Psi' = G
    h = 1e-6
    err2 = np.max(np.abs((Psi(ss[1:-1] + h) - Psi(ss[1:-1] - h)) / (2 * h)
                         - G_np(ss[1:-1])))
    return err1, err2


# --------------------------------------------------------- geometry helpers
def s_limits(b, u):
    dstar = b * (3.0 * b * b - u * u) / 48.0
    u3 = u ** 3
    with np.errstate(divide="ignore", over="ignore", invalid="ignore"):
        Rhi = 216.0 * (1.0 - dstar) / u3
        Rlo = 216.0 * (-1.0 - dstar) / u3
    s_hi = np.where(Rhi >= 1.0, PI6, np.arcsin(np.clip(Rhi, -1.0, 1.0)) / 3.0)
    s_lo = np.where(Rlo <= -1.0, -PI6, np.arcsin(np.clip(Rlo, -1.0, 1.0)) / 3.0)
    # |d*| < 5/8 < 1 guarantees R_hi > 0 > R_lo, hence s_lo <= 0 <= s_hi.
    return s_lo, s_hi


def u_kinks(b):
    """u in (0,Umax) where the clipping switches on: R_hi=1 or R_lo=-1."""
    Umax = np.sqrt(9.0 * b * b + 24.0)
    out = []
    for coef in ([1.0, -4.5 * b, 0.0, -216.0 + 13.5 * b ** 3],      # R_hi = 1
                 [1.0, 4.5 * b, 0.0, -216.0 - 13.5 * b ** 3]):      # R_lo = -1
        for r in np.roots(coef):
            if abs(r.imag) < 1e-11 * max(1.0, abs(r.real)):
                rr = r.real
                if 1e-12 < rr < Umax - 1e-12:
                    out.append(rr)
    return sorted(out)


def inner_u_integral(b, nu):
    """Int_0^Umax(b) u^8 [Psi(s_hi)-Psi(s_lo)] du, composite Gauss with panels
    split at the clipping kinks."""
    Umax = np.sqrt(9.0 * b * b + 24.0)
    edges = [0.0] + u_kinks(b) + [Umax]
    xg, wg = leggauss(nu)
    tot = 0.0
    for lo, hi in zip(edges[:-1], edges[1:]):
        if hi - lo < 1e-14:
            continue
        mid, half = 0.5 * (hi + lo), 0.5 * (hi - lo)
        u = mid + half * xg
        sl, sh = s_limits(b, u)
        # G is even and Psi is built from the s>=0 branch, so
        # Int_{s_lo}^{s_hi} G = Psi(s_hi) + Psi(-s_lo)   (s_lo <= 0 <= s_hi always)
        val = u ** 8 * (Psi(sh) + Psi(-sl))
        tot += half * np.dot(wg, val)
    return tot


def b_kinks():
    """b where a clipping curve enters/leaves [0,Umax]: R_hi(Umax)=1 etc."""
    def fhi(b):
        U2 = 9 * b * b + 24
        return U2 ** 1.5 - (216.0 + 4.5 * b * U2 - 13.5 * b ** 3)

    def flo(b):
        U2 = 9 * b * b + 24
        return U2 ** 1.5 - (216.0 - 4.5 * b * U2 + 13.5 * b ** 3)

    ks = []
    grid = np.linspace(-1.0, 1.0, 20001)
    for f in (fhi, flo):
        v = np.array([f(x) for x in grid])
        idx = np.nonzero(np.sign(v[:-1]) * np.sign(v[1:]) < 0)[0]
        for i in idx:
            ks.append(brentq(f, grid[i], grid[i + 1], xtol=1e-15, rtol=1e-15))
    return sorted(ks)


def total(npan_b, nb, nu):
    ks = b_kinks()
    base = [-1.0] + ks + [1.0]
    edges = []
    for lo, hi in zip(base[:-1], base[1:]):
        edges.extend(np.linspace(lo, hi, npan_b + 1)[:-1])
    edges.append(1.0)
    xg, wg = leggauss(nb)
    tot = 0.0
    for lo, hi in zip(edges[:-1], edges[1:]):
        mid, half = 0.5 * (hi + lo), 0.5 * (hi - lo)
        for x, wt in zip(xg, wg):
            tot += half * wt * inner_u_integral(mid + half * x, nu)
    return tot / CONST


if __name__ == "__main__":
    e1, e2 = _self_test()
    print(f"self-test: max|G_formula - G_def| = {e1:.3e}, max|Psi' - G| = {e2:.3e}")
    print("Psi(sigma) =", sp.simplify(_Psi_sym))
    print("b-kinks (clipping onset):", b_kinks())

    res = {}
    print("\n  npan_b  nb  nu        16*P_B                  P_B")
    prev = None
    for npan_b, nb, nu in [(4, 16, 24), (8, 20, 32), (16, 24, 40),
                           (32, 32, 48), (48, 40, 56), (64, 48, 64)]:
        I = total(npan_b, nb, nu)
        PB = I / 16.0
        delta = "" if prev is None else f"   d={PB-prev:+.3e}"
        print(f"  {npan_b:5d} {nb:3d} {nu:3d}   {I:.16f}   {PB:.16f}{delta}")
        res[f"{npan_b}_{nb}_{nu}"] = {"I16": I, "PB": PB}
        prev = PB
    res["PB_final"] = prev
    res["self_test"] = [float(e1), float(e2)]
    res["b_kinks"] = b_kinks()
    with open(os.path.join(ROOT, "results", "quartic_quad.json"), "w") as f:
        json.dump(res, f, indent=2)
    print("\nwrote results/quartic_quad.json")
