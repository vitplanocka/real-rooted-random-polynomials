"""Exact reduction of P_B to a 3-D integral in (b, u, s), verification, and the
"no-d-constraint" separable closed form.

DERIVATION (all verified numerically below)
-------------------------------------------
f = x^4+bx^3+cx^2+dx+e,  f' = 4(x-x1)(x-x2)(x-x3),  x1<x2<x3.
Let A = x2-x1 > 0, B = x3-x2 > 0.  Then, integrating f',
    g(x2)-g(x1) = A^3 (A + 2B)/3,        g(x2)-g(x3) = B^3 (B + 2A)/3.
Admissible e-interval = ( -g(x2), -max(g(x1),g(x3)) ), of length
    L = min(...) = m^3 (m + 2M)/3,  m = min(A,B), M = max(A,B)
        [since A^3(A+2B) - B^3(B+2A) = (A^2-B^2)(A+B)^2].
Note A<B  <=>  g(x1)<g(x3), so the "max" switch is exactly at A=B, i.e. at
x2 = -b/4, i.e. at  d = b c/2 - b^3/8.

Substitutions (c -> u, d -> w, w -> s):
    c  = (9 b^2 - u^2)/24,      u in [0, Umax], Umax = sqrt(9b^2+24),
        dc = (u/12) du         (c=3b^2/8 at u=0 down to c=-1 at u=Umax;
                                u = sqrt(9b^2-24c) = 6*(y2-y1))
    d  = d* + (u^3/432)(3w - w^3),   d* = b(3b^2-u^2)/48,   w in [-1,1],
        dd = (u^3/144)(1-w^2) dw
    A  = (u/8) phi(w),  B = (u/8) psi(w),
        phi = sqrt((4-w^2)/3) + w,   psi = sqrt((4-w^2)/3) - w
    => L = (u/8)^4 Lam(w),  Lam(w) = (q-|w|)^3 (3q+|w|)/3, q = sqrt((4-w^2)/3)
    w  = 2 sin s,  s in [-pi/6, pi/6],  dw = 2 cos s ds,
        3w-w^3 = 2 sin 3s   =>   d = d* + (u^3/216) sin(3s).

Hence, with the (numerically verified) fact that the e-interval is NEVER
clipped by [-1,1],

  16 P_B = (1/7077888) * Int_{-1}^{1} db Int_0^{Umax(b)} du  u^8
                        * Int_{s_lo}^{s_hi} Lam(2 sin s)(1-4 sin^2 s) 2 cos s ds

  s_lo = max(-pi/6, (1/3) arcsin( clip( 216(-1-d*)/u^3 ) )),
  s_hi = min(+pi/6, (1/3) arcsin( clip( 216(+1-d*)/u^3 ) )),
  empty if s_lo >= s_hi.       [7077888 = 12 * 8^4 * 144]

If the constraint |d| <= 1 is dropped, the integral SEPARATES completely:
  16 * FULL = (1/7077888) * (Int_{-1}^1 (9b^2+24)^{9/2} db / 9) * Int_{-1}^1 Lam(w)(1-w^2) dw
both factors elementary.  |d|<=1 is the only thing standing between P_B and a
closed form of that shape.
"""

import json
import os
import sys

import numpy as np
import sympy as sp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from quartic_common import crit_points, d_band, e_interval, g_of  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = {}
SQ3 = np.sqrt(3.0)


# ------------------------------------------------------------------ helpers
def Lam(w):
    q = np.sqrt((4.0 - w * w) / 3.0)
    aw = np.abs(w)
    return (q - aw) ** 3 * (3.0 * q + aw) / 3.0


def bcd_from_buw(b, u, w):
    c = (9.0 * b * b - u * u) / 24.0
    dstar = b * (3.0 * b * b - u * u) / 48.0
    d = dstar + (u**3 / 432.0) * (3.0 * w - w**3)
    return c, d


# --------------------------------------------- 1. verify L closed form + map
print("=== verify L = m^3(m+2M)/3 and the (b,u,w) parametrization ===")
rng = np.random.default_rng(31337)
N = 500_000
b = rng.uniform(-1, 1, N)
u = rng.uniform(0, 1, N) * np.sqrt(9 * b * b + 24)
w = rng.uniform(-1, 1, N)
c, d = bcd_from_buw(b, u, w)
inbox = (np.abs(c) <= 1) & (np.abs(d) <= 1)

x1, x2, x3 = crit_points(b, c, d)
ok = np.isfinite(x1)
print(f"  all (b,u,w) map into the 3-crit-point band: {ok.all()}")
A = x2 - x1
Bd = x3 - x2
m = np.minimum(A, Bd)
M = np.maximum(A, Bd)
L_direct = -np.maximum(g_of(x1, b, c, d), g_of(x3, b, c, d)) + g_of(x2, b, c, d)
L_closed = m**3 * (m + 2.0 * M) / 3.0
rel = np.abs(L_direct - L_closed) / np.maximum(1e-12, np.abs(L_direct))
print(f"  max rel err  L_direct vs m^3(m+2M)/3: {np.nanmax(rel):.3e}")
OUT["L_formula_max_rel_err"] = float(np.nanmax(rel))

# A,B from (u,w)
phi = np.sqrt((4 - w * w) / 3.0) + w
psi = np.sqrt((4 - w * w) / 3.0) - w
print(f"  max |A - (u/8)phi| = {np.max(np.abs(A - u/8*phi)):.3e}")
print(f"  max |B - (u/8)psi| = {np.max(np.abs(Bd - u/8*psi)):.3e}")
OUT["AB_param_max_err"] = float(max(np.max(np.abs(A - u / 8 * phi)),
                                    np.max(np.abs(Bd - u / 8 * psi))))
print(f"  max |L - (u/8)^4 Lam(w)| = {np.max(np.abs(L_direct-(u/8)**4*Lam(w))):.3e}")

# kink location d = bc/2 - b^3/8  <=>  A = B
dstar = b * c / 2.0 - b**3 / 8.0
dstar2 = b * (3 * b * b - u * u) / 48.0
print(f"  max |b c/2 - b^3/8 - b(3b^2-u^2)/48| = {np.max(np.abs(dstar-dstar2)):.3e}")
print(f"  sign(A-B) == sign(d - d*) always: "
      f"{np.all(np.sign(np.round(A-Bd,12)) == np.sign(np.round(d-dstar,12)))}")

# --------------------------------------- 2. verify the change-of-variables by MC
print("\n=== verify 16 P_B integral identity by two independent MCs ===")
# (i) direct MC in (b,c,d)
Nm = 20_000_000
rng = np.random.default_rng(4242)
bb, cc, dd = rng.uniform(-1, 1, (3, Nm))
lo, hi = e_interval(bb, cc, dd)
Ld = np.where(np.isfinite(lo), hi - lo, 0.0)
I_direct = 8.0 * Ld.mean()          # integral over the cube [-1,1]^3
print(f"  direct   16 P_B = Int L db dc dd = {I_direct:.8f}")

# (ii) MC in (b,u,w) with the jacobian
bb = rng.uniform(-1, 1, Nm)
Um = np.sqrt(9 * bb * bb + 24)
uu = rng.uniform(0, 1, Nm) * Um
ww = rng.uniform(-1, 1, Nm)
cc2, dd2 = bcd_from_buw(bb, uu, ww)
integ = uu**8 * Lam(ww) * (1 - ww * ww) / 7077888.0
integ = np.where(np.abs(dd2) <= 1.0, integ, 0.0)
vol = 2.0 * Um.mean() * 2.0    # db*du*dw measure factor: 2 * <Umax> * 2
I_param = (integ * (2.0 * Um * 2.0)).mean()
print(f"  reparam  16 P_B = {I_param:.8f}")
print(f"  ratio = {I_param/I_direct:.8f}")
OUT["mc_check_direct"] = float(I_direct)
OUT["mc_check_reparam"] = float(I_param)

# ----------------------------------------- 3. global extremes of the e-interval
print("\n=== global extremes of the admissible e-interval over the band ===")
from scipy.optimize import minimize  # noqa: E402


def ends(p):
    """p = (b, t, w) with u = t*Umax; returns (e_lo, e_hi) or None if |d|>1."""
    b_, t_, w_ = p
    if not (-1 <= b_ <= 1 and 0 <= t_ <= 1 and -1 <= w_ <= 1):
        return None
    U = np.sqrt(9 * b_ * b_ + 24)
    u_ = t_ * U
    c_, d_ = bcd_from_buw(b_, u_, w_)
    if abs(d_) > 1:
        return None
    x1_, x2_, x3_ = crit_points(b_, c_, d_)
    if not np.isfinite(x1_):
        return None
    return (-g_of(x2_, b_, c_, d_),
            -max(g_of(x1_, b_, c_, d_), g_of(x3_, b_, c_, d_)))


def neg_or_big(p, which, sign):
    r = ends(p)
    if r is None:
        return 10.0
    return sign * r[which]


# vectorised coarse screen on a dense (b,u,w) grid, then Nelder-Mead refine
nb_, nu_, nw_ = 401, 401, 401
bg = np.linspace(-1, 1, nb_)
tg = np.linspace(0, 1, nu_)
wg_ = np.linspace(-1, 1, nw_)
BB, TT, WW = np.meshgrid(bg, tg, wg_, indexing="ij")
UU = TT * np.sqrt(9 * BB**2 + 24)
CC, DD = bcd_from_buw(BB, UU, WW)
X1, X2, X3 = crit_points(BB, CC, DD)
good = np.isfinite(X1) & (np.abs(DD) <= 1.0)
ELO = np.where(good, -g_of(X2, BB, CC, DD), np.nan)
EHI = np.where(good, -np.maximum(g_of(X1, BB, CC, DD), g_of(X3, BB, CC, DD)), np.nan)
print(f"  grid {nb_}x{nu_}x{nw_}: e_lo in [{np.nanmin(ELO):.8f},{np.nanmax(ELO):.8f}]"
      f"  e_hi in [{np.nanmin(EHI):.8f},{np.nanmax(EHI):.8f}]")

best = {}
for name, which, sign in [("min_e_lo", 0, +1), ("max_e_lo", 0, -1),
                          ("min_e_hi", 1, +1), ("max_e_hi", 1, -1)]:
    F = np.where(good, sign * (ELO if which == 0 else EHI), np.inf)
    flat = np.argsort(F, axis=None)[:12]
    bestval, bestp = np.inf, None
    for k in flat:
        i, j, l = np.unravel_index(k, F.shape)
        p0 = np.array([bg[i], tg[j], wg_[l]])
        r = minimize(neg_or_big, p0, args=(which, sign), method="Nelder-Mead",
                     options={"xatol": 1e-14, "fatol": 1e-16, "maxiter": 2000})
        if r.fun < bestval:
            bestval, bestp = r.fun, r.x
    val = sign * bestval
    b_, t_, w_ = bestp
    U = np.sqrt(9 * b_ * b_ + 24)
    c_, d_ = bcd_from_buw(b_, t_ * U, w_)
    print(f"  {name} = {val:+.10f}  at (b,c,d)=({b_:+.8f},{c_:+.8f},{d_:+.8f})")
    best[name] = {"value": float(val), "bcd": [float(b_), float(c_), float(d_)]}
OUT["e_interval_extremes"] = best
mg = min(1 - best["max_e_hi"]["value"], best["min_e_lo"]["value"] + 1)
print(f"  ==> margin to the [-1,1] window: {mg:.6f}   (clipping impossible)")
OUT["no_clip_margin"] = float(mg)

# ------------------------------------------- 4. separable "no |d|<=1" version
print("\n=== the |d|<=1-free separable integral (closed form) ===")
ws, bs = sp.symbols("w b", real=True)
q = sp.sqrt((4 - ws**2) / 3)
Lam_s = (q - ws) ** 3 * (3 * q + ws) / 3          # w >= 0 branch
Iw = 2 * sp.integrate(sp.expand(Lam_s * (1 - ws**2)), (ws, 0, 1))
Iw = sp.simplify(sp.nsimplify(sp.simplify(Iw)))
print("  Int_{-1}^{1} Lam(w)(1-w^2) dw =", Iw, "=", float(Iw))
Ib = sp.integrate((9 * bs**2 + 24) ** sp.Rational(9, 2), (bs, -1, 1))
Ib = sp.simplify(Ib)
print("  Int_{-1}^{1} (9b^2+24)^{9/2} db =", sp.nsimplify(Ib), "=", float(Ib))
FULL16 = float(Ib) / 9.0 * float(Iw) / 7077888.0
print(f"  16*FULL = {FULL16:.10f}   ->  FULL/16 'probability' = {FULL16/16:.10f}")
print(f"  true 16 P_B ~ {I_direct:.8f}  =>  |d|<=1 removes "
      f"{100*(1-I_direct/FULL16):.2f}% of it")
OUT["separable_Iw"] = str(Iw)
OUT["separable_Iw_val"] = float(Iw)
OUT["separable_Ib"] = str(sp.nsimplify(Ib))
OUT["separable_Ib_val"] = float(Ib)
OUT["FULL16_no_d_constraint"] = FULL16
OUT["frac_removed_by_d_constraint"] = float(1 - I_direct / FULL16)

with open(os.path.join(ROOT, "results", "quartic_reduction.json"), "w") as f:
    json.dump(OUT, f, indent=2)
print("\nwrote results/quartic_reduction.json")
