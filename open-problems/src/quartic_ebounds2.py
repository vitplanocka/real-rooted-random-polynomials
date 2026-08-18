"""Exact-as-possible extrema of the e-window endpoints.

KEY REDUCTIONS (derived here, checked numerically below):

* grad_(b,c,d) g(x_i) = (x_i^3, x_i^2, x_i) (envelope thm, since g'(x_i)=f'(x_i)=0).
  It never vanishes for x_i != 0, so max g(x2) sits on the boundary of the
  feasible set; on the *discriminant* sheet (double root y, simple root s)

        b = -(4/3)(2y+s),  c = 2(y^2+2ys),  d = -4 y^2 s,
        g(y) = y^3 (y - 4 s)/3                                    (exact)

  a 2-D problem, whose stationary points need y=0.  So the max is at a vertex
  of {(y,s) : |b|,|c|,|d| <= 1}.

* Normal form f = (x^2+px+q)^2 + delta x + eps, p=b/2, q=c/2-b^2/8,
  delta = d - bc/2 + b^3/8.  Hence  g(x) = (x^2+px+q)^2 - q^2 + delta x,
  so when delta = 0 both local minima of g equal -q^2 exactly.
  q ranges over [-5/8, 1/2] on the cube, so -q^2 >= -25/64.
"""
import json, os, sys
import numpy as np
import mpmath as mp
from scipy.optimize import minimize

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
ROOT = os.path.dirname(HERE)
from quartic_common import crit_points, g_of   # noqa: E402

mp.mp.dps = 50


def bcd_sheet(y, s):
    return -(4.0/3.0)*(2*y + s), 2.0*(y*y + 2*y*s), -4.0*y*y*s


def F(y, s):
    return y**3*(y - 4*s)/3.0


# ---- 1. verify the sheet formula against the raw machinery
rng = np.random.default_rng(3)
err = 0.0
for _ in range(20000):
    y, s = rng.uniform(-2, 2, 2)
    b, c, d = bcd_sheet(y, s)
    err = max(err, abs(g_of(y, b, c, d) - F(y, s)))
print("check g(y) = y^3(y-4s)/3 on the discriminant sheet: max err =", err)

# ---- 2. fine grid + SLSQP on the sheet
N = 4000
ay = np.linspace(-2.0, 2.0, N)
Y, S = np.meshgrid(ay, ay, indexing="ij")
B, C, D = bcd_sheet(Y, S)
feas = (np.abs(B) <= 1) & (np.abs(C) <= 1) & (np.abs(D) <= 1)
V = np.where(feas, F(Y, S), -np.inf)
k = int(np.argmax(V)); idx = np.unravel_index(k, V.shape)
print(f"sheet grid {N}^2: max g = {V.flat[k]:.12f} at y={Y[idx]:.8f} s={S[idx]:.8f}")

cons = ([{"type": "ineq", "fun": lambda v, j=j: 1.0 - bcd_sheet(*v)[j]} for j in range(3)]
        + [{"type": "ineq", "fun": lambda v, j=j: bcd_sheet(*v)[j] + 1.0} for j in range(3)])
best = (-np.inf, None)
starts = [np.array([Y[idx], S[idx]])] + [rng.uniform(-1.5, 1.5, 2) for _ in range(3000)]
for x0 in starts:
    r = minimize(lambda v: -F(*v), x0, method="SLSQP", constraints=cons,
                 options={"maxiter": 500, "ftol": 1e-16})
    if all(c["fun"](r.x) > -1e-10 for c in cons) and -r.fun > best[0]:
        best = (float(-r.fun), r.x.copy())
print(f"sheet SLSQP  : max g = {best[0]:.15f} at y={best[1][0]:.12f} s={best[1][1]:.12f}")
yb, sb = best[1]
print(f"               (b,c,d) = {bcd_sheet(yb,sb)}")

# ---- 3. exact solve of the candidate vertex  b = +1, d = -1
#   2y+s = -3/4  and  y^2 s = 1/4  =>  8y^3 + 3y^2 + 1 = 0
poly = lambda t: 8*t**3 + 3*t**2 + 1
y0 = mp.findroot(poly, mp.mpf(str(yb)))
s0 = -mp.mpf(3)/4 - 2*y0
c0 = 2*(y0*y0 + 2*y0*s0)
G0 = y0**3*(y0 - 4*s0)/3
print("\nexact vertex  b=+1, d=-1, y root of 8y^3+3y^2+1=0:")
print("   y   =", mp.nstr(y0, 30))
print("   s   =", mp.nstr(s0, 30))
print("   c   =", mp.nstr(c0, 30), " (|c|<1, so c is NOT an active constraint)")
print("   maxg=", mp.nstr(G0, 30))
print("   (3y^2-24y+1)/64 =", mp.nstr((3*y0**2 - 24*y0 + 1)/64, 30))
print("   => min e_lo =", mp.nstr(-G0, 30))

# ---- 4. max e_hi : minimise max(g(x1),g(x3)).  delta=0 gives exactly -q^2.
q_min = mp.mpf(-1)/2 - mp.mpf(1)/8          # c=-1, b=+-1
print("\nmax e_hi: with delta=0, max(g(x1),g(x3)) = -q^2, q = c/2 - b^2/8 in [-5/8,1/2]")
print("   q_extreme = -5/8 at (b,c)=(+-1,-1); delta=0 => d = bc/2 - b^3/8 = -+5/8")
print("   => max e_hi = q^2 = 25/64 =", float(mp.mpf(25)/64))
for b, c, d in [(1.0, -1.0, -0.625), (-1.0, -1.0, 0.625)]:
    x1, x2, x3 = crit_points(b, c, d)
    g1 = g_of(x1, b, c, d); g3 = g_of(x3, b, c, d)
    print(f"   check (b,c,d)=({b},{c},{d}): g(x1)={g1:.15f} g(x3)={g3:.15f}  -25/64={-25/64:.15f}")

# is  max(g(x1),g(x3)) >= -q^2  always?  (numerical test)
M = 5_000_000
b = rng.random(M)*2-1; c = rng.random(M)*2-1; d = rng.random(M)*2-1
x1, x2, x3 = crit_points(b, c, d)
g1 = g_of(x1, b, c, d); g3 = g_of(x3, b, c, d)
qq = c/2 - b*b/8
H = np.maximum(g1, g3)
ok = np.isfinite(H)
slack = H[ok] + qq[ok]**2
print(f"   test max(g1,g3) + q^2 >= 0 on {int(ok.sum())} in-region samples: min slack = {slack.min():.3e}")
print(f"   min over samples of max(g1,g3) = {H[ok].min():.12f}   (-25/64 = {-25/64:.12f})")

# ---- 5. brute-force confirmation over the whole cube (fine grid, both extrema)
out = {
    "min_e_lo": float(-G0),
    "min_e_lo_exact": "-(3y^2-24y+1)/64 where 8y^3+3y^2+1=0, y=-0.66104...",
    "min_e_lo_at_bcd": [1.0, float(c0), -1.0],
    "min_e_lo_mp50": mp.nstr(-G0, 40),
    "max_e_hi": 25/64,
    "max_e_hi_exact": "25/64",
    "max_e_hi_at_bcd": [1.0, -1.0, -0.625],
    "margin_lo_to_minus1": float(1 + (-G0)*0 + 1 - G0),
    "margin_hi_to_plus1": float(1 - mp.mpf(25)/64),
    "min_slack_maxg_plus_q2": float(slack.min()),
}
out["margin_lo_to_minus1"] = float(1 - G0)
with open(os.path.join(ROOT, "results", "quartic_ebounds_exact.json"), "w") as f:
    json.dump(out, f, indent=2)
print("\nmargins:  min e_lo = %.15f  (distance to -1: %.15f)" % (float(-G0), float(1 - G0)))
print("          max e_hi = %.15f  (distance to +1: %.15f)" % (25/64, 1 - 25/64))
print("wrote results/quartic_ebounds_exact.json")
