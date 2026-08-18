"""INDEPENDENT quadrature for P_B, done in the raw (b,c,d) variables with the
critical points obtained by numerically solving the cubic f'=0.

  16 P_B = Int_{-1}^1 db Int_{-1}^{3b^2/8} dc Int_{d_lo v -1}^{d_hi ^ 1} L dd

  L = g(x2) - max(g(x1),g(x3)),  x1<x2<x3 roots of 4x^3+3bx^2+2cx+d.

Shares no algebra with quartic_quad.py beyond the cubic solver: no reduction to
(u,s), no Lam, no Psi, no Jacobians.  Inner integral is split at the kink
d* = bc/2 - b^3/8 (where g(x1)=g(x3)) and uses scipy.quad, which copes with the
(d-d_lo)^{3/2} endpoint behaviour.
"""

import json
import os
import sys

import numpy as np
from scipy.integrate import quad

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from quartic_common import crit_points, d_band, g_of  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def L_of(d, b, c):
    x1, x2, x3 = crit_points(b, c, d)
    if not np.isfinite(x1):
        return 0.0
    return float(g_of(x2, b, c, d)
                 - max(g_of(x1, b, c, d), g_of(x3, b, c, d)))


def inner_d(c, b, tol):      # c first: scipy.quad passes the integration var first
    dl, dh = d_band(b, c)
    if not np.isfinite(dl):
        return 0.0
    lo = max(-1.0, float(dl))
    hi = min(1.0, float(dh))
    if hi <= lo:
        return 0.0
    dstar = b * c / 2.0 - b ** 3 / 8.0
    pts = [lo, hi] if not (lo < dstar < hi) else [lo, dstar, hi]
    tot = 0.0
    for a, z in zip(pts[:-1], pts[1:]):
        tot += quad(L_of, a, z, args=(b, c), epsabs=tol, epsrel=tol, limit=200)[0]
    return tot


def mid_c(b, tol):
    return quad(inner_d, -1.0, 3.0 * b * b / 8.0, args=(b, tol),
                epsabs=tol, epsrel=tol, limit=200)[0]


if __name__ == "__main__":
    tol = float(sys.argv[1]) if len(sys.argv) > 1 else 1e-10
    # kinks in b where the d-band starts poking outside [-1,1]
    bk = 0.6143021014162962
    tot = 0.0
    for a, z in [(-1.0, -bk), (-bk, 0.0), (0.0, bk), (bk, 1.0)]:
        v, err = quad(mid_c, a, z, args=(tol,), epsabs=tol, epsrel=tol, limit=200)
        print(f"  b in [{a:+.6f},{z:+.6f}] -> {v:.14f}  (quad err est {err:.1e})")
        tot += v
    print(f"\n16 P_B = {tot:.15f}")
    print(f"   P_B = {tot/16:.15f}")
    with open(os.path.join(ROOT, "results", "quartic_quad_direct.json"), "w") as f:
        json.dump({"tol": tol, "I16": tot, "PB": tot / 16.0}, f, indent=2)
