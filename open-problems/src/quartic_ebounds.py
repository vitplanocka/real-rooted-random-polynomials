"""True extrema of the admissible e-window endpoints over the closed region

    R = { (b,c,d) in [-1,1]^3 : f'(x)=4x^3+3bx^2+2cx+d has 3 real roots x1<=x2<=x3 }

    e_lo = -g(x2),   e_hi = -max(g(x1),g(x3)),   g(x)=x^4+bx^3+cx^2+dx.

We need   min e_lo = -max_R g(x2)   and   max e_hi = -min_R max(g(x1),g(x3)).

Structural facts used (envelope theorem; g'(x_i)=f'(x_i)=0):
    grad_(b,c,d) g(x_i) = (x_i^3, x_i^2, x_i) = x_i (x_i^2, x_i, 1).
So grad g(x2) vanishes only at x2=0 (where g(x2)=0), hence max_R g(x2) > 0 is
attained on the boundary of R -- and the same argument on each cube face/edge
shows it cannot be in the relative interior of a face or an edge either, so it
sits on the discriminant surface (x1=x2 or x2=x3) or at a cube corner.
Likewise no interior stationary point of max(g(x1),g(x3)).

Strategy: (i) dense deterministic grid over the cube, (ii) SLSQP refinement in
the root parametrisation x1<=x2<=x3 with the cube as constraints, from many
starts, (iii) explicit search on the discriminant surface f'=4(x-r)^2(x-t).
"""
import json, os, sys
import numpy as np
from scipy.optimize import minimize, brentq

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
ROOT = os.path.dirname(HERE)
from quartic_common import crit_points, g_of   # noqa: E402


# ---------------------------------------------------------------- (i) grid
def grid_scan(n=500, chunk=40):
    ax = np.linspace(-1.0, 1.0, n)
    bestG = (-np.inf, None); bestH = (np.inf, None)
    for i0 in range(0, n, chunk):
        bb = ax[i0:i0 + chunk]
        B, C, D = np.meshgrid(bb, ax, ax, indexing="ij")
        x1, x2, x3 = crit_points(B, C, D)
        g1 = g_of(x1, B, C, D); g2 = g_of(x2, B, C, D); g3 = g_of(x3, B, C, D)
        G = np.where(np.isfinite(g2), g2, -np.inf)
        H = np.where(np.isfinite(g2), np.maximum(g1, g3), np.inf)
        k = int(np.argmax(G))
        if G.flat[k] > bestG[0]:
            idx = np.unravel_index(k, G.shape)
            bestG = (float(G.flat[k]), (float(B[idx]), float(C[idx]), float(D[idx])))
        k = int(np.argmin(H))
        if H.flat[k] < bestH[0]:
            idx = np.unravel_index(k, H.shape)
            bestH = (float(H.flat[k]), (float(B[idx]), float(C[idx]), float(D[idx])))
    return bestG, bestH


# ------------------------------------------- root parametrisation + SLSQP
def bcd(x):
    x1, x2, x3 = x
    e1 = x1 + x2 + x3
    e2 = x1*x2 + x1*x3 + x2*x3
    e3 = x1*x2*x3
    return -4.0*e1/3.0, 2.0*e2, -4.0*e3


def gx(xi, x):
    b, c, d = bcd(x)
    return (((xi + b)*xi + c)*xi + d)*xi


CONS = [{"type": "ineq", "fun": lambda x, j=j, s=s: s*(1.0 - s*bcd(x)[j])}
        for j in range(3) for s in (1.0,)]
CONS = ([{"type": "ineq", "fun": lambda x, j=j: 1.0 - bcd(x)[j]} for j in range(3)]
        + [{"type": "ineq", "fun": lambda x, j=j: bcd(x)[j] + 1.0} for j in range(3)]
        + [{"type": "ineq", "fun": lambda x: x[1] - x[0]},
           {"type": "ineq", "fun": lambda x: x[2] - x[1]}])


def refine(obj, starts):
    best = (np.inf, None)
    for x0 in starts:
        try:
            r = minimize(obj, x0, method="SLSQP", constraints=CONS,
                         options={"maxiter": 800, "ftol": 1e-16})
        except Exception:
            continue
        if r.success or r.status in (0, 9):
            v = obj(r.x)
            ok = all(c["fun"](r.x) > -1e-9 for c in CONS)
            if ok and v < best[0]:
                best = (float(v), r.x.copy())
    return best


def negG(x):  return -gx(x[1], x)                       # maximise g(x2)
def Hfun(x):  return max(gx(x[0], x), gx(x[2], x))      # minimise max(g1,g3)


if __name__ == "__main__":
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 500
    (Gv, Gat), (Hv, Hat) = grid_scan(n)
    print(f"grid {n}^3:  max g(x2) = {Gv:.12f} at {Gat}")
    print(f"           min max(g1,g3) = {Hv:.12f} at {Hat}")

    rng = np.random.default_rng(7)
    starts = []
    for at in (Gat, Hat):
        x = np.sort(np.array(crit_points(*at)))
        starts.append(x)
    for _ in range(500):
        v = np.sort(rng.uniform(-1.6, 1.6, 3))
        b, c, d = bcd(v)
        if max(abs(b), abs(c), abs(d)) <= 1.0:
            starts.append(v)
    print(f"{len(starts)} feasible starts")

    vG, xG = refine(negG, starts)
    vH, xH = refine(Hfun, starts)
    bG = bcd(xG); bH = bcd(xH)
    maxG = -vG
    minH = vH
    print("\n== max g(x2) ==")
    print(f"  value        = {maxG:.15f}   =>  min e_lo = {-maxG:.15f}")
    print(f"  roots x1,x2,x3 = {xG}")
    print(f"  (b,c,d)      = {bG}")
    print(f"  gap to -1 in e_lo: {-maxG - (-1.0):.12f}")
    print("\n== min max(g(x1),g(x3)) ==")
    print(f"  value        = {minH:.15f}   =>  max e_hi = {-minH:.15f}")
    print(f"  roots x1,x2,x3 = {xH}")
    print(f"  (b,c,d)      = {bH}")
    print(f"  gap to +1 in e_hi: {1.0 - (-minH):.12f}")

    # ---- dense scan of the discriminant surface f' = 4(x-r)(x-y)^2 (x2=x3=y)
    #      and f' = 4(x-y)^2(x-t) (x1=x2=y), where the max must live.
    print("\n== discriminant-surface scan ==")
    NN = 3000
    for tag in ("x2=x3", "x1=x2"):
        aa = np.linspace(-3.0, 3.0, NN)
        R, Y = np.meshgrid(aa, aa, indexing="ij")
        if tag == "x2=x3":
            e1 = R + 2*Y; e2 = 2*R*Y + Y*Y; e3 = R*Y*Y; xs = Y
        else:
            e1 = 2*Y + R; e2 = Y*Y + 2*Y*R; e3 = Y*Y*R; xs = Y
        B = -4*e1/3.0; C = 2*e2; D = -4*e3
        feas = (np.abs(B) <= 1) & (np.abs(C) <= 1) & (np.abs(D) <= 1)
        gv = (((xs + B)*xs + C)*xs + D)*xs
        gv = np.where(feas, gv, -np.inf)
        k = int(np.argmax(gv)); idx = np.unravel_index(k, gv.shape)
        print(f"   {tag}: max g(merged/x2) = {gv.flat[k]:.12f} at r={R[idx]:.6f} y={Y[idx]:.6f}"
              f"  (b,c,d)=({B[idx]:.6f},{C[idx]:.6f},{D[idx]:.6f})")

    # ---- corners of the cube, for completeness
    print("\n== cube corners with 3 real critical points ==")
    for b in (-1, 1):
        for c in (-1, 1):
            for d in (-1, 1):
                x1, x2, x3 = crit_points(float(b), float(c), float(d))
                if np.isfinite(x1):
                    g1 = g_of(x1, b, c, d); g2 = g_of(x2, b, c, d); g3 = g_of(x3, b, c, d)
                    print(f"   ({b:+d},{c:+d},{d:+d}): g(x2)={g2:+.9f}  max(g1,g3)={max(g1,g3):+.9f}")

    out = {"grid_n": n,
           "max_g_x2": maxG, "min_e_lo": -maxG, "argmax_bcd": list(map(float, bG)),
           "argmax_roots": list(map(float, xG)),
           "min_max_g1g3": minH, "max_e_hi": -minH, "argmin_bcd": list(map(float, bH)),
           "argmin_roots": list(map(float, xH)),
           "margin_lo": 1.0 - maxG, "margin_hi": 1.0 + minH}
    with open(os.path.join(ROOT, "results", "quartic_ebounds.json"), "w") as f:
        json.dump(out, f, indent=2)
    print("\nwrote results/quartic_ebounds.json")
