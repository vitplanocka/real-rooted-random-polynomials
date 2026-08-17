"""ROUTE 1b -- the leading-coefficient (V(t)) route with the a-integral in
closed form.  This is the same integral as src/nonmonic_vt.py evaluates by
nested quadrature, reorganised so that no step is numerically fragile.

Starting point (identical to nonmonic_vt.py, both sign symmetries used):

    P = (1/6) int_0^1 (da/a) int_0^1 db int_{s_lo}^{s_hi} sigma L dsigma

with L = max(0, min(K_p,u) + min(K_m,u))/u,  u = 27 a^2,
     K_p = (b-sig)^2 (b+2 sig) >= 0,  K_m = (b+sig)^2 (2 sig - b),
     K_p + K_m = 4 sig^3,  s_lo = sqrt(max(0,b^2-3a)),  s_hi = sqrt(b^2+3a).

Swap the order: for fixed (b, sigma) the constraint |c| <= 1, i.e.
|sigma^2 - b^2| <= 3a, means a runs over [a0, 1] with a0 = |sigma^2-b^2|/3, and
sigma runs over [0, sqrt(b^2+3)].  Since `a` enters ONLY through u = 27a^2, the
inner integral is elementary:

    P = (1/6) int_0^1 db int_0^{sqrt(b^2+3)} sigma G(b,sigma) dsigma,
    G = int_{a0}^1 L/a da.

With alpha_X = sqrt(X/27) (the a at which the band edge X stops being clipped):

  sigma >= b/2  (K_m >= 0):   G = h(K_p) + h(K_m),
        h(X) = ln(m/a0) + (X/54)(1/m^2 - 1),   m = min(max(alpha_X, a0), 1)
  sigma <  b/2  (K_m  < 0):   M = -K_m,  beta = sqrt(M/27) < alpha_p,
        G = [ln(x1/x0) + M/(54 x1^2) - M/(54 x0^2)]   over [max(a0,beta), min(1,alpha_p)]
          + (2 sigma^3/27)(1/x0^2 - 1)                over [max(a0,alpha_p), 1]

Every evaluation is a handful of sqrt/log: no root finding, no nested
quadrature, no small-a cancellation.  G has an integrable log singularity only
on the curve sigma = b (there a0 = 0: the band covers the whole window for every
small a), which is put at a panel endpoint where tanh-sinh handles it.

Breakpoints in sigma are located by bisecting an exact regime signature (cheap,
since G costs microseconds), so panel edges sit on the kinks rather than near
them.

Anchor: the same code with the b-integrand restricted reproduces p(a) and V(1).

Output: results/route1_closed_a.json
"""
import json
import os
import sys
import time
from multiprocessing import Pool

import numpy as np
import mpmath as mp

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "..", "results", "route1_closed_a.json")

DPS = 40
mp.mp.dps = DPS


# ------------------------------------------------------------------ G
def _h(X, a0, ctx):
    """int_{a0}^1 [1/a if a < sqrt(X/27) else X/(27 a^3)] da,  X >= 0."""
    alpha = ctx.sqrt(X / 27)
    m = alpha
    if m < a0:
        m = a0
    if m > 1:
        m = ctx.mpf(1) if ctx is mp else 1.0
    return ctx.log(m / a0) + (X / 54) * (1 / m ** 2 - 1)


def G(b, s, ctx=mp):
    """int_{a0}^1 L(a;b,s)/a da, in closed form."""
    one = ctx.mpf(1) if ctx is mp else 1.0
    Kp = (b - s) ** 2 * (b + 2 * s)
    Km = (b + s) ** 2 * (2 * s - b)
    # a0 = |s^2-b^2|/3 written factored: the expanded form rounds to exactly 0
    # once s is within a relative working-precision epsilon of b, and tanh-sinh
    # puts nodes exactly that close to the sigma = b panel endpoint -- which
    # turned the whole integral into +inf.
    a0 = abs(s - b) * (s + b) / 3
    if a0 <= 0:
        # sigma has rounded exactly onto b.  G ~ 2 ln(1/a0) diverges only
        # logarithmically there and the quadrature weight at such a node is
        # ~2^-prec, so flooring a0 at the smallest representable scale is
        # harmless -- whereas returning inf poisons the whole sum.
        a0 = (ctx.mpf(2) ** (-2 * ctx.mp.prec) if ctx is mp
              else np.float64(1e-300))
    if Km >= 0:
        return _h(Kp, a0, ctx) + _h(Km, a0, ctx)
    M = -Km
    beta = ctx.sqrt(M / 27)
    alp = ctx.sqrt(Kp / 27)
    tot = one * 0
    # segment where the top is clipped but the band still pokes into [-1,1]
    x0, x1 = max(a0, beta), min(one, alp)
    if x1 > x0:
        tot += ctx.log(x1 / x0) + M / (54 * x1 ** 2) - M / (54 * x0 ** 2)
    # segment where nothing is clipped
    x0 = max(a0, alp)
    if one > x0:
        tot += (2 * s ** 3 / 27) * (1 / x0 ** 2 - 1)
    return tot


def regime(b, s):
    """float regime fingerprint of G (which branch every clamp takes)."""
    Kp = (b - s) ** 2 * (b + 2 * s)
    Km = (b + s) ** 2 * (2 * s - b)
    a0 = abs(s * s - b * b) / 3.0
    if Km >= 0:
        out = [1]
        for X in (Kp, Km):
            al = np.sqrt(X / 27)
            out.append(0 if al < a0 else (2 if al > 1 else 1))
        return tuple(out)
    beta = np.sqrt(-Km / 27)
    alp = np.sqrt(Kp / 27)
    return (0, int(beta > a0), int(beta > 1), int(alp > a0), int(alp > 1))


# ------------------------------------------------------------------ panels
def clean_panels(pts, tol):
    """Sorted panel list keeping BOTH endpoints exactly and dropping interior
    cut points that sit within `tol` of a neighbour.

    Dropping the *point* (rather than skipping the resulting sliver interval, as
    an `if x1-x0 < tol: continue` guard does) matters: a spurious cut at
    1 - 2.2e-16 -- one ulp below the endpoint, which the b-scan does produce --
    otherwise removes that sliver from the integral entirely and biases P by
    I(1)*2.2e-16/6 = 7.4e-17, i.e. exactly three significant digits.
    """
    pts = sorted(pts)
    out = [pts[0]]
    for p in pts[1:-1]:
        if p - out[-1] > tol and pts[-1] - p > tol:
            out.append(p)
    out.append(pts[-1])
    return out


def _bisect_change(f, x0, x1, s0, n=90):
    for _ in range(n):
        xm = 0.5 * (x0 + x1)
        if f(xm) == s0:
            x0 = xm
        else:
            x1 = xm
    return 0.5 * (x0 + x1)


def sigma_cuts(b, s_hi, nscan=4000):
    grid = np.unique(np.concatenate([
        np.linspace(1e-15, s_hi, nscan),
        np.geomspace(1e-12, s_hi, nscan // 2)]))
    sig = [regime(b, s) for s in grid]
    cuts = []
    for i in range(len(grid) - 1):
        if sig[i] != sig[i + 1]:
            cuts.append(_bisect_change(lambda x: regime(b, x), grid[i],
                                       grid[i + 1], sig[i]))
    cuts.append(b)                      # log singularity of G on sigma = b
    cuts = [c for c in cuts if 0 < c < s_hi]
    return sorted(set(cuts))


def inner_b(b, degree=8):
    """int_0^{sqrt(b^2+3)} sigma G(b,sigma) dsigma  at fixed b.

    The panel endpoints sigma = b and sigma = sqrt(b^2+3) are kept in FULL mp
    precision.  G has a log singularity exactly on sigma = b, so rounding that
    endpoint to float leaves the singularity ~1e-17 INSIDE a panel, where
    tanh-sinh no longer resolves it; that alone biased P by ~7e-17.
    """
    b = mp.mpf(b)
    bf = float(b)
    s_hi = mp.sqrt(b * b + 3)
    s_hi_f = float(s_hi)
    raw = [c for c in sigma_cuts(bf, s_hi_f) if abs(c - bf) > 1e-11 * (1 + bf)]
    pts = clean_panels([mp.mpf(0)] + [mp.mpf(c) for c in raw] + [b, s_hi],
                       mp.mpf("1e-13"))
    tot = mp.mpf(0)
    for x0, x1 in zip(pts[:-1], pts[1:]):
        tot += mp.quad(lambda s: s * G(b, s), [x0, x1], maxdegree=degree)
    return tot


def _worker(args):
    b_str, degree, dps = args
    mp.mp.dps = dps
    return mp.nstr(inner_b(mp.mpf(b_str), degree=degree), dps - 3)


def b_regime(b, nscan=1200):
    return tuple(sigma_cuts(b, float(np.sqrt(b * b + 3.0)), nscan=nscan)
                 .__len__() for _ in (0,))


def b_cuts(nscan=1500):
    """kinks of the b-integrand: where the sigma-regime layout changes."""
    grid = np.linspace(1e-9, 1.0, nscan)
    sig = []
    for b in grid:
        cs = sigma_cuts(b, float(np.sqrt(b * b + 3.0)), nscan=800)
        sig.append((len(cs), tuple(regime(b, 0.5 * (u + v))
                                   for u, v in zip([0.0] + cs,
                                                   cs + [float(np.sqrt(b * b + 3))]))))
    cuts = []
    for i in range(len(grid) - 1):
        if sig[i] != sig[i + 1]:
            cuts.append(_bisect_change(
                lambda x: (lambda cs: (len(cs), tuple(
                    regime(x, 0.5 * (u + v)) for u, v in zip(
                        [0.0] + cs, cs + [float(np.sqrt(x * x + 3))]))))(
                    sigma_cuts(x, float(np.sqrt(x * x + 3.0)), nscan=800)),
                grid[i], grid[i + 1], sig[i], n=60))
    return sorted(c for c in cuts if 0 < c < 1)


# ------------------------------------------------------------------ main
def main():
    nproc = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    dps = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    mp.mp.dps = dps
    t0 = time.time()
    res = {"dps": dps}

    print("locating b-kinks ...", flush=True)
    cuts = b_cuts()
    panels = clean_panels([0.0] + list(cuts) + [1.0], 1e-9)
    print(f"  {len(panels)-1} b-panels: "
          f"{['%.10f' % c for c in panels]}", flush=True)
    res["b_panels"] = [float(c) for c in panels]

    from mpmath.calculus.quadrature import GaussLegendre, TanhSinh
    gl = GaussLegendre(mp.mp)
    ts = TanhSinh(mp.mp)
    prec = mp.mp.prec

    totals = {}
    with Pool(nproc) as pool:
        for method, degrees in (("gauss-legendre", (5, 6, 7)),
                                ("tanh-sinh", (5, 6))):
            for deg in degrees:
                tot = mp.mpf(0)
                for x0, x1 in zip(panels[:-1], panels[1:]):
                    if method == "gauss-legendre":
                        nodes = gl.get_nodes(mp.mpf(x0), mp.mpf(x1), deg, prec)
                        scale = mp.mpf(1)
                    else:
                        nodes = []
                        for d in range(1, deg + 1):
                            nodes.extend(ts.get_nodes(mp.mpf(x0), mp.mpf(x1),
                                                      d, prec))
                        scale = mp.mpf(2) ** (-deg)
                    vals = pool.map(_worker, [(mp.nstr(x, dps), 8, dps)
                                              for x, w in nodes], chunksize=4)
                    tot += scale * mp.fsum(w * mp.mpf(v)
                                           for (x, w), v in zip(nodes, vals))
                P = tot / 6
                totals[f"{method}_deg{deg}"] = P
                print(f"  {method:15s} degree {deg}: P = {mp.nstr(P, dps-4)}"
                      f"   ({time.time()-t0:.0f}s)", flush=True)

    res["P_by_method"] = {k: mp.nstr(v, dps - 4) for k, v in totals.items()}
    P = totals["tanh-sinh_deg6"]
    exact = mp.mpf(641) / 2430 - mp.log(3) / 24
    sweep = mp.mpf("0.217993225")
    res["P"] = mp.nstr(P, dps - 4)
    res["exact_641_2430_minus_log3_24"] = mp.nstr(exact, dps - 4)
    res["P_minus_exact"] = mp.nstr(P - exact, 6)
    res["P_minus_sweep"] = mp.nstr(P - sweep, 6)
    res["method_spread"] = mp.nstr(
        max(abs(a - b) for a in totals.values() for b in totals.values()), 6)
    res["elapsed_seconds"] = round(time.time() - t0, 1)
    print("P             =", mp.nstr(P, dps - 4))
    print("641/2430-ln3/24 =", mp.nstr(exact, dps - 4))
    print("P - exact     =", mp.nstr(P - exact, 6))
    print("P - sweep     =", mp.nstr(P - sweep, 6))
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    with open(OUT, "w") as fh:
        json.dump(res, fh, indent=2)
    print("written", os.path.abspath(OUT))


if __name__ == "__main__":
    main()
