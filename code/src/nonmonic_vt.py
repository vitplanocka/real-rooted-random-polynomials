"""ROUTE 1 -- the V(t) route of TASK.md, at high precision.

    P = (1/8) int_0^1 a^3 V(1/a) da,
    V(t) = vol_3{(A,B,C) in [-t,t]^3 : x^3+Ax^2+Bx+C has 3 real roots}.

Key device: the sigma-substitution makes every integrand piecewise POLYNOMIAL,
so the innermost integral is done in closed form and all clipping breakpoints
are roots of explicit cubics (no dense-scan/bisection kink hunting, no loss of
digits at the kinks).

Band (proved in THEOREMS.md S1/S2, re-derived in factored form here).  For
f = a x^3 + b x^2 + c x + d with a > 0 and sigma = sqrt(b^2-3ac) > 0:

    d_hi = P_p(sigma)/u,  P_p = 2 sigma^3 - 3 b sigma^2 + b^3 = (b-sig)^2(b+2sig)
    d_lo = -P_m(sigma)/u, P_m = 2 sigma^3 + 3 b sigma^2 - b^3 = (b+sig)^2(2sig-b)
    u = 27 a^2,           P_p + P_m = 4 sigma^3  (= band width * u)

and for the window [-w, w] (scale u by w):  the clipped overlap length is

    L = max(0, min(P_p, U) + min(P_m, U)) / u   with U = u*w.

Monic case is a = 1 (u = 27), b = A, window w = t, so U = 27 t: that IS V(t):

    V(t) = (4/81) int_0^t dA int_{s_lo}^{s_hi} s * max(0, min(P_p,27t)+min(P_m,27t)) ds
    s_lo = sqrt(max(0, A^2-3t)),  s_hi = sqrt(A^2+3t)

(the factor 2 from (A,C)->(-A,-C); note s_lo > 0 is exactly TASK pitfall 2, the
`min(t, A^2/3)` upper limit on B, here automatic.)

Non-monic, window [-1,1]:  with a in (0,1] and b in [0,1] (both sign symmetries
used, factor 2 each),

    P  = (1/6) int_0^1 (da/a) int_0^1 db int_{s_lo}^{s_hi} s L(s) ds,
    s_lo = sqrt(max(0, b^2-3a)), s_hi = sqrt(b^2+3a),  u = U = 27 a^2,
    p(a) := (1/(6a)) int_0^1 db int s L ds   is P( 3 real roots | leading coef a ),
    and  V(1/a) = 8 p(a) / a^3.

Anchors reproduced through this same code path (see main()):
  * V(1) = 766/1215 + ln(3)/6      (Theorem 1)
  * depressed-cubic anchor 2 sqrt(3)/45
  * p(1) = 383/4860 + ln(3)/48
  * p(0+) = 1/2 + 5/72 + ln(2)/12  (random quadratic limit)

Output: results/nonmonic_quadrature.json
"""
import json
import os
import sys
import time
from multiprocessing import Pool

import numpy as np
import mpmath as mp

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "..", "results", "nonmonic_quadrature.json")

DPS = 40
mp.mp.dps = DPS


# ------------------------------------------------------------------ cubics
def _real_roots_f(c3, c2, c1, c0):
    """real roots of c3 x^3 + c2 x^2 + c1 x + c0 (float, for structure scans)."""
    r = np.roots([c3, c2, c1, c0])
    return sorted(float(z.real) for z in r if abs(z.imag) < 1e-9 * (1 + abs(z)))


def _real_roots_mp(c3, c2, c1, c0):
    """Real roots of a cubic, computed entirely in mp arithmetic.

    Closed-form (trigonometric / Cardano) so that it stays correct when the
    outer quadrature probes a ~ 1e-30 and u = 27a^2 underflows float64 --
    seeding from np.roots there would silently return the wrong roots.
    A couple of Newton steps polish away the cancellation in the formulas.
    """
    A = mp.mpf(c2) / c3
    B = mp.mpf(c1) / c3
    C = mp.mpf(c0) / c3
    p = B - A ** 2 / 3
    q = 2 * A ** 3 / 27 - A * B / 3 + C
    shift = A / 3
    disc = -4 * p ** 3 - 27 * q ** 2          # > 0  <=>  three real roots
    roots = []
    if p < 0 and disc > 0:
        m = 2 * mp.sqrt(-p / 3)
        arg = 3 * q / (p * m)                 # = (3q)/(2p) * sqrt(-3/p)
        arg = max(mp.mpf(-1), min(mp.mpf(1), arg))
        th = mp.acos(arg) / 3
        for k in (0, 1, 2):
            roots.append(m * mp.cos(th - 2 * mp.pi * k / 3) - shift)
    else:
        if p == 0:
            y = mp.cbrt(-q) if q <= 0 else -mp.cbrt(q)
        else:
            s = mp.sqrt(q ** 2 / 4 + p ** 3 / 27)
            u1 = -q / 2 + s
            u2 = -q / 2 - s
            cb = lambda z: mp.cbrt(z) if z >= 0 else -mp.cbrt(-z)
            y = cb(u1) + cb(u2)
        roots.append(y - shift)
    C3, C2, C1, C0 = mp.mpf(c3), mp.mpf(c2), mp.mpf(c1), mp.mpf(c0)
    out = []
    for z in roots:
        for _ in range(50):
            f = ((C3 * z + C2) * z + C1) * z + C0
            df = (3 * C3 * z + 2 * C2) * z + C1
            if df == 0:
                break
            dz = f / df
            z -= dz
            if abs(dz) <= mp.mpf(10) ** (-DPS - 8) * (1 + abs(z)):
                break
        out.append(z)
    return sorted(out)


def breakpoints(b, u, U, s_lo, s_hi, exact=True):
    """sigma-values in (s_lo, s_hi) where the clipping pattern changes.

    Solved in the SHIFTED variable z = sigma - b, in which the cubics are

        P_p = U :  z^2 (3b + 2z) = U      ->  2z^3 + 3b z^2 - U
        P_m = +-U: (2b+z)^2 (b+2z) = +-U  ->  2z^3 + 9b z^2 + 12b^2 z + 4b^3 -+ U

    The unshifted form 2s^3-3bs^2+b^3 = U has a near-double root at s = b whose
    two branches sit only ~sqrt(U/3b) apart; in float64 that is destroyed once
    U << b^3 (i.e. small leading coefficient) and the kink scan then returns
    dozens of phantom breakpoints. The z-form has no such cancellation.
    """
    rr = _real_roots_mp if exact else _real_roots_f
    pts = []
    for coeffs in ((2, 3 * b, 0, -U),
                   (2, 9 * b, 12 * b * b, 4 * b ** 3 - U),
                   (2, 9 * b, 12 * b * b, 4 * b ** 3 + U)):
        for z in rr(*coeffs):
            s = b + z
            if s_lo < s < s_hi:
                pts.append(s)
    return sorted(pts)


# ------------------------------------------------------------------ inner
def _case(b, u, U, s):
    """(clip_hi, clip_lo, is_zero) at sigma = s; factored forms for stability."""
    Pp = (b - s) ** 2 * (b + 2 * s)
    Pm = (b + s) ** 2 * (2 * s - b)
    ch = Pp > U
    cl = Pm > U
    tot = (U if ch else Pp) + (U if cl else Pm)
    return (bool(ch), bool(cl), bool(tot <= 0))


def _panel_integral(b, u, U, x0, x1, case):
    """exact int_{x0}^{x1} s * [min(Pp,U)+min(Pm,U)] / u  ds on one smooth panel."""
    ch, cl, zero = case
    if zero:
        return mp.mpf(0)

    def anti(s):
        # integrand pieces, all polynomial in s
        if ch and cl:
            val = 2 * U * s ** 2 / 2                      # (U+U)*s
        elif ch:      # U + P_m = U + 2s^3+3bs^2-b^3
            val = (U * s ** 2 / 2 + 2 * s ** 5 / 5
                   + 3 * b * s ** 4 / 4 - b ** 3 * s ** 2 / 2)
        elif cl:      # U + P_p = U + 2s^3-3bs^2+b^3
            val = (U * s ** 2 / 2 + 2 * s ** 5 / 5
                   - 3 * b * s ** 4 / 4 + b ** 3 * s ** 2 / 2)
        else:         # P_p + P_m = 4 s^3
            val = 4 * s ** 5 / 5
        return val / u

    return anti(x1) - anti(x0)


def inner_sigma_integral(b, u, U, s_lo, s_hi, exact=True):
    """int_{s_lo}^{s_hi} s * L(s) ds, in closed form on each smooth panel."""
    if s_hi <= s_lo:
        return mp.mpf(0) if exact else 0.0
    pts = [s_lo] + breakpoints(b, u, U, s_lo, s_hi, exact=exact) + [s_hi]
    tot = mp.mpf(0) if exact else 0.0
    for x0, x1 in zip(pts[:-1], pts[1:]):
        if x1 <= x0:
            continue
        mid = (x0 + x1) / 2
        tot += _panel_integral(b, u, U, x0, x1, _case(b, u, U, mid))
    return tot


def case_signature(b, u, U, s_lo, s_hi):
    """float structure fingerprint used to locate kinks of the outer integrand."""
    if s_hi <= s_lo:
        return ("empty",)
    pts = [s_lo] + breakpoints(b, u, U, s_lo, s_hi, exact=False) + [s_hi]
    return tuple(_case(b, u, U, (x0 + x1) / 2)
                 for x0, x1 in zip(pts[:-1], pts[1:]))


# ------------------------------------------------------------------ V(t)
def V_inner_A(A, t, exact=True):
    """int over s at fixed A, for the monic window [-t,t] (a=1, u=27, U=27t)."""
    u = mp.mpf(27) if exact else 27.0
    U = 27 * (mp.mpf(t) if exact else float(t))
    s_lo = mp.sqrt(max(A * A - 3 * t, 0)) if exact else \
        float(np.sqrt(max(A * A - 3 * t, 0.0)))
    s_hi = mp.sqrt(A * A + 3 * t) if exact else float(np.sqrt(A * A + 3 * t))
    return inner_sigma_integral(A, u, U, s_lo, s_hi, exact=exact)


def V_of_t(t, degree=8):
    """V(t) = (4/3) * 2 * int_0^t (int s L ds) dA ... see module docstring:
       V(t) = (4/3) int_0^t [int_{s_lo}^{s_hi} s * (min+min)/27 ds] dA * 2 ... """
    t = mp.mpf(t)
    # locate A-values where the sigma-pattern changes
    cuts = _find_cuts(lambda A: case_signature(
        A, 27.0, 27.0 * float(t), float(np.sqrt(max(A * A - 3 * float(t), 0.0))),
        float(np.sqrt(A * A + 3 * float(t)))), 0.0, float(t))
    tot = mp.mpf(0)
    for x0, x1 in zip(cuts[:-1], cuts[1:]):
        if x1 - x0 < 1e-15:
            continue
        tot += mp.quad(lambda A: V_inner_A(A, t), [mp.mpf(x0), mp.mpf(x1)],
                       maxdegree=degree)
    # 2 (A -> -A sym) * (2/3) (dB = (2s/3) ds)
    return 2 * mp.mpf(2) / 3 * tot


# ------------------------------------------------------------------ p(a)
def _pa_inner_b(a, b, exact=True):
    if exact:
        a = mp.mpf(a)
        b = mp.mpf(b)
        u = 27 * a * a
        s_lo = mp.sqrt(max(b * b - 3 * a, mp.mpf(0)))
        s_hi = mp.sqrt(b * b + 3 * a)
    else:
        u = 27.0 * a * a
        s_lo = float(np.sqrt(max(b * b - 3.0 * a, 0.0)))
        s_hi = float(np.sqrt(b * b + 3.0 * a))
    return inner_sigma_integral(b, u, u, s_lo, s_hi, exact=exact)


def _b_signature(a, b):
    u = 27.0 * a * a
    s_lo = float(np.sqrt(max(b * b - 3.0 * a, 0.0)))
    s_hi = float(np.sqrt(b * b + 3.0 * a))
    return case_signature(b, u, u, s_lo, s_hi)


def _find_cuts(sig_fn, x0, x1, nscan=400, nbis=70, grid=None):
    """split [x0,x1] where the structure fingerprint changes."""
    if grid is None:
        grid = np.linspace(x0, x1, nscan)
    sigs = [sig_fn(g) for g in grid]
    cuts = [x0]
    for i in range(len(grid) - 1):
        if sigs[i] != sigs[i + 1]:
            lo, hi = grid[i], grid[i + 1]
            s0 = sigs[i]
            for _ in range(nbis):
                mid = 0.5 * (lo + hi)
                if sig_fn(mid) == s0:
                    lo = mid
                else:
                    hi = mid
            cuts.append(0.5 * (lo + hi))
    cuts.append(x1)
    return cuts


def _b_grid(nlin=401, nlog=401, lo=1e-14):
    """linear + logarithmic scan grid on [0,1].

    For small `a` the whole b-structure lives near b ~ sqrt(3a), and a purely
    linear scan of 400 points walks straight past it; the resulting missed kinks
    were costing ~1e-9 relative accuracy in p(a) at a = 1e-6.
    """
    return np.unique(np.concatenate([np.linspace(0.0, 1.0, nlin),
                                     np.geomspace(lo, 1.0, nlog)]))


def p_of_a(a, degree=7):
    """P(3 real roots | leading coefficient = a),  a in (0,1]."""
    af = float(a)
    cuts = _find_cuts(lambda b: _b_signature(af, b), 0.0, 1.0, grid=_b_grid())
    # b = sqrt(3a) (where s_lo leaves 0) is an exact structural breakpoint
    if 3.0 * af < 1.0:
        cuts.append(float(np.sqrt(3.0 * af)))
    cuts = sorted(set(cuts))
    tot = mp.mpf(0)
    for x0, x1 in zip(cuts[:-1], cuts[1:]):
        if x1 - x0 < 1e-14:
            continue
        tot += mp.quad(lambda bb: _pa_inner_b(a, bb),
                       [mp.mpf(x0), mp.mpf(x1)], maxdegree=degree)
    return tot / (6 * mp.mpf(a))


# ------------------------------------------------------------------ outer
def _set_prec_for(a):
    """Working precision needed at leading coefficient `a`.

    The sigma-window has width ~3a/b around sigma=b, and the expanded cubics
    P_p = 2s^3-3bs^2+b^3 lose ~ 27a^2/(4b^4) in relative accuracy there, so the
    precision must grow like 2*log10(1/a).  (This is why a plain float pipeline
    silently degrades for small leading coefficients.)
    """
    global DPS
    la = float(mp.log10(a)) if a > 0 else -40.0
    DPS = min(400, 40 + int(2.2 * max(0.0, -la)) + 10)
    mp.mp.dps = DPS
    return DPS


def _pa_worker(args):
    a_str, degree = args
    a = mp.mpf(a_str)
    _set_prec_for(a)
    return mp.nstr(p_of_a(a, degree=degree), 40)


def _pv_worker(args):
    """integrand of  int_0^sqrt(delta) 2 v p(v^2) dv  (a = v^2 substitution)."""
    v_str, degree = args
    v = mp.mpf(v_str)
    a = v * v
    _set_prec_for(a)
    return mp.nstr(2 * v * p_of_a(a, degree=degree), 40)


def outer_nodes(x0, x1, degree, method="gauss-legendre"):
    """(nodes, scale) such that the rule value is scale * sum w f(x).

    mpmath convention (see QuadratureRule.sum_next): Gauss-Legendre nodes at a
    single degree already form a complete rule; tanh-sinh nodes are incremental,
    the degree-m rule being 2^-m times the sum over levels 1..m.
    """
    from mpmath.calculus.quadrature import GaussLegendre, TanhSinh
    prec = mp.mp.prec
    if method == "gauss-legendre":
        q = GaussLegendre(mp.mp)
        return q.get_nodes(mp.mpf(x0), mp.mpf(x1), degree, prec), mp.mpf(1)
    q = TanhSinh(mp.mp)
    nodes = []
    for deg in range(1, degree + 1):
        nodes.extend(q.get_nodes(mp.mpf(x0), mp.mpf(x1), deg, prec))
    return nodes, mp.mpf(2) ** (-degree)


def integrate_parallel(x0, x1, degree, method, pool, inner_degree):
    nodes, scale = outer_nodes(x0, x1, degree, method)
    xs = [mp.nstr(x, 35) for x, w in nodes]
    vals = pool.map(_pa_worker, [(x, inner_degree) for x in xs], chunksize=1)
    tot = mp.mpf(0)
    for (x, w), v in zip(nodes, vals):
        tot += w * mp.mpf(v)
    return tot * scale


def gl_all_degrees(x0, x1, degrees, pool, inner_degree, worker=_pa_worker):
    """Gauss-Legendre values at several degrees (each degree is a full rule)."""
    from mpmath.calculus.quadrature import GaussLegendre
    q = GaussLegendre(mp.mp)
    prec = mp.mp.prec
    out = []
    nev = 0
    for d in degrees:
        nodes = q.get_nodes(mp.mpf(x0), mp.mpf(x1), d, prec)
        vals = pool.map(worker, [(mp.nstr(x, 40), inner_degree)
                                 for x, w in nodes], chunksize=1)
        nev += len(nodes)
        out.append(mp.fsum(w * mp.mpf(v) for (x, w), v in zip(nodes, vals)))
    return out, nev


def panel_all_degrees(x0, x1, max_degree, pool, inner_degree):
    """tanh-sinh values of the panel integral at every degree 1..max_degree.

    The degree-d rule uses the cumulative node set of levels 1..d, so ONE batch
    of function evaluations yields the whole convergence table for free.
    """
    from mpmath.calculus.quadrature import TanhSinh
    q = TanhSinh(mp.mp)
    prec = mp.mp.prec
    levels = [q.get_nodes(mp.mpf(x0), mp.mpf(x1), d, prec)
              for d in range(1, max_degree + 1)]
    flat = [x for lv in levels for (x, w) in lv]
    vals = pool.map(_pa_worker, [(mp.nstr(x, 40), inner_degree) for x in flat],
                    chunksize=1)
    it = iter(vals)
    out = []
    running = mp.mpf(0)
    for d, lv in enumerate(levels, start=1):
        for (x, w) in lv:
            running += w * mp.mpf(next(it))
        out.append(mp.mpf(2) ** (-d) * running)
    return out, len(flat)


def find_a_cuts(lo=1e-3, hi=1.0):
    """multi-resolution structure scan for kinks of p(a) on [lo, hi]."""
    grid = _b_grid(nlin=301, nlog=301)

    def a_sig(a):
        cuts = _find_cuts(lambda b: _b_signature(a, b), 0.0, 1.0, nbis=35,
                          grid=grid)
        return (len(cuts),
                tuple(_b_signature(a, 0.5 * (cuts[i] + cuts[i + 1]))
                      for i in range(len(cuts) - 1)))
    found = [c for c in _find_cuts(a_sig, lo, hi, nscan=501, nbis=45)
             if lo < c < hi]
    found.sort()
    merged = []
    for c in found:
        if not merged or c - merged[-1] > 1e-7:
            merged.append(c)
    return merged


def main():
    t0 = time.time()
    res = {}
    nproc = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    out_deg = int(sys.argv[2]) if len(sys.argv) > 2 else 7
    in_deg = int(sys.argv[3]) if len(sys.argv) > 3 else 7

    # ---------------- anchors -------------------------------------------
    print("=== anchors ===")
    V1 = V_of_t(1)
    V1x = mp.mpf(766) / 1215 + mp.log(3) / 6
    print("V(1)      =", mp.nstr(V1, 30))
    print("exact     =", mp.nstr(V1x, 30))
    print("|diff|    =", mp.nstr(abs(V1 - V1x), 5))
    res["anchor_V1"] = {"computed": mp.nstr(V1, 30), "exact": mp.nstr(V1x, 30),
                        "abs_err": mp.nstr(abs(V1 - V1x), 5)}

    # depressed cubic anchor: A = 0, B in [-1,0], window [-1,1] -> 2 sqrt(3)/45
    # in sigma variables: A=0 => s = sqrt(-3B), B in [-1,0] => s in [0, sqrt 3]
    dep = inner_sigma_integral(mp.mpf(0), mp.mpf(27), mp.mpf(27),
                               mp.mpf(0), mp.sqrt(3)) * mp.mpf(2) / 3 / 4
    depx = 2 * mp.sqrt(3) / 45
    print("depressed =", mp.nstr(dep, 30), " exact", mp.nstr(depx, 30),
          " |diff|", mp.nstr(abs(dep - depx), 5))
    res["anchor_depressed"] = {"computed": mp.nstr(dep, 30),
                               "exact": mp.nstr(depx, 30),
                               "abs_err": mp.nstr(abs(dep - depx), 5)}

    p1 = p_of_a(mp.mpf(1), degree=in_deg)
    p1x = mp.mpf(383) / 4860 + mp.log(3) / 48
    print("p(1)      =", mp.nstr(p1, 30), " exact", mp.nstr(p1x, 30),
          " |diff|", mp.nstr(abs(p1 - p1x), 5))
    res["anchor_p1"] = {"computed": mp.nstr(p1, 30), "exact": mp.nstr(p1x, 30),
                        "abs_err": mp.nstr(abs(p1 - p1x), 5)}
    # V(1) from p(1) through the scaling identity
    res["anchor_V1_from_p1"] = mp.nstr(8 * p1, 30)

    # small-a limit: P(c^2 > 4bd) = 1/2 + 5/72 + ln2/12
    lim = mp.mpf(1) / 2 + mp.mpf(5) / 72 + mp.log(2) / 12
    for aa in ("1e-3", "1e-4", "1e-5"):
        v = p_of_a(mp.mpf(aa), degree=in_deg)
        print(f"p({aa}) = {mp.nstr(v, 20)}   limit {mp.nstr(lim, 20)}"
              f"   diff {mp.nstr(v - lim, 5)}")
        res[f"p_small_{aa}"] = mp.nstr(v, 25)
    res["p_zero_limit_exact"] = mp.nstr(lim, 25)

    # V(t) table (t >= 1, clipping active) + scaling cross-check 8p(1/t)/a^3
    vt = {}
    for t in (1, 1.5, 2, 3, 5, 10):
        a = mp.mpf(1) / mp.mpf(t)
        v_direct = V_of_t(t)
        v_scaled = 8 * p_of_a(a, degree=in_deg) / a ** 3
        vt[str(t)] = {"V_direct": mp.nstr(v_direct, 25),
                      "V_from_p": mp.nstr(v_scaled, 25),
                      "rel_diff": mp.nstr(abs(v_direct - v_scaled)
                                          / abs(v_direct), 5)}
        print(f"V({t}) direct {mp.nstr(v_direct, 22)}  "
              f"via p {mp.nstr(v_scaled, 22)}  "
              f"reldiff {vt[str(t)]['rel_diff']}")
    res["V_of_t_table"] = vt

    # ---------------- the outer integral --------------------------------
    print("=== outer integral over a ===")
    t1 = time.time()
    DELTA = 1e-4          # [0, DELTA] handled by the a = v^2 substitution
    cuts = find_a_cuts(1e-3, 1.0)
    a_cuts = sorted(set([DELTA, 1e-3] + cuts + [1.0]))
    print(f"a-pieces ({len(a_cuts)-1} panels above {DELTA}, "
          f"scan {time.time()-t1:.0f}s):", ["%.10f" % c for c in a_cuts])
    res["a_pieces"] = a_cuts

    with Pool(nproc) as pool:
        # --- the [0, DELTA] head.  p(a) = p(0) - (2/3) sqrt(a) + ... so the
        # integrand is NOT analytic in a at 0 (TASK pitfall 3).  Substituting
        # a = v^2 removes the sqrt and keeps every node away from 0.
        head_degs = [4, 5, 6]
        head_vals, k = gl_all_degrees(0.0, float(np.sqrt(DELTA)), head_degs,
                                      pool, in_deg, worker=_pv_worker)
        nev = k
        for d, v in zip(head_degs, head_vals):
            print(f"  head [0,{DELTA}] GL(v) degree {d}: {mp.nstr(v, 28)}")
        head = head_vals[-1]
        res["head_piece"] = {"delta": DELTA,
                             "gl_v_degrees": {str(d): mp.nstr(v, 30)
                                              for d, v in zip(head_degs,
                                                              head_vals)},
                             "value": mp.nstr(head, 30),
                             "conv": mp.nstr(head_vals[-1] - head_vals[-2], 5)}

        per_panel = []
        for x0, x1 in zip(a_cuts[:-1], a_cuts[1:]):
            if x1 - x0 < 1e-13:
                continue
            vals, k = panel_all_degrees(x0, x1, out_deg, pool, in_deg)
            nev += k
            per_panel.append(((x0, x1), vals))
            print(f"  panel [{x0:.8f},{x1:.8f}] deg{out_deg}="
                  f"{mp.nstr(vals[-1], 25)}  d-1 diff "
                  f"{mp.nstr(vals[-1]-vals[-2], 3)}")
    totals = {}
    for d in range(1, out_deg + 1):
        totals[d] = head + mp.fsum(v[d - 1] for _, v in per_panel)
    for d in sorted(totals):
        print(f"  outer tanh-sinh degree {d}: P = {mp.nstr(totals[d], 30)}")
    P = totals[out_deg]
    conv = abs(totals[out_deg - 1] - totals[out_deg])
    res["P_outer_degree_table"] = {str(k): mp.nstr(v, 30)
                                   for k, v in totals.items()}
    res["P_panels"] = [{"a0": x0, "a1": x1, "value": mp.nstr(v[-1], 30),
                        "deg_doubling_diff": mp.nstr(v[-1] - v[-2], 5)}
                       for (x0, x1), v in per_panel]
    res["n_p_evaluations"] = nev
    res["P"] = mp.nstr(P, 30)
    res["P_node_doubling_diff"] = mp.nstr(conv, 5)

    cand1 = mp.mpf(641) / 2430 - mp.log(3) / 24
    cand2 = mp.mpf("0.217993225")
    res["cand_dxdy"] = mp.nstr(cand1, 30)
    res["P_minus_dxdy"] = mp.nstr(P - cand1, 5)
    res["P_minus_sweep"] = mp.nstr(P - cand2, 5)
    print("P                       =", mp.nstr(P, 25))
    print("641/2430 - ln3/24       =", mp.nstr(cand1, 25))
    print("P - dxdy                =", mp.nstr(P - cand1, 5))
    print("P - sweep(0.217993225)  =", mp.nstr(P - cand2, 5))
    res["elapsed_seconds"] = round(time.time() - t0, 1)
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    with open(OUT, "w") as fh:
        json.dump(res, fh, indent=2)
    print("written", os.path.abspath(OUT), res["elapsed_seconds"], "s")


if __name__ == "__main__":
    main()
