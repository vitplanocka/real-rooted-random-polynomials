r"""High-precision evaluation of

    P_A = P( x^3 + a x^2 + b x + c has 3 distinct real roots ),  (a,b,c) iid N(0,1)

by two structurally different quadratures.

METHOD C  ("coefficient space").  c is independent of (a,b) and standard normal,
and the cubic has 3 distinct real roots iff b < a^2/3 and c_lo < c < c_hi with
27 c_hi = (a-s)^2 (a+2s), 27 c_lo = (a+s)^2 (a-2s), s = sqrt(a^2-3b).  Change
variable b -> s ( b = (a^2-s^2)/3, db = -(2s/3) ds ), which makes the region the
half plane s >= 0 and removes the square-root branch point:

    P = (1/2pi) \int_R da \int_0^inf ds (2s/3) e^{-a^2/2} e^{-((a^2-s^2)/3)^2/2} D(a,s)
    D(a,s) = Phi(c_hi) - Phi(c_lo)

The integrand is even in a (the map (a,b,c)->(-a,b,-c) preserves real-rootedness),
so P = (1/pi) \int_0^inf ... .  Fixed-order Gauss-Legendre panels in both
variables; s-panels are placed at s = sqrt(a^2 + 3k), i.e. uniformly in units of
the standard deviation (=3) of the Gaussian factor in the variable s^2.

METHOD R  ("root space").  Substitute (r1,r2,r3) -> (a,b,c) = (-e1, e2, -e3);
|Jacobian| = |V| = |(r1-r2)(r1-r3)(r2-r3)|; ordered triples biject with cubics
having 3 distinct real roots, so

    P = (1/6) (2pi)^{-3/2} \int_{R^3} exp(-(e1^2+e2^2+e3^2)/2) |V| dr .

Freezing y=r2, z=r3 makes e1^2+e2^2+e3^2 a QUADRATIC in u=r1 and |V| a quadratic
times |y-z|, so the u-integral is closed form (erf + exp).  What is left is a
2-D integral over (y,z), reparametrised by y = mid-d, z = mid+d with mid,d >= 0
(the integrand is symmetric in y<->z and invariant under r -> -r):

    P = (16/6) (2pi)^{-3/2} \int_0^inf \int_0^inf  d * J(mid-d, mid+d)  dd dmid
    J(y,z) = \int_R |(u-y)(u-z)| exp(-Q(u)/2) du ,  Q = A u^2 + B u + C,
    A = 1+p^2+m^2, B = 2p(1+m), C = p^2+m^2, p = y+z, m = yz.
"""
import json
import os
import sys
import time
from multiprocessing import Pool

from mpmath import mp, mpf

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gaussian_cubic_glnodes import panel_nodes  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# ---------------------------------------------------------------------------
# shared numerics
# ---------------------------------------------------------------------------

_CLAMP = 30  # erf(30) = 1 - 1e-393 : safe up to ~380 dps


def _erf(x):
    if x > _CLAMP:
        return mpf(1)
    if x < -_CLAMP:
        return mpf(-1)
    return mp.erf(x)


def _erfc(x):
    if x > _CLAMP:
        return mp.erfc(x)  # genuinely tiny, mpmath handles it
    return mp.erfc(x)


def phi_diff(lo, hi, sq2):
    """Phi(hi) - Phi(lo), evaluated so that no catastrophic cancellation occurs."""
    if lo >= 0:
        return (_erfc(lo / sq2) - _erfc(hi / sq2)) / 2
    if hi <= 0:
        return (_erfc(-hi / sq2) - _erfc(-lo / sq2)) / 2
    return (_erf(hi / sq2) + _erf(-lo / sq2)) / 2


# ---------------------------------------------------------------------------
# METHOD C : coefficient space
# ---------------------------------------------------------------------------

# panel edges in units of the sd (=3) of the Gaussian factor exp(-(s^2-a^2)^2/18)
C_DELTAS = [-26, -18, -12, -7, -4, -2, 0, 2, 4, 7, 12, 18, 26]
C_APANELS = [0, 0.75, 1.5, 2.25, 3, 4, 5, 6.5, 8, 10, 13, 16, 20]
# deliberately different breakpoint set, used as a robustness variant
C_DELTAS_V = [-27, -19, -13.5, -9, -5.5, -3, -1, 1, 3, 5.5, 9, 13.5, 19, 27]
C_APANELS_V = [0, 0.6, 1.2, 1.9, 2.6, 3.4, 4.3, 5.4, 6.8, 8.5, 11, 14, 17, 21]


def _G(a, n_in, deltas):
    """inner integral over s at fixed a"""
    sq2 = mp.sqrt(2)
    a2 = a * a
    vs = sorted({mpf(0)} | {a2 + 3 * mpf(d) for d in deltas if a2 + 3 * mpf(d) > 0})
    edges = [mp.sqrt(v) for v in vs]
    tot = mpf(0)
    for lo, hi in zip(edges[:-1], edges[1:]):
        if hi <= lo:
            continue
        for s, w in panel_nodes(lo, hi, n_in):
            bb = (a2 - s * s) / 3
            chi = (a - s) ** 2 * (a + 2 * s) / 27
            clo = (a + s) ** 2 * (a - 2 * s) / 27
            tot += w * (2 * s / 3) * mp.exp(-bb * bb / 2) * phi_diff(clo, chi, sq2)
    return tot


def _c_panel(args):
    lo, hi, n_out, n_in, deltas, prec = args
    mp.prec = prec
    tot = mpf(0)
    for a, w in panel_nodes(mpf(lo), mpf(hi), n_out):
        tot += w * mp.exp(-a * a / 2) * _G(a, n_in, deltas)
    return +tot


def method_C(dps, n_out, n_in, apanels=None, deltas=None, procs=28):
    mp.dps = dps
    apanels = apanels or C_APANELS
    deltas = deltas or C_DELTAS
    prec = mp.prec
    # warm the node cache in the parent so forked children inherit it
    panel_nodes(mpf(0), mpf(1), n_out)
    panel_nodes(mpf(0), mpf(1), n_in)
    tasks = [(apanels[i], apanels[i + 1], n_out, n_in, deltas, prec)
             for i in range(len(apanels) - 1)]
    with Pool(procs) as pool:
        parts = pool.map(_c_panel, tasks)
    mp.dps = dps
    tot = sum(parts)
    return tot / mp.pi


def method_C_tail_bound(A):
    """|discarded a-tail| <= (1/pi) * int_A^inf e^{-a^2/2} * sup_a G  da,
    and G(a) <= (1/3) int_0^inf exp(-(a^2-v)^2/18) dv <= (1/3) sqrt(18 pi) = sqrt(2 pi).
    Hence bound = (1/pi) sqrt(2pi) * sqrt(2pi) Q(A) = 2 Q(A)."""
    return 2 * mp.ncdf(-mpf(A))


# ---------------------------------------------------------------------------
# METHOD R : root space
# ---------------------------------------------------------------------------

R_PANELS = [0, 0.5, 1.0, 1.5, 2.0, 2.75, 3.5, 4.5, 6.0, 8.0, 11.0, 15.0, 20.0]
R_PANELS_V = [0, 0.4, 0.85, 1.35, 1.9, 2.5, 3.2, 4.0, 5.0, 6.4, 8.2, 10.5, 13.5, 17, 21]


def J_root(y, z, sq2pi, sq2):
    """int_R |(u-y)(u-z)| exp(-Q(u)/2) du   (y <= z)"""
    p = y + z
    m = y * z
    A = 1 + p * p + m * m
    B = 2 * p * (1 + m)
    C = p * p + m * m
    mu = -B / (2 * A)
    sig = 1 / mp.sqrt(A)
    K = mp.exp(-(C - B * B / (4 * A)) / 2)

    q0 = mu * mu - p * mu + m      # g(mu)
    q1 = 2 * mu - p                # g'(mu)

    t1 = (y - mu) / sig
    t2 = (z - mu) / sig
    e1t = mp.exp(-t1 * t1 / 2) if abs(t1) < 1e6 else mpf(0)
    e2t = mp.exp(-t2 * t2 / 2) if abs(t2) < 1e6 else mpf(0)

    def piece(ta, tb, ea, eb):
        """int_{ta}^{tb} g(mu+sig t) e^{-t^2/2} sig dt, with ea=e^{-ta^2/2} etc.
        ta/tb may be -inf/+inf (pass None)."""
        if ta is None:
            dPhi = mp.ncdf(tb)
            E1 = -eb
            T2 = sq2pi * dPhi - tb * eb
        elif tb is None:
            dPhi = mp.ncdf(-ta)
            E1 = ea
            T2 = sq2pi * dPhi + ta * ea
        else:
            dPhi = phi_diff(ta, tb, sq2)
            E1 = ea - eb
            T2 = sq2pi * dPhi + ta * ea - tb * eb
        return sig * (sig * sig * T2 + sig * q1 * E1 + q0 * sq2pi * dPhi)

    left = piece(None, t1, None, e1t)      # g >= 0
    midi = piece(t1, t2, e1t, e2t)         # g <= 0
    right = piece(t2, None, e2t, None)     # g >= 0
    return K * (left - midi + right)


def _r_panel(args):
    mlo, mhi, dlo, dhi, n, prec = args
    mp.prec = prec
    sq2pi = mp.sqrt(2 * mp.pi)
    sq2 = mp.sqrt(2)
    tot = mpf(0)
    mn = panel_nodes(mpf(mlo), mpf(mhi), n)
    dn = panel_nodes(mpf(dlo), mpf(dhi), n)
    for mid, wm in mn:
        sub = mpf(0)
        for d, wd in dn:
            sub += wd * d * J_root(mid - d, mid + d, sq2pi, sq2)
        tot += wm * sub
    return +tot


def method_R(dps, n, panels=None, procs=28):
    mp.dps = dps
    panels = panels or R_PANELS
    prec = mp.prec
    panel_nodes(mpf(0), mpf(1), n)
    tasks = []
    for i in range(len(panels) - 1):
        for j in range(len(panels) - 1):
            tasks.append((panels[i], panels[i + 1], panels[j], panels[j + 1], n, prec))
    with Pool(procs) as pool:
        parts = pool.map(_r_panel, tasks)
    mp.dps = dps
    tot = sum(parts)
    return mpf(16) / 6 * (2 * mp.pi) ** mpf(-1.5) * tot


def method_R_tail_bound(R):
    """Every root of x^3+ax^2+bx+c obeys |x| <= 1 + max(|a|,|b|,|c|) (Cauchy).
    The discarded region has |r2|>R or |r3|>R, hence max_i |r_i| > R, hence
    max(|a|,|b|,|c|) > R-1.  Union bound: <= 6 * Q(R-1)."""
    return 6 * mp.ncdf(-(mpf(R) - 1))


# ---------------------------------------------------------------------------

def digits_agree(x, y):
    d = abs(x - y)
    if d == 0:
        return mp.dps
    return int(mp.floor(-mp.log10(d / abs(x))))


def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--procs", type=int, default=28)
    args = ap.parse_args()

    log = []

    if args.quick:
        c_runs = [(40, 24, 24), (40, 32, 32)]
        r_runs = [(40, 20), (40, 28)]
        c_var = (40, 32, 32)
        r_var = (40, 28)
        WORK = 40
    else:
        c_runs = [(90, 48, 48), (90, 64, 64), (90, 84, 84), (110, 110, 110)]
        r_runs = [(90, 36), (90, 52), (90, 72), (110, 96)]
        c_var = (110, 104, 104)
        r_var = (110, 92)
        WORK = 110

    print("=== METHOD C (coefficient space, (a,s) Gauss-Legendre panels) ===")
    cvals = []
    for dps, n_out, n_in in c_runs:
        t0 = time.time()
        v = method_C(dps, n_out, n_in, procs=args.procs)
        el = time.time() - t0
        mp.dps = dps
        cvals.append(v)
        prev = "" if len(cvals) < 2 else "   d(prev)=%s" % mp.nstr(v - cvals[-2], 5)
        print(f"  dps={dps} n_out={n_out} n_in={n_in}  [{el:.1f}s]")
        print(f"    {mp.nstr(v, dps-6)}{prev}")
        log.append(dict(method="C", variant="main-panels", dps=dps, n_out=n_out,
                        n_in=n_in, value=mp.nstr(v, dps - 4), seconds=round(el, 1)))

    print("\n--- METHOD C, variant panel breakpoints (same reduction, different mesh) ---")
    dps, n_out, n_in = c_var
    t0 = time.time()
    Cv = method_C(dps, n_out, n_in, apanels=C_APANELS_V, deltas=C_DELTAS_V, procs=args.procs)
    el = time.time() - t0
    mp.dps = dps
    print(f"  dps={dps} n_out={n_out} n_in={n_in}  [{el:.1f}s]")
    print(f"    {mp.nstr(Cv, dps-6)}")
    log.append(dict(method="C", variant="variant-panels", dps=dps, n_out=n_out,
                    n_in=n_in, value=mp.nstr(Cv, dps - 4), seconds=round(el, 1)))

    print("\n=== METHOD R (root space, u-integral closed form, (mid,d) GL panels) ===")
    rvals = []
    for dps, n in r_runs:
        t0 = time.time()
        v = method_R(dps, n, procs=args.procs)
        el = time.time() - t0
        mp.dps = dps
        rvals.append(v)
        prev = "" if len(rvals) < 2 else "   d(prev)=%s" % mp.nstr(v - rvals[-2], 5)
        print(f"  dps={dps} n={n}  [{el:.1f}s]")
        print(f"    {mp.nstr(v, dps-6)}{prev}")
        log.append(dict(method="R", variant="main-panels", dps=dps, n=n,
                        value=mp.nstr(v, dps - 4), seconds=round(el, 1)))

    print("\n--- METHOD R, variant panel breakpoints ---")
    dps, n = r_var
    t0 = time.time()
    Rv = method_R(dps, n, panels=R_PANELS_V, procs=args.procs)
    el = time.time() - t0
    mp.dps = dps
    print(f"  dps={dps} n={n}  [{el:.1f}s]")
    print(f"    {mp.nstr(Rv, dps-6)}")
    log.append(dict(method="R", variant="variant-panels", dps=dps, n=n,
                    value=mp.nstr(Rv, dps - 4), seconds=round(el, 1)))

    mp.dps = WORK
    C, R = cvals[-1], rvals[-1]
    pairs = {
        "C(main) vs R(main)": (C, R),
        "C(main) vs C(variant mesh)": (C, Cv),
        "R(main) vs R(variant mesh)": (R, Rv),
        "C(variant) vs R(variant)": (Cv, Rv),
        "C self-convergence (last two n)": (cvals[-1], cvals[-2]),
        "R self-convergence (last two n)": (rvals[-1], rvals[-2]),
    }
    print("\n=== agreement table (matching significant decimal digits) ===")
    agree = {}
    for k, (x, y) in pairs.items():
        agree[k] = digits_agree(x, y)
        print(f"  {k:34s} : {agree[k]:3d} digits   diff = {mp.nstr(x - y, 6)}")

    tbC = method_C_tail_bound(C_APANELS[-1])
    tbR = method_R_tail_bound(R_PANELS[-1])
    print(f"\n  method C truncation bound (|a|>{C_APANELS[-1]}) : {mp.nstr(tbC, 5)}")
    print(f"  method R truncation bound (|r|>{R_PANELS[-1]}) : {mp.nstr(tbR, 5)}")

    # consensus value: digits common to C(main), R(main), C(var), R(var)
    vals = [C, R, Cv, Rv]
    spread = max(vals) - min(vals)
    common = digits_agree(C, C + spread) if spread else WORK
    print(f"\n  spread over all four high-order runs = {mp.nstr(spread, 6)}")
    print(f"  => digits common to all four: {common}")
    print(f"\n  P_A = {mp.nstr(C, 50)}")

    results = dict(
        constant="P(x^3+a x^2+b x+c has 3 distinct real roots), (a,b,c) iid N(0,1)",
        runs=log,
        method_C_final=mp.nstr(C, WORK - 6),
        method_R_final=mp.nstr(R, WORK - 6),
        method_C_variant=mp.nstr(Cv, WORK - 6),
        method_R_variant=mp.nstr(Rv, WORK - 6),
        pairwise_differences={k: mp.nstr(x - y, 6) for k, (x, y) in pairs.items()},
        pairwise_agreeing_digits=agree,
        spread_all_four=mp.nstr(spread, 6),
        digits_common_to_all_four=common,
        truncation_bound_C=mp.nstr(tbC, 5),
        truncation_bound_R=mp.nstr(tbR, 5),
        truncation_radius_C=C_APANELS[-1],
        truncation_radius_R=R_PANELS[-1],
    )
    os.makedirs(os.path.join(ROOT, "results"), exist_ok=True)
    with open(os.path.join(ROOT, "results", "gaussian_cubic_quad.json"), "w") as fh:
        json.dump(results, fh, indent=2)
    print("\nwrote results/gaussian_cubic_quad.json")


if __name__ == "__main__":
    main()
