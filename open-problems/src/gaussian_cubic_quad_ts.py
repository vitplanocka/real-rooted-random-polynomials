r"""METHOD T -- third, deliberately code-disjoint check on P_A.

Methods C and R in gaussian_cubic_quad.py share one piece of machinery: my own
Gauss-Legendre node generator (gaussian_cubic_glnodes.py).  A bug there would
touch both.  This script recomputes the same coefficient-space integral using
ONLY mpmath's own quadrature (its native tanh-sinh for the inner s-integral and
its native Gauss-Legendre for the outer a-integral), so it shares no numerical
code with C or R beyond mpmath itself.

    P = (1/pi) \int_0^inf e^{-a^2/2} G(a) da,
    G(a) = \int_0^inf (2s/3) exp(-((a^2-s^2)/3)^2/2) (Phi(c_hi) - Phi(c_lo)) ds
"""
import json
import os
import sys
import time
from multiprocessing import Pool

from mpmath import mp, mpf

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

APANELS = [0, 0.8, 1.6, 2.4, 3.2, 4.2, 5.4, 7.0, 9.0, 11.5, 15.0, 20.0]
DELTAS = (-26, -16, -9, -4, 0, 4, 9, 16, 26)


def _D(a, s, sq2):
    chi = (a - s) ** 2 * (a + 2 * s) / 27
    clo = (a + s) ** 2 * (a - 2 * s) / 27
    if clo >= 0:
        return (mp.erfc(clo / sq2) - mp.erfc(chi / sq2)) / 2
    if chi <= 0:
        return (mp.erfc(-chi / sq2) - mp.erfc(-clo / sq2)) / 2
    return (mp.erf(chi / sq2) + mp.erf(-clo / sq2)) / 2


def _G(a, deg_in, sq2):
    a2 = a * a
    f = lambda s: (2 * s / 3) * mp.exp(-((a2 - s * s) / 3) ** 2 / 2) * _D(a, s, sq2)
    vs = sorted({mpf(0)} | {a2 + 3 * mpf(d) for d in DELTAS if a2 + 3 * mpf(d) > 0})
    return mp.quad(f, [mp.sqrt(v) for v in vs], method="tanh-sinh", maxdegree=deg_in)


def _panel(args):
    lo, hi, prec, deg_in, deg_out = args
    mp.prec = prec
    sq2 = mp.sqrt(2)
    F = lambda a: mp.exp(-a * a / 2) * _G(a, deg_in, sq2)
    return +mp.quad(F, [mpf(lo), mpf(hi)], method="gauss-legendre", maxdegree=deg_out)


def method_T(dps, deg_in, deg_out, procs=12):
    mp.dps = dps
    prec = mp.prec
    tasks = [(APANELS[i], APANELS[i + 1], prec, deg_in, deg_out)
             for i in range(len(APANELS) - 1)]
    with Pool(procs) as pool:
        parts = pool.map(_panel, tasks)
    mp.dps = dps
    return sum(parts) / mp.pi


if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--procs", type=int, default=12)
    ap.add_argument("--dps", type=int, default=45)
    args = ap.parse_args()

    mp.dps = args.dps  # must precede parsing ref, or it is truncated to 15 digits
    ref = mpf("0.16992938262347950265644315713176190213405726145463153153274197075706879103307417918893")
    out = []
    for deg_in, deg_out in [(6, 4), (7, 5), (8, 6)]:
        t0 = time.time()
        v = method_T(args.dps, deg_in, deg_out, args.procs)
        el = time.time() - t0
        mp.dps = args.dps
        d = v - ref
        dig = int(mp.floor(-mp.log10(abs(d) / v))) if d != 0 else args.dps
        print(f"  deg_in={deg_in} deg_out={deg_out} [{el:.0f}s]")
        print(f"    {mp.nstr(v, args.dps - 3)}")
        print(f"    T - C(150) = {mp.nstr(d, 6)}   -> {dig} agreeing digits")
        out.append(dict(deg_in=deg_in, deg_out=deg_out, dps=args.dps,
                        value=mp.nstr(v, args.dps - 3), diff_vs_C=mp.nstr(d, 6),
                        agreeing_digits=dig, seconds=round(el, 1)))
        sys.stdout.flush()

    with open(os.path.join(ROOT, "results", "gaussian_cubic_quad_ts.json"), "w") as fh:
        json.dump(dict(
            method=("METHOD T: coefficient space, mpmath-native tanh-sinh (inner) + "
                    "mpmath-native Gauss-Legendre (outer); shares no numerical code "
                    "with methods C and R"),
            reference_value_method_C=mp.nstr(ref, 86),
            runs=out), fh, indent=2)
    print("wrote results/gaussian_cubic_quad_ts.json")
