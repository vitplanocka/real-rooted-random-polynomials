"""Double-precision sanity checks for the Problem A reduction.

(1) Confirm  c_lo < c < c_hi  <=>  numpy.roots gives 3 distinct real roots.
(2) Crude double-precision evaluation of the 2-D integral, should land near 0.1700.
"""
import numpy as np
from scipy import integrate
from scipy.special import ndtr

rng = np.random.default_rng(20260818)


def band(a, b):
    """Return (ok, c_lo, c_hi) with ok = (b < a^2/3)."""
    disc = a * a - 3.0 * b
    ok = disc > 0.0
    s = np.sqrt(np.where(ok, disc, 0.0))
    c_hi = (a - s) ** 2 * (a + 2 * s) / 27.0
    c_lo = (a + s) ** 2 * (a - 2 * s) / 27.0
    return ok, c_lo, c_hi


# ---------------------------------------------------------------- check (1)
def check_band_vs_roots(n=200000):
    a, b, c = rng.standard_normal((3, n))
    ok, clo, chi = band(a, b)
    pred = ok & (clo < c) & (c < chi)

    actual = np.empty(n, dtype=bool)
    for i in range(n):
        r = np.roots([1.0, a[i], b[i], c[i]])
        # three real roots, all distinct
        actual[i] = np.all(np.abs(r.imag) < 1e-9 * (1.0 + np.abs(r.real)))

    mism = np.nonzero(pred != actual)[0]
    # For mismatches, look at how close to the boundary they are (numerical ties)
    info = []
    for i in mism[:20]:
        d = min(abs(c[i] - clo[i]), abs(c[i] - chi[i])) if ok[i] else abs(a[i] ** 2 / 3 - b[i])
        info.append((float(a[i]), float(b[i]), float(c[i]), bool(pred[i]), bool(actual[i]), float(d)))
    return n, int(mism.size), info, float(pred.mean()), float(actual.mean())


# ---------------------------------------------------------------- check (2)
def crude_integral():
    """P = (1/pi) int_0^inf e^{-a^2/2} [ int_0^inf (2s/3) e^{-b^2/2} D ds ] da
    with b = (a^2-s^2)/3, D = Phi(c_hi)-Phi(c_lo).  (integrand even in a)"""

    def inner(s, a):
        b = (a * a - s * s) / 3.0
        c_hi = (a - s) ** 2 * (a + 2 * s) / 27.0
        c_lo = (a + s) ** 2 * (a - 2 * s) / 27.0
        return (2 * s / 3.0) * np.exp(-(b * b) / 2.0) * (ndtr(c_hi) - ndtr(c_lo))

    def outer(a):
        pts = sorted({0.0, max(a - 6.0, 0.0), a, a + 6.0})
        tot = 0.0
        for lo, hi in zip(pts[:-1], pts[1:]):
            tot += integrate.quad(inner, lo, hi, args=(a,), limit=200,
                                  epsabs=1e-13, epsrel=1e-13)[0]
        tot += integrate.quad(inner, pts[-1], np.inf, args=(a,), limit=200,
                              epsabs=1e-13, epsrel=1e-13)[0]
        return np.exp(-a * a / 2.0) * tot

    val, err = integrate.quad(outer, 0.0, 16.0, limit=400, epsabs=1e-13, epsrel=1e-13)
    return val / np.pi, err / np.pi


# a totally independent crude check: plain 2-D dblquad in (a,b)
def crude_dblquad():
    def f(b, a):
        s = np.sqrt(a * a - 3.0 * b)
        c_hi = (a - s) ** 2 * (a + 2 * s) / 27.0
        c_lo = (a + s) ** 2 * (a - 2 * s) / 27.0
        return np.exp(-(a * a + b * b) / 2.0) * (ndtr(c_hi) - ndtr(c_lo))

    val, err = integrate.dblquad(f, -12, 12, lambda a: -12, lambda a: a * a / 3.0,
                                 epsabs=1e-12, epsrel=1e-12)
    return val / (2 * np.pi), err / (2 * np.pi)


if __name__ == "__main__":
    n, nmis, info, pm, am = check_band_vs_roots()
    print(f"[check 1] n={n}  mismatches={nmis}  pred_rate={pm:.6f}  roots_rate={am:.6f}")
    for row in info:
        print("   mismatch a,b,c=%.6g,%.6g,%.6g pred=%s roots=%s dist_to_boundary=%.3g" % row)

    v, e = crude_integral()
    print(f"[check 2a] (a,s) nested quad  P = {v!r}   (reported err {e:.2e})")
    v2, e2 = crude_dblquad()
    print(f"[check 2b] dblquad in (a,b)   P = {v2!r}   (reported err {e2:.2e})")
    print(f"[check 2] difference = {v - v2:.3e}")
    print(f"[prior MC] 0.169962 +- 4.2e-5 ; deviation 2a = {(v-0.169962)/4.2e-5:+.2f} sigma")
