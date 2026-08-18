"""Arbitrary-precision Gauss-Legendre nodes/weights, with on-disk caching.

Initial guesses come from scipy (double precision), then Newton-refined against
the mpmath Legendre recurrence to full working precision.
"""
import os
import pickle
from mpmath import mp, mpf

CACHE_DIR = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), ".cache")
os.makedirs(CACHE_DIR, exist_ok=True)

_mem = {}


def _legendre_p_dp(n, x):
    """(P_n(x), P_n'(x)) via the standard three-term recurrence, mp arithmetic."""
    p0 = mpf(1)
    p1 = x
    if n == 0:
        return p0, mpf(0)
    for k in range(2, n + 1):
        p0, p1 = p1, ((2 * k - 1) * x * p1 - (k - 1) * p0) / k
    dp = n * (x * p1 - p0) / (x * x - 1)
    return p1, dp


def gauss_legendre(n, prec=None):
    """Nodes/weights for int_{-1}^{1}.  Returns list of (x, w) as mpf."""
    if prec is None:
        prec = mp.prec
    key = (n, prec)
    if key in _mem:
        return _mem[key]
    fn = os.path.join(CACHE_DIR, f"gl_{n}_{prec}.pkl")
    if os.path.exists(fn):
        with open(fn, "rb") as fh:
            data = pickle.load(fh)
        out = [(mpf(a), mpf(b)) for a, b in data]
        _mem[key] = out
        return out

    from scipy.special import roots_legendre
    xs_dp, _ = roots_legendre(n)

    old = mp.prec
    mp.prec = prec + 30
    out = []
    try:
        for x0 in xs_dp:
            x = mpf(float(x0))
            for _ in range(80):
                p, dp = _legendre_p_dp(n, x)
                dx = p / dp
                x = x - dx
                if abs(dx) < mp.mpf(2) ** (-(prec + 20)):
                    break
            p, dp = _legendre_p_dp(n, x)
            w = 2 / ((1 - x * x) * dp * dp)
            out.append((x, w))
    finally:
        mp.prec = old
    out = [(+x, +w) for x, w in out]  # round to working precision
    with open(fn, "wb") as fh:
        pickle.dump([(mp.nstr(a, mp.dps + 15), mp.nstr(b, mp.dps + 15)) for a, b in out], fh)
    _mem[key] = out
    return out


def panel_nodes(lo, hi, n, prec=None):
    """Nodes/weights mapped onto [lo, hi]."""
    gl = gauss_legendre(n, prec)
    c = (hi + lo) / 2
    h = (hi - lo) / 2
    return [(c + h * x, h * w) for x, w in gl]


if __name__ == "__main__":
    mp.dps = 60
    for n in (8, 32):
        nd = gauss_legendre(n)
        # sanity: sum of weights = 2, and int_{-1}^1 x^{2n-2} dx = 2/(2n-1)
        s = sum(w for _, w in nd)
        m = sum(w * x ** (2 * n - 2) for x, w in nd)
        print(n, mp.nstr(s - 2, 5), mp.nstr(m - mpf(2) / (2 * n - 1), 5))
