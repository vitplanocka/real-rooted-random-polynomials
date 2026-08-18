"""Common vectorized machinery for the quartic 4-distinct-real-roots problem.

f(x) = x^4 + b x^3 + c x^2 + d x + e,   (b,c,d,e) iid U[-1,1].

Key structure (see quartic_structure.py for validation):
  f'(x) = 4x^3 + 3b x^2 + 2c x + d.
  f has 4 distinct real roots
    iff f' has 3 distinct real roots x1<x2<x3 (min, max, min of f)
        and f(x1)<0, f(x2)>0, f(x3)<0.
  Writing g(x) = x^4 + b x^3 + c x^2 + d x  (so f = g + e), the critical
  points do not depend on e, hence the admissible e-set is the OPEN INTERVAL
        -g(x2)  <  e  <  -max(g(x1), g(x3)),
  which is always nonempty (x2 is a local max of g).
"""

import numpy as np

# ----------------------------------------------------------------------------
# Cubic f'(x)=0  <=>  x^3 + A x^2 + B x + C = 0 with A=3b/4, B=c/2, C=d/4.
# Three distinct real roots iff  B < A^2/3  and  C strictly between C_lo, C_hi:
#     s = sqrt(A^2 - 3B),  27 C_hi = (A-s)^2 (A+2s),  27 C_lo = (A+s)^2 (A-2s).
# In terms of (b,c,d):  s = sqrt(9b^2/16 - 3c/2)  requires c < 3b^2/8,
#     and d/4 in (C_lo, C_hi).
# ----------------------------------------------------------------------------


def d_band(b, c):
    """Return (d_lo, d_hi): open interval of d for which f' has 3 distinct real
    roots, at given (b,c).  Returns (nan,nan) where c >= 3b^2/8."""
    b = np.asarray(b, dtype=float)
    c = np.asarray(c, dtype=float)
    A = 0.75 * b
    B = 0.5 * c
    disc = A * A - 3.0 * B
    ok = disc > 0.0
    s = np.sqrt(np.where(ok, disc, 0.0))
    C_hi = (A - s) ** 2 * (A + 2 * s) / 27.0
    C_lo = (A + s) ** 2 * (A - 2 * s) / 27.0
    d_lo = np.where(ok, 4.0 * C_lo, np.nan)
    d_hi = np.where(ok, 4.0 * C_hi, np.nan)
    return d_lo, d_hi


def crit_points(b, c, d):
    """Three real critical points x1<=x2<=x3 of f (roots of 4x^3+3bx^2+2cx+d).

    Uses the trigonometric (casus irreducibilis) formula; valid where the cubic
    has three real roots.  Where it does not, results are nan.
    Returns (x1, x2, x3) sorted ascending.
    """
    b = np.asarray(b, dtype=float)
    c = np.asarray(c, dtype=float)
    d = np.asarray(d, dtype=float)
    A = 0.75 * b
    B = 0.5 * c
    C = 0.25 * d
    # depressed: t^3 + p t + q,  x = t - A/3
    p = B - A * A / 3.0
    q = 2.0 * A**3 / 27.0 - A * B / 3.0 + C
    neg_p = -p
    pos = neg_p > 0.0
    r = np.sqrt(np.where(pos, neg_p / 3.0, 1.0))       # = sqrt(-p/3)
    # cos(theta) = 3q / (2 p r)
    with np.errstate(invalid="ignore", divide="ignore"):
        arg = np.where(pos, 3.0 * q / (2.0 * p * r), 2.0)
    # three distinct real roots  <=>  p < 0 AND |arg| < 1  (<=> 4p^3+27q^2 < 0)
    ok = pos & (np.abs(arg) <= 1.0)
    theta = np.arccos(np.clip(np.where(ok, arg, 0.0), -1.0, 1.0))
    k = np.arange(3).reshape((3,) + (1,) * np.ndim(theta))
    t = 2.0 * r * np.cos(theta / 3.0 - 2.0 * np.pi * k / 3.0)
    x = t - A / 3.0
    x = np.sort(x, axis=0)
    bad = ~ok
    if np.ndim(bad) == 0:
        if bad:
            x = np.full_like(x, np.nan)
    else:
        x = np.where(bad, np.nan, x)
    return x[0], x[1], x[2]


def g_of(x, b, c, d):
    """g(x) = x^4 + b x^3 + c x^2 + d x  (Horner)."""
    return (((x + b) * x + c) * x + d) * x


def e_interval(b, c, d):
    """Unclipped admissible e-interval (e_lo, e_hi) = (-g(x2), -max(g(x1),g(x3))).

    nan where f' lacks 3 distinct real roots.
    """
    x1, x2, x3 = crit_points(b, c, d)
    g1 = g_of(x1, b, c, d)
    g2 = g_of(x2, b, c, d)
    g3 = g_of(x3, b, c, d)
    return -g2, -np.maximum(g1, g3)


def e_length_clipped(b, c, d):
    """Length of admissible e-set intersected with [-1,1]."""
    lo, hi = e_interval(b, c, d)
    L = np.minimum(hi, 1.0) - np.maximum(lo, -1.0)
    L = np.where(np.isfinite(L), L, 0.0)
    return np.maximum(L, 0.0)


# ----------------------------------------------------------------------------
# Sign characterization (Delta > 0, P < 0, D < 0)
# ----------------------------------------------------------------------------


def quartic_discriminant(b, c, d, e):
    """Discriminant of x^4 + b x^3 + c x^2 + d x + e (from sympy, expanded)."""
    b2 = b * b
    b3 = b2 * b
    b4 = b2 * b2
    c2 = c * c
    c3 = c2 * c
    d2 = d * d
    e2 = e * e
    return (
        256.0 * e**3
        - 192.0 * b * d * e2
        - 128.0 * c2 * e2
        + 144.0 * c * d2 * e
        - 27.0 * d2 * d2
        + 144.0 * b2 * c * e2
        - 6.0 * b2 * d2 * e
        - 80.0 * b * c2 * d * e
        + 18.0 * b * c * d2 * d
        + 16.0 * c2 * c2 * e
        - 4.0 * c3 * d2
        - 27.0 * b4 * e2
        + 18.0 * b3 * c * d * e
        - 4.0 * b3 * d2 * d
        - 4.0 * b2 * c3 * e
        + b2 * c2 * d2
    )


def four_real_by_signs(b, c, d, e):
    Delta = quartic_discriminant(b, c, d, e)
    P = 8.0 * c - 3.0 * b * b
    D = 64.0 * e - 16.0 * c * c + 16.0 * b * b * c - 16.0 * b * d - 3.0 * b**4
    return (Delta > 0) & (P < 0) & (D < 0)
