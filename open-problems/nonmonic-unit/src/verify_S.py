"""INDEPENDENT verification of  S = 479/960 - (2/3) ln 2  and  P = 719/2880 - ln(2)/3.

Route used here is structurally different from src/derive_S.py:
 * no s-substitution, no case analysis -- the d-band endpoints are computed
   numerically from the actual critical points of f, and the intersection with
   [0,1] is taken numerically;
 * the 2-D integral over (a,c) is done with mpmath tanh-sinh quadrature at 40
   working digits, the domain split at the two non-smooth curves ac = 1/4
   (bottom-clip boundary) and ac = 1/3 (edge of the two-critical-point region).
Then mpmath.identify / PSLQ is run blind on the resulting number.
"""
import mpmath as mp

mp.mp.dps = 40

def band_len(a, c):
    """length of {d in [0,1] : a x^3 + x^2 + c x + d has three real roots}."""
    disc = 1 - 3*a*c
    if disc <= 0:
        return mp.mpf(0)
    r = mp.sqrt(disc)
    xm = (-1 - r)/(3*a)          # local max
    xp = (-1 + r)/(3*a)          # local min
    g = lambda x: a*x**3 + x**2 + c*x
    d_lo = -g(xm)
    d_hi = -g(xp)
    lo = max(d_lo, mp.mpf(0)); hi = min(d_hi, mp.mpf(1))
    return max(mp.mpf(0), hi - lo)

def inner(a):
    """int_0^1 band_len(a,c) dc, split at the non-smooth points."""
    cmax = min(mp.mpf(1), 1/(3*a))       # band empty beyond ac = 1/3
    cclip = 1/(4*a)                      # ac = 1/4  <=> s = 1/2
    pts = [mp.mpf(0)]
    if 0 < cclip < cmax:
        pts.append(cclip)
    pts.append(cmax)
    return mp.quad(lambda c: band_len(a, c), pts)

def main():
    print("mpmath dps =", mp.mp.dps)
    # outer split: a = 1/4 (cclip enters), a = 1/3 (cmax leaves c=1)
    S = mp.quad(inner, [mp.mpf(0), mp.mpf(1)/4, mp.mpf(1)/3, mp.mpf(1)])
    print("S  (quadrature, 40 dps) =", mp.nstr(S, 32))

    cand = mp.mpf(479)/960 - mp.mpf(2)/3*mp.log(2)
    print("S  (closed form)        =", mp.nstr(cand, 32))
    print("difference              =", mp.nstr(S - cand, 8))

    print("\nblind identify on S with basis {ln2, ln3}:")
    print("  ", mp.identify(S, ['log(2)', 'log(3)']))
    print("blind identify on S with basis {ln2}:")
    print("  ", mp.identify(S, ['log(2)']))
    print("blind PSLQ on [1, S, ln2, ln3]:")
    print("  ", mp.pslq([mp.mpf(1), S, mp.log(2), mp.log(3)], maxcoeff=10**8, maxsteps=10**6))

    P = mp.mpf(1)/5760 + S/2
    Pc = mp.mpf(719)/2880 - mp.log(2)/3
    print("\nP  (from quadrature)    =", mp.nstr(P, 32))
    print("P  (closed form)        =", mp.nstr(Pc, 32))
    print("difference              =", mp.nstr(P - Pc, 8))
    print("blind identify on P:    ", mp.identify(P, ['log(2)', 'log(3)']))

    # also re-do the quadrature at a lower precision setting as a stability check
    mp.mp.dps = 25
    S25 = mp.quad(inner, [mp.mpf(0), mp.mpf(1)/4, mp.mpf(1)/3, mp.mpf(1)])
    print("\nS at dps=25             =", mp.nstr(S25, 22), " (delta vs dps=40:",
          mp.nstr(S25 - cand, 6), ")")

if __name__ == '__main__':
    main()
