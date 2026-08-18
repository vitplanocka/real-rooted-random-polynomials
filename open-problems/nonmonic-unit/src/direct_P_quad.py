"""Fully independent high-precision evaluation of
     P = vol_4{(a,b,c,d) in [0,1]^4 : a x^3+b x^2+c x+d has three real roots}
WITHOUT using the cone/face reduction, without Theorem 2, without the s-substitution.

Only input: for fixed (a,b,c) with a>0, f = g + d is affine in d, so the set of
admissible d is the interval [d_lo, d_hi] = [-g(x_-), -g(x_+)] where x_-<x_+ are the
critical points (empty if b^2-3ac <= 0).  P = int_{[0,1]^3} |[d_lo,d_hi] cap [0,1]| .

Both d_lo and d_hi are strictly increasing in c (d/dc = -x_mp >= 0), so for fixed (a,b)
the inner integrand has at most three kinks in c, located by bisection:
    c1: d_lo(c) = 0   (below this, bottom clips)
    c2: d_hi(c) = 1   (above this, top clips)
    c3: d_lo(c) = 1   (above this the band is entirely above the window: L = 0)
plus the endpoint cmax = b^2/(3a) where the band closes.
"""
import mpmath as mp

def endpoints(a, b, c):
    disc = b*b - 3*a*c
    if disc <= 0:
        return None
    r = mp.sqrt(disc)
    xm = (-b - r)/(3*a); xp = (-b + r)/(3*a)
    g = lambda x: a*x**3 + b*x**2 + c*x
    return -g(xm), -g(xp)

def L(a, b, c):
    e = endpoints(a, b, c)
    if e is None:
        return mp.mpf(0)
    d_lo, d_hi = e
    lo = max(d_lo, mp.mpf(0)); hi = min(d_hi, mp.mpf(1))
    return max(mp.mpf(0), hi - lo)

def bisect(f, lo, hi):
    """root of increasing f on [lo,hi] or None if no sign change"""
    flo, fhi = f(lo), f(hi)
    if flo*fhi > 0:
        return None
    return mp.findroot(f, (lo, hi), solver='anderson', tol=mp.mpf(10)**(-2*mp.mp.dps))

def inner(a, b):
    cmax = min(mp.mpf(1), b*b/(3*a))
    if cmax <= 0:
        return mp.mpf(0)
    eps = mp.mpf(10)**(-mp.mp.dps)
    hi = cmax*(1 - eps)
    pts = [mp.mpf(0), cmax]
    for target, which in ((mp.mpf(0), 0), (mp.mpf(1), 1), (mp.mpf(1), 0)):
        f = lambda c, t=target, w=which: endpoints(a, b, c)[w] - t
        try:
            r = bisect(f, mp.mpf(0), hi)
        except Exception:
            r = None
        if r is not None and 0 < r < cmax:
            pts.append(r)
    pts = sorted(set(pts))
    return mp.quad(lambda c: L(a, b, c), pts)

def main(dps=20):
    mp.mp.dps = dps
    # outer 2-D integral over (a,b); split b at 1/2 and a at 1/3 to help the adaptive rule
    f_a = lambda a: mp.quad(lambda b: inner(a, b), [mp.mpf(0), mp.mpf(1)/2, mp.mpf(1)])
    P = mp.quad(f_a, [mp.mpf(1)/1000, mp.mpf(1)/10, mp.mpf(1)/3, mp.mpf(1)])
    # a in (0, 1/1000): bound the neglected sliver -- L <= 1 there, so it is < 1e-3;
    # handle it properly with a separate (log-scaled) piece
    tail = mp.quad(lambda u: mp.e**u * f_a(mp.e**u),
                   [mp.log(mp.mpf(10)**(-12)), mp.log(mp.mpf(1)/1000)])
    tiny = mp.mpf(10)**(-12)   # crude bound on a < 1e-12
    print("P (a>1e-3)      =", mp.nstr(P, 20))
    print("P (1e-12<a<1e-3)=", mp.nstr(tail, 20))
    tot = P + tail
    cand = mp.mpf(719)/2880 - mp.log(2)/3
    print("P total         =", mp.nstr(tot, 20))
    print("closed form     =", mp.nstr(cand, 20))
    print("difference      =", mp.nstr(tot - cand, 8), " (residual sliver a<1e-12 is <", tiny, ")")

if __name__ == '__main__':
    import sys
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 20)
