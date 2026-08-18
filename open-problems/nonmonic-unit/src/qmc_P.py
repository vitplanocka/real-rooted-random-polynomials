"""Independent high-accuracy evaluation of the FULL 4-D volume
     P = vol_4{(a,b,c,d) in [0,1]^4 : a x^3+b x^2+c x+d has three real roots}
by randomized quasi-Monte Carlo on the 3-D integral of the exact d-band length.

Uses NO cone reduction, NO Theorem 2, NO s-substitution: for fixed (a,b,c) with a>0
the admissible d form the interval [-g(x_-), -g(x_+)] (x_± the critical points of
f = g + d), and P = int_{[0,1]^3} |[d_lo,d_hi] cap [0,1]| da db dc.

Scrambled Sobol' with R independent scramblings gives an honest empirical error bar
(std of the R replicate means / sqrt(R)) rather than a self-reported tolerance.
"""
import numpy as np
from scipy.stats import qmc

def bandlen(a, b, c):
    disc = b*b - 3.0*a*c
    ok = (disc > 0) & (a > 0)
    r = np.sqrt(np.where(ok, disc, 0.0))
    aa = np.where(a > 0, a, 1.0)
    xm = (-b - r)/(3.0*aa); xp = (-b + r)/(3.0*aa)
    g = lambda x: a*x**3 + b*x**2 + c*x
    d_lo = -g(xm); d_hi = -g(xp)
    lo = np.maximum(d_lo, 0.0); hi = np.minimum(d_hi, 1.0)
    return np.where(ok, np.maximum(hi - lo, 0.0), 0.0)

def main(m=22, R=32, seed=7):
    rng = np.random.default_rng(seed)
    means = []
    for i in range(R):
        s = qmc.Sobol(d=3, scramble=True, seed=int(rng.integers(2**31)))
        pts = s.random_base2(m)
        means.append(bandlen(pts[:, 0], pts[:, 1], pts[:, 2]).mean())
    means = np.array(means)
    est = means.mean(); err = means.std(ddof=1)/np.sqrt(R)
    cand = 719/2880 - np.log(2)/3
    print(f"randomized Sobol': R={R} replicates x 2^{m} = {R*2**m:,} points total")
    print(f"P (QMC)      = {est:.14f}")
    print(f"P (empirical se) = {err:.3e}")
    print(f"P (closed)   = {cand:.14f}")
    print(f"difference   = {est-cand:+.3e}   ({(est-cand)/err:+.2f} sigma)")

if __name__ == '__main__':
    import sys
    main(*(int(x) for x in sys.argv[1:]))
