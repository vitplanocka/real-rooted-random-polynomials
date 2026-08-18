"""THIRD, structurally independent evaluation of 16 P_B: raw (b,c,d) coordinates,
critical points from the trigonometric cubic solution, band length taken straight
from its definition L = g(x2) - max(g(x1),g(x3)).  No normal form, no Lambda, no
closed-form tau-integral, no unclipped/clipped decomposition.

The only structural inputs are (i) the exact d-band endpoints d_lo,d_hi (the
already-validated cubic-discriminant formula), (ii) the kink d* = bc/2 - b^3/8,
(iii) the exact clipping-onset loci, all used ONLY to place panel edges and
variable substitutions, which cannot change the value of the integral.
"""
import os, sys, time
import mpmath as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from quartic_hiprec import gl, gl_int   # GL nodes only

def crit(b, c, d):
    """x1<=x2<=x3, roots of 4x^3+3bx^2+2cx+d, trig formula, in mpmath."""
    A = 3*b/4; B = c/2; C = d/4
    p = B - A*A/3
    q = 2*A**3/27 - A*B/3 + C
    r = mp.sqrt(-p/3)
    arg = 3*q/(2*p*r)
    if arg > 1: arg = mp.mpf(1)
    if arg < -1: arg = mp.mpf(-1)
    th = mp.acos(arg)
    xs = [2*r*mp.cos(th/3 - 2*mp.pi*k/3) - A/3 for k in range(3)]
    xs.sort()
    return xs

def g(x, b, c, d):
    return (((x + b)*x + c)*x + d)*x

def Lraw(b, c, d):
    x1, x2, x3 = crit(b, c, d)
    return g(x2, b, c, d) - max(g(x1, b, c, d), g(x3, b, c, d))

def dband(b, c):
    A = 3*b/4; B = c/2
    s = mp.sqrt(A*A - 3*B)
    return 4*(A + s)**2*(A - 2*s)/27, 4*(A - s)**2*(A + 2*s)/27

def inner_d(b, c, n):
    dl, dh = dband(b, c)
    dstar = b*c/2 - b**3/8
    tot = mp.mpf(0)
    # left piece [max(-1,dl), dstar]
    if dl < -1:
        tot += gl_int(lambda d: Lraw(b, c, d), -1, dstar, n)
    else:
        W = dstar - dl
        tot += gl_int(lambda w: 2*w*Lraw(b, c, dl + w*w), 0, mp.sqrt(W), n)
    # right piece [dstar, min(1,dh)]
    if dh > 1:
        tot += gl_int(lambda d: Lraw(b, c, d), dstar, 1, n)
    else:
        W = dh - dstar
        tot += gl_int(lambda w: 2*w*Lraw(b, c, dh - w*w), 0, mp.sqrt(W), n)
    return tot

def mid_c(b, n_c, n_d):
    """int_{-1}^{3b^2/8} inner_d dc, in the variable m with c = 3b^2/8 - 2m."""
    M = (3*b*b + 8)/16
    TAU_C = 8/(3*mp.sqrt(3))
    # clipping onset: 1 + b^3/16 - b m = tau_c m^{3/2}  (m0 = n0^2)
    K = 1 + b**3/16
    n = mp.mpf(1)
    for _ in range(200):
        F = TAU_C*n**3 + b*n*n - K
        dF = 3*TAU_C*n*n + 2*b*n
        dn = F/dF; n -= dn
        if abs(dn) < mp.mpf(10)**(-(mp.mp.dps + 5)): break
    m0 = n*n
    def J(m):                      # dc = -2 dm  =>  factor 2
        return 2*inner_d(b, 3*b*b/8 - 2*m, n_d)
    if m0 >= M:                    # no clipping anywhere on this b-slice
        return gl_int(lambda r: 2*r*J(r*r), 0, mp.sqrt(M), n_c)
    tot = gl_int(lambda r: 2*r*J(r*r), 0, mp.sqrt(m0), n_c)          # m in [0,m0]
    D = M - m0
    tot += gl_int(lambda r: 2*D*r*J(m0 + D*r*r), 0, 1, n_c)          # m in [m0,M]
    return tot

if __name__ == "__main__":
    mp.mp.dps = int(sys.argv[1]) if len(sys.argv) > 1 else 30
    nb = int(sys.argv[2]) if len(sys.argv) > 2 else 30
    nc = int(sys.argv[3]) if len(sys.argv) > 3 else 30
    nd = int(sys.argv[4]) if len(sys.argv) > 4 else 30
    BSTAR = mp.findroot(lambda x: 27*x**3 + 9*x**2 + 108*x - 76, mp.mpf('0.6143021014162961'))
    t0 = time.time()
    # integrand is even in b: 16 P_B = 2 * int_0^1
    part1 = gl_int(lambda b: mid_c(b, nc, nd), 0, BSTAR, nb, 2)
    T = mp.sqrt(1 - BSTAR)
    part2 = gl_int(lambda t: 2*t*mid_c(BSTAR + t*t, nc, nd), 0, T, nb, 2)
    I16 = 2*(part1 + part2)
    print(f"dps={mp.mp.dps} nb={nb} nc={nc} nd={nd}   [{time.time()-t0:.0f}s]")
    print("  b in [0,b*]  ->", mp.nstr(part1, mp.mp.dps))
    print("  b in [b*,1]  ->", mp.nstr(part2, mp.mp.dps))
    print("  16 P_B (RAW) =", mp.nstr(I16, mp.mp.dps))
    ref = mp.mpf('0.0874292854494397687231104525326038583412617745909571190226647499145855113887')
    print("  reference    =", mp.nstr(ref, mp.mp.dps))
    print("  difference   =", mp.nstr(I16 - ref, 6))
