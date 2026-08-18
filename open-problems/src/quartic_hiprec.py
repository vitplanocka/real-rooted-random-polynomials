"""High-precision P_B for Problem B.

    16 P_B = U - C_clip,
    U      = (4K/9) 2^-18 Int_{-1}^{1} (3b^2+8)^{9/2} db     [closed form, K=128/105]
    C_clip = the same integral restricted to |d| > 1.

Two structurally different evaluations of C_clip:
  METHOD A: exact tau-integral  T(z) = (4/105) u^{5/2}(21-5u),  numerical in (b,m).
  METHOD B: exact m-integral    (2/9)(M^{9/2}-n0^9),            numerical in (b,y).
Both use exact panel edges (b*, m0(b) / y1(b)) and substitutions that render the
integrands analytic, so composite Gauss-Legendre converges geometrically.
"""
import json, os, sys, time
import mpmath as mp

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# ------------------------------------------------------------------ GL nodes
_glcache = {}
def gl(n):
    key = (n, mp.mp.prec)
    if key in _glcache: return _glcache[key]
    xs, ws = [], []
    for i in range(1, n + 1):
        x = mp.cos(mp.pi * (i - mp.mpf(1)/4) / (n + mp.mpf(1)/2))
        for _ in range(100):
            p0, p1 = mp.mpf(1), x
            for k in range(2, n + 1):
                p0, p1 = p1, ((2*k - 1)*x*p1 - (k - 1)*p0)/k
            dp = n*(x*p1 - p0)/(x*x - 1)
            dx = p1/dp
            x -= dx
            if abs(dx) < mp.mpf(10)**(-(mp.mp.dps + 5)): break
        p0, p1 = mp.mpf(1), x
        for k in range(2, n + 1):
            p0, p1 = p1, ((2*k - 1)*x*p1 - (k - 1)*p0)/k
        dp = n*(x*p1 - p0)/(x*x - 1)
        xs.append(x); ws.append(2/((1 - x*x)*dp*dp))
    _glcache[key] = (xs, ws)
    return xs, ws

def gl_int(f, a, b, n, npan=1):
    xs, ws = gl(n)
    a, b = mp.mpf(a), mp.mpf(b)
    tot = mp.mpf(0)
    h = (b - a)/npan
    for j in range(npan):
        lo = a + j*h; mid = lo + h/2; half = h/2
        tot += half*mp.fsum(w*f(mid + half*x) for x, w in zip(xs, ws))
    return tot

# ------------------------------------------------------------------ geometry
def setup():
    global TAU_C, BSTAR
    TAU_C = 8/(3*mp.sqrt(3))
    BSTAR = mp.findroot(lambda b: 1 - b**3/8 - b/2 - TAU_C*Mb(b)**mp.mpf(1.5),
                        mp.mpf('0.614302101416296'))

def Mb(b): return (3*b*b + 8)/16

def tau1(b): return (1 - b**3/8 - b/2)/Mb(b)**mp.mpf(1.5)

def u_of_z(z):
    """u in [0,1] with (u-1)^2 (u-4) + 27 z^2/16 = 0  (i.e. 16(1-u)^2(4-u)=27z^2)."""
    r = 27*z*z/16
    if r >= 4: return mp.mpf(0)
    u = mp.mpf(float(_u_float(float(z))))
    for _ in range(6):
        F = (u - 1)**2*(u - 4) + r
        dF = 3*(u - 1)*(u - 3)
        if dF == 0: break
        du = F/dF
        u -= du
        if abs(du) < mp.mpf(10)**(-(mp.mp.dps + 5)): break
    return u

def _u_float(z):
    import numpy as np
    r = 27.0*z*z/16.0
    if r >= 4.0: return 0.0
    lo, hi = 0.0, 1.0
    for _ in range(200):
        mid = 0.5*(lo + hi)
        if (mid - 1)**2*(mid - 4) + r < 0: lo = mid
        else: hi = mid
    return 0.5*(lo + hi)

def T_of(z):
    if z >= TAU_C: return mp.mpf(0)
    u = u_of_z(z)
    return (mp.mpf(4)/105)*u**mp.mpf(2.5)*(21 - 5*u)

def tau_of_y(y):
    return 4*(1 - y*y)*mp.sqrt(4 - y*y)/(3*mp.sqrt(3))

def y1_of(b):
    t1 = tau1(b)
    if t1 >= TAU_C: return mp.mpf(0)
    return mp.sqrt(u_of_z(t1))

def n0_of(b, tau):
    """positive root of tau n^3 + b n^2 - (1 + b^3/16)."""
    K = 1 + b**3/16
    n = mp.mpf(float(_n0_float(float(b), float(tau), float(K))))
    for _ in range(6):
        F = tau*n**3 + b*n*n - K
        dF = 3*tau*n*n + 2*b*n
        dn = F/dF
        n -= dn
        if abs(dn) < mp.mpf(10)**(-(mp.mp.dps + 5)): break
    return n

def _n0_float(b, tau, K):
    lo, hi = 0.0, 1.0
    while tau*hi**3 + b*hi*hi - K < 0: hi *= 2.0
    for _ in range(200):
        mid = 0.5*(lo + hi)
        if tau*mid**3 + b*mid*mid - K < 0: lo = mid
        else: hi = mid
    return 0.5*(lo + hi)

# ------------------------------------------------------------------ method B
def innerB(b, n, npan):
    y1 = y1_of(b)
    if y1 <= 0: return mp.mpf(0)
    M9 = Mb(b)**mp.mpf(4.5)
    def f(y):
        n0 = n0_of(b, tau_of_y(y))
        return (3 - y*y)*y**4*(M9 - n0**9)
    return gl_int(f, 0, y1, n, npan)

def methodB(nb, nib, npb=1, npi=1):
    Tm = mp.sqrt(1 - BSTAR)
    def f(t):
        return 2*t*innerB(BSTAR + t*t, nib, npi)
    return (mp.mpf(32)/27)*gl_int(f, 0, Tm, nb, npb)

# ------------------------------------------------------------------ method A
def innerA(b, n, npan):
    Mv = Mb(b)
    n0 = n0_of(b, TAU_C); m0 = n0*n0
    if m0 >= Mv: return mp.mpf(0)
    D = Mv - m0
    def f(s):
        m = m0 + D*s*s
        z = (1 + b**3/16 - b*m)/m**mp.mpf(1.5)
        return 2*s*m**mp.mpf(3.5)*T_of(z)
    return D*gl_int(f, 0, 1, n, npan)

def methodA(nb, nib, npb=1, npi=1):
    Tm = mp.sqrt(1 - BSTAR)
    def f(t):
        return 2*t*innerA(BSTAR + t*t, nib, npi)
    return 4*gl_int(f, 0, Tm, nb, npb)

# ------------------------------------------------------------------ main
if __name__ == "__main__":
    dps = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    mp.mp.dps = dps + 10
    setup()
    print(f"dps = {mp.mp.dps}")
    print("tau_c =", mp.nstr(TAU_C, 30))
    print("b*    =", mp.nstr(BSTAR, 30))

    U = mp.sqrt(3)*mp.asinh(mp.sqrt(6)/4)/90 + 7013*mp.sqrt(11)/302400
    # independent evaluation of U from its definition
    K = mp.mpf(128)/105
    Ui = (4*K/9)*mp.mpf(2)**-18*gl_int(lambda b: (3*b*b + 8)**mp.mpf(4.5), -1, 1, 80, 4)
    print("U (closed form) =", mp.nstr(U, dps))
    print("U (quadrature)  =", mp.nstr(Ui, dps), "   diff =", mp.nstr(U - Ui, 5))

    res = {"dps": mp.mp.dps, "b_star": mp.nstr(BSTAR, dps),
           "U": mp.nstr(U, dps), "U_quad_diff": mp.nstr(U - Ui, 5)}
    print("\n  method   nb  nin  npb npi        C_clip")
    prevA = prevB = None
    for nb, nin, npb, npi in [(40, 40, 1, 1), (60, 60, 2, 2), (80, 80, 3, 3), (100, 100, 4, 4)]:
        t0 = time.time(); A = methodA(nb, nin, npb, npi); ta = time.time() - t0
        t0 = time.time(); B = methodB(nb, nin, npb, npi); tb = time.time() - t0
        dA = "" if prevA is None else f"  dA={mp.nstr(A-prevA,3)}"
        dB = "" if prevB is None else f"  dB={mp.nstr(B-prevB,3)}"
        print(f"  A {nb:4d} {nin:4d} {npb:3d} {npi:3d}   {mp.nstr(A, dps)}  [{ta:.0f}s]{dA}")
        print(f"  B {nb:4d} {nin:4d} {npb:3d} {npi:3d}   {mp.nstr(B, dps)}  [{tb:.0f}s]{dB}")
        print(f"     A-B = {mp.nstr(A-B, 5)}")
        prevA, prevB = A, B
        res[f"A_{nb}_{nin}_{npb}_{npi}"] = mp.nstr(A, dps)
        res[f"B_{nb}_{nin}_{npb}_{npi}"] = mp.nstr(B, dps)

    C = (prevA + prevB)/2
    I16 = U - C
    PB = I16/16
    print("\nC_clip =", mp.nstr(C, dps))
    print("16 P_B =", mp.nstr(I16, dps))
    print("   P_B =", mp.nstr(PB, dps))
    res.update({"C_clip": mp.nstr(C, dps), "I16": mp.nstr(I16, dps),
                "PB": mp.nstr(PB, dps),
                "A_minus_B": mp.nstr(prevA - prevB, 5)})
    with open(os.path.join(ROOT, "results", "quartic_hiprec.json"), "w") as f:
        json.dump(res, f, indent=2)
    print("\nwrote results/quartic_hiprec.json")
