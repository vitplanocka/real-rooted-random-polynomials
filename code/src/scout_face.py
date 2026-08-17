"""Quick double-precision scout of the face decomposition

    P = (V(1) + S_b)/16,
    V(1) = vol_3{(A,B,C) in [-1,1]^3 : x^3+Ax^2+Bx+C has 3 real roots}
    S_b  = vol_3{(a,c,d) in [-1,1]^3 : a x^3 + x^2 + c x + d has 3 real roots}

Both computed with the sigma-parameterisation (piecewise-polynomial integrand).
Purpose: (i) validate the decomposition against the known V(1), (ii) get a first
answer good to ~1e-10, far more than the 1.7e-5 needed to separate candidates.
"""
import numpy as np
from scipy.integrate import quad

# ---------------------------------------------------------------- bands
# f = a x^3 + b x^2 + c x + d, a > 0, sigma = sqrt(b^2 - 3 a c) > 0:
#   d_hi = (b-sigma)^2 (b+2 sigma) / (27 a^2)
#   d_lo = (b+sigma)^2 (b-2 sigma) / (27 a^2)


def L_overlap(d_lo, d_hi, w_lo=-1.0, w_hi=1.0):
    return max(0.0, min(d_hi, w_hi) - max(d_lo, w_lo))


# ---------------------------------------------------------------- V(1) = S_a
# monic: a=1, b=A; B = (A^2-sigma^2)/3, dB = -(2 sigma/3) dsigma
def V1_inner(A):
    s_lo = np.sqrt(max(0.0, A * A - 3.0))
    s_hi = np.sqrt(A * A + 3.0)

    def f(s):
        d_hi = (A - s) ** 2 * (A + 2 * s) / 27.0
        d_lo = (A + s) ** 2 * (A - 2 * s) / 27.0
        return (2.0 * s / 3.0) * L_overlap(d_lo, d_hi)

    val, err = quad(f, s_lo, s_hi, limit=400, epsabs=1e-14, epsrel=1e-13)
    return val


def V1():
    val, err = quad(V1_inner, 0.0, 1.0, limit=400, epsabs=1e-14, epsrel=1e-13)
    return 2.0 * val, err        # factor 2: A -> -A, C -> -C symmetry


# ---------------------------------------------------------------- S_b
# b = 1 fixed, a in [-1,1]; (a,c,d) -> (-a,-c,d) is a symmetry (x -> -x), so
# integrate a in [0,1] and double.  c = (1-s^2)/(3a),  dc = -(2s/(3a)) ds.
def Sb_inner(a):
    u = 27.0 * a * a
    s_lo = np.sqrt(max(0.0, 1.0 - 3.0 * a))
    s_hi = np.sqrt(1.0 + 3.0 * a)

    def f(s):
        d_hi = (s - 1.0) ** 2 * (2 * s + 1.0) / u
        d_lo = -((s + 1.0) ** 2 * (2 * s - 1.0)) / u
        return (2.0 / (3.0 * a)) * s * L_overlap(d_lo, d_hi)

    val, err = quad(f, s_lo, s_hi, limit=400, epsabs=1e-14, epsrel=1e-13)
    return val


def Sb():
    val, err = quad(Sb_inner, 0.0, 1.0, limit=400, epsabs=1e-13, epsrel=1e-12)
    return 2.0 * val, err


if __name__ == "__main__":
    import math
    v1, e1 = V1()
    v1_exact = 766.0 / 1215.0 + math.log(3.0) / 6.0
    print(f"V(1) computed = {v1:.16f}  (err est {e1:.1e})")
    print(f"V(1) exact    = {v1_exact:.16f}")
    print(f"V(1) diff     = {v1 - v1_exact:.3e}")

    sb, e2 = Sb()
    print(f"S_b computed  = {sb:.16f}  (err est {e2:.1e})")

    P = (v1_exact + sb) / 16.0
    print(f"P = (V(1)+S_b)/16 = {P:.16f}")
    cand1 = 641.0 / 2430.0 - math.log(3.0) / 24.0
    cand2 = 0.217993225
    print(f"dxdy 641/2430-ln3/24 = {cand1:.16f}   diff {P-cand1:+.3e}")
    print(f"sweep 0.217993225    = {cand2:.16f}   diff {P-cand2:+.3e}")
