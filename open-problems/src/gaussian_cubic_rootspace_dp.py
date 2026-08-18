"""Double-precision validation of the ROOT-SPACE reduction (Method 2).

Map (r1,r2,r3) -> (a,b,c) = (-e1, e2, -e3); |Jacobian| = |V| = |(r1-r2)(r1-r3)(r2-r3)|.
Ordered triples r1<r2<r3 <-> cubics with 3 distinct real roots, so

  P = (1/6) (2pi)^{-3/2} \int_{R^3} exp(-(e1^2+e2^2+e3^2)/2) |V| dr

Fix y=r2, z=r3, integrate u=r1 analytically:
  e1 = u+p, e2 = u p + m, e3 = u m,   p=y+z, m=yz
  Q(u) = e1^2+e2^2+e3^2 = A u^2 + B u + C,  A=1+p^2+m^2, B=2p(1+m), C=p^2+m^2
  |V| = |y-z| * |(u-y)(u-z)|,  g(u) = (u-y)(u-z) = u^2 - p u + m
"""
import numpy as np
from scipy.special import ndtr
from scipy import integrate

SQRT2PI = np.sqrt(2 * np.pi)


def J(y, z):
    """int_R |(u-y)(u-z)| exp(-Q(u)/2) du"""
    p = y + z
    m = y * z
    A = 1.0 + p * p + m * m
    B = 2.0 * p * (1.0 + m)
    C = p * p + m * m
    mu = -B / (2.0 * A)
    sig = 1.0 / np.sqrt(A)
    K = np.exp(-(C - B * B / (4.0 * A)) / 2.0)

    # full line: int g e = sig*sqrt(2pi) * (sig^2 + mu^2 - p mu + m)
    full = sig * SQRT2PI * (sig * sig + mu * mu - p * mu + m)

    # partial on [y,z]  (y<z assumed)
    t1 = (y - mu) / sig
    t2 = (z - mu) / sig
    dPhi = ndtr(t2) - ndtr(t1)
    e1t = np.exp(-t1 * t1 / 2.0)
    e2t = np.exp(-t2 * t2 / 2.0)
    E1 = e1t - e2t
    T2 = SQRT2PI * dPhi + t1 * e1t - t2 * e2t
    part = sig * (sig * sig * T2 + sig * (2 * mu - p) * E1
                  + (mu * mu - p * mu + m) * SQRT2PI * dPhi)

    return K * (full - 2.0 * part)


def integrand_md(mid, d):
    """d * J(mid-d, mid+d)"""
    return d * J(mid - d, mid + d)


def P_rootspace(R=14.0):
    pref = (1.0 / 6.0) * (2 * np.pi) ** (-1.5) * 16.0

    def inner(d, mid):
        return integrand_md(mid, d)

    val, err = integrate.dblquad(inner, 0.0, R, lambda m: 0.0, lambda m: R,
                                 epsabs=1e-13, epsrel=1e-13)
    return pref * val, pref * err


if __name__ == "__main__":
    # spot-check J against brute-force numerical u-integration
    rng = np.random.default_rng(7)
    worst = 0.0
    for _ in range(200):
        y, z = np.sort(rng.standard_normal(2) * 2)
        p, m = y + z, y * z

        def f(u):
            e1 = u + p
            e2 = u * p + m
            e3 = u * m
            return abs((u - y) * (u - z)) * np.exp(-(e1**2 + e2**2 + e3**2) / 2)

        # integrate over a finite window that certainly contains all the mass:
        # Q(u)/2 >= A(u-mu)^2/2 + const, so |u-mu| <= 40/sqrt(A) is far beyond.
        p_, m_ = y + z, y * z
        A_ = 1 + p_ * p_ + m_ * m_
        mu_ = -2 * p_ * (1 + m_) / (2 * A_)
        w = 45.0 / np.sqrt(A_)
        pts = sorted({mu_ - w, y, z, mu_ + w})
        pts = [mu_ - w] + [q for q in (y, z) if mu_ - w < q < mu_ + w] + [mu_ + w]
        num = sum(integrate.quad(f, lo, hi, limit=400, epsabs=1e-300, epsrel=1e-13)[0]
                  for lo, hi in zip(pts[:-1], pts[1:]))
        rel = abs(num - J(y, z)) / max(abs(num), 1e-300)
        worst = max(worst, rel)
    print(f"[J formula] worst relative error vs brute force over 200 samples: {worst:.3e}")

    v, e = P_rootspace()
    print(f"[root space] P = {v!r}  (reported err {e:.2e})")
    print(f"[coeff space, earlier] 0.16992938262347956")
    print(f"difference = {v - 0.16992938262347956:.3e}")
