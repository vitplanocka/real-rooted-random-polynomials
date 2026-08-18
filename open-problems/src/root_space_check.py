"""Problem A, third route: integrate in ROOT space instead of coefficient space.

Structurally independent of both the (a,b)-Phi-difference quadrature and the
Monte Carlo, so it is a real cross-check rather than a re-run.

Derivation.  With f(x) = x^3 + a x^2 + b x + c = (x-r1)(x-r2)(x-r3),

    a = -e1,  b = e2,  c = -e3        (e_k elementary symmetric in the roots)

The Jacobian of (r1,r2,r3) -> (e1,e2,e3) is the Vandermonde
V = prod_{i<j}(r_i - r_j), the map is 3!-to-1 onto the all-real region, and the
standard normal density is even, so

    P_A = (2*pi)^{-3/2} \\int_{r1<r2<r3} V(r) exp(-(e1^2+e2^2+e3^2)/2) dr.

Naively imposing r1<r2<r3 with a mask gives an integrand with kinks on the
simplex faces and only algebraic convergence (measured: ~0.16989 at n=500 and
still climbing).  Instead parametrise the ordered simplex by its GAPS,

    r1 = u,  r2 = u + p,  r3 = u + p + q,      u in R,  p,q > 0,

which has unit Jacobian and makes the Vandermonde the smooth positive
polynomial V = p*q*(p+q).  The domain is now a product, the integrand is
analytic, and Gauss-Legendre converges geometrically.

Decay: for large p or q the roots spread, so e2 ~ -p^2 and the weight decays
like exp(-p^4/2); truncating p,q at M and u at +-L is harmless well before
double precision.
"""
import json
import os
import sys
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "..", "results", "root_space_check.json")


def integral(L: float, M: float, nu: int, npq: int) -> float:
    """Gauss-Legendre on u in [-L,L] and p,q in [0,M], gap parametrisation."""
    xu, wu = np.polynomial.legendre.leggauss(nu)
    xp, wp = np.polynomial.legendre.leggauss(npq)
    u = L * xu
    wU = L * wu
    pq = 0.5 * M * (xp + 1.0)
    wP = 0.5 * M * wp

    U = u[:, None, None]
    P = pq[None, :, None]
    Q = pq[None, None, :]
    r1, r2, r3 = U, U + P, U + P + Q
    e1 = r1 + r2 + r3
    e2 = r1 * r2 + r1 * r3 + r2 * r3
    e3 = r1 * r2 * r3
    V = P * Q * (P + Q)
    integrand = V * np.exp(-(e1 ** 2 + e2 ** 2 + e3 ** 2) / 2.0)
    W = wU[:, None, None] * wP[None, :, None] * wP[None, None, :]
    return float((integrand * W).sum()) * (2.0 * np.pi) ** (-1.5)


def main() -> None:
    runs = []
    for (L, M) in ((6.0, 5.0), (7.0, 6.0), (8.0, 7.0)):
        for n in (40, 60, 80, 100, 140):
            val = integral(L, M, n, n)
            runs.append({"L": L, "M": M, "n": n, "value": repr(val)})
            print(f"L={L:4.1f} M={M:4.1f} n={n:4d}   P_A = {val:.16f}", flush=True)
    best = integral(8.0, 7.0, 180, 180)
    print(f"\nbest (L=8, M=7, n=180): {best:.16f}")
    json.dump({"problem": "A (monic cubic, Gaussian coefficients)",
               "method": "root-space Vandermonde integral, gap parametrisation, "
                         "tensor Gauss-Legendre",
               "runs": runs, "best": repr(best)},
              open(OUT, "w"), indent=2)
    print(f"wrote {OUT}")


if __name__ == "__main__":
    sys.exit(main())
