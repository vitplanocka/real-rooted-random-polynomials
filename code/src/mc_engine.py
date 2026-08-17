"""Vectorized Monte Carlo engine for real-rootedness probabilities.

Cases:
  dep_cubic_sym     x^3+px+q,            (p,q)   iid U[-1,1]  (anchor: 2*sqrt(3)/45)
  monic_cubic_sym   x^3+ax^2+bx+c,       (a,b,c) iid U[-1,1]  (OPEN target)
  monic_cubic_unit  x^3+ax^2+bx+c,       (a,b,c) iid U[0,1]
  monic_cubic_gauss x^3+ax^2+bx+c,       (a,b,c) iid N(0,1)
  quartic_sym       x^4+ax^3+bx^2+cx+d,  iid U[-1,1]          (OPEN, all 4 roots real)
  matrix3_unit      3x3 matrix, entries iid U[0,1], all eigenvalues real
                    (the parent problem; literature simulation ~0.708)

Method: chunked vectorized sampling with antithetic pairing (u, 1-u).
Standard errors are estimated from the dispersion of per-chunk proportions
(each chunk is an iid replicate), which correctly accounts for the
antithetic correlation.

Quartic all-real test uses sign conditions
    Disc > 0  and  P = 8b-3a^2 < 0  and  D = 64d-16b^2+16a^2 b-16ac-3a^4 < 0
validated at startup against numpy.roots on 2e5 samples.

Usage:  python mc_engine.py [N_cubic] [N_quartic] [N_matrix]
Defaults: 2e8, 1e8, 1e7.   Output: results/mc_results.json
"""
import json
import os
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "..", "results", "mc_results.json")

CHUNK = 5 * 10**6  # antithetic doubles this per draw


def cubic_disc(a, b, c):
    return (18 * a * b * c - 4 * a**3 * c + a * a * b * b
            - 4 * b**3 - 27 * c * c)


def quartic_all_real(a, b, c, d):
    """All four roots real (generic): Disc > 0, P < 0, D < 0."""
    disc = (256 * d**3 - 192 * a * c * d**2 - 128 * b**2 * d**2
            + 144 * a**2 * b * d**2 - 27 * a**4 * d**2
            + 144 * b * c**2 * d - 6 * a**2 * c**2 * d
            - 80 * a * b**2 * c * d + 18 * a**3 * b * c * d
            + 16 * b**4 * d - 4 * a**2 * b**3 * d - 27 * c**4
            + 18 * a * b * c**3 - 4 * a**3 * c**3 - 4 * b**3 * c**2
            + a**2 * b**2 * c**2)
    P = 8 * b - 3 * a * a
    D = 64 * d - 16 * b * b + 16 * a * a * b - 16 * a * c - 3 * a**4
    return (disc > 0) & (P < 0) & (D < 0)


def validate_quartic(n=200_000, seed=12345):
    """Cross-check sign conditions against numpy.roots."""
    rng = np.random.default_rng(seed)
    coef = rng.uniform(-1, 1, (n, 4))
    pred = quartic_all_real(coef[:, 0], coef[:, 1], coef[:, 2], coef[:, 3])
    mism = 0
    for i in range(n):
        r = np.roots([1.0, *coef[i]])
        allreal = np.all(np.abs(r.imag) < 1e-7 * np.maximum(1, np.abs(r)))
        if allreal != pred[i]:
            mism += 1
    return mism, n


def run_case(name, sampler, n_total, seed):
    """sampler(u) -> bool array; u is (m, dim) uniform in [0,1)."""
    rng = np.random.default_rng(seed)
    dim = sampler.dim
    props, n_done = [], 0
    t0 = time.time()
    while n_done < n_total:
        m = min(CHUNK, (n_total - n_done + 1) // 2)
        u = rng.random((m, dim))
        k = np.count_nonzero(sampler(u)) + np.count_nonzero(sampler(1.0 - u))
        props.append(k / (2 * m))
        n_done += 2 * m
    props = np.asarray(props)
    p = props.mean()
    se = props.std(ddof=1) / np.sqrt(len(props)) if len(props) > 1 else float("nan")
    elapsed = time.time() - t0
    print(f"{name:18s} p = {p:.8f}  se = {se:.2e}  n = {n_done:.2e}  "
          f"({elapsed:.1f}s)")
    return {"p": p, "se": se, "n": n_done, "seconds": round(elapsed, 1)}


def make_sampler(fn, dim):
    fn.dim = dim
    return fn


def dep_cubic(u):
    p = 2 * u[:, 0] - 1
    q = 2 * u[:, 1] - 1
    return -4 * p**3 - 27 * q * q >= 0


def monic_cubic_sym(u):
    a, b, c = (2 * u[:, i] - 1 for i in range(3))
    return cubic_disc(a, b, c) >= 0


def monic_cubic_unit(u):
    a, b, c = u[:, 0], u[:, 1], u[:, 2]
    return cubic_disc(a, b, c) >= 0


def monic_cubic_gauss(u):
    # antithetic via u -> 1-u still valid: N^{-1}(1-u) = -N^{-1}(u)
    from scipy.special import ndtri
    a, b, c = (ndtri(np.clip(u[:, i], 1e-16, 1 - 1e-16)) for i in range(3))
    return cubic_disc(a, b, c) >= 0


def quartic_sym(u):
    a, b, c, d = (2 * u[:, i] - 1 for i in range(4))
    return quartic_all_real(a, b, c, d)


def matrix3_unit(u):
    m = u.reshape(-1, 3, 3)
    ev = np.linalg.eigvals(m)
    return np.all(np.abs(ev.imag) < 1e-9, axis=1)


def main():
    n_cubic = int(float(sys.argv[1])) if len(sys.argv) > 1 else 2 * 10**8
    n_quart = int(float(sys.argv[2])) if len(sys.argv) > 2 else 10**8
    n_mat = int(float(sys.argv[3])) if len(sys.argv) > 3 else 10**7

    print("validating quartic sign conditions vs numpy.roots ...")
    mism, nval = validate_quartic()
    print(f"quartic condition validation: {mism}/{nval} mismatches")
    results = {"quartic_validation": {"mismatches": mism, "n": nval}}

    cases = [
        ("dep_cubic_sym", make_sampler(dep_cubic, 2), n_cubic, 1),
        ("monic_cubic_sym", make_sampler(monic_cubic_sym, 3), n_cubic, 2),
        ("monic_cubic_unit", make_sampler(monic_cubic_unit, 3), n_cubic, 3),
        ("monic_cubic_gauss", make_sampler(monic_cubic_gauss, 3), n_cubic // 4, 4),
        ("quartic_sym", make_sampler(quartic_sym, 4), n_quart, 5),
        ("matrix3_unit", make_sampler(matrix3_unit, 9), n_mat, 6),
    ]
    for name, sampler, n, seed in cases:
        results[name] = run_case(name, sampler, n, seed)

    anchor = 2 * np.sqrt(3) / 45
    dev = (results["dep_cubic_sym"]["p"] - anchor) / results["dep_cubic_sym"]["se"]
    results["anchor_check"] = {
        "dep_cubic_exact": anchor,
        "deviation_sigmas": dev,
    }
    print(f"\nanchor check: dep cubic exact = {anchor:.10f}, "
          f"MC deviation = {dev:+.2f} sigma")

    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    with open(OUT, "w") as fh:
        json.dump(results, fh, indent=2)
    print(f"written: {os.path.abspath(OUT)}")


if __name__ == "__main__":
    main()
