"""From-scratch Monte Carlo cross-check for

    P_A = P( x^3 + a x^2 + b x + c has 3 distinct real roots ),  (a,b,c) iid N(0,1)

Uses the sign of the cubic discriminant

    D3 = 18 a b c - 4 a^3 c + a^2 b^2 - 4 b^3 - 27 c^2

(D3 > 0  <=>  three distinct real roots), evaluated in float64 on i.i.d. normal
triples.  Deliberately shares NO code and NO reduction with the quadrature: it
never touches c_lo / c_hi, Phi, or the (a,s) / root-space changes of variable.

Also reports:
  * a float128 (longdouble) recomputation of the discriminant on a subsample, to
    show that float64 round-off near D3 = 0 does not bias the answer;
  * a numpy.roots-based estimate on a smaller subsample as a second opinion.
"""
import json
import os
import time
from multiprocessing import Pool

import numpy as np

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CHUNK = 2_000_000


def _count(args):
    ss, n = args
    rng = np.random.default_rng(ss)
    hits = 0
    done = 0
    while done < n:
        k = min(CHUNK, n - done)
        a = rng.standard_normal(k)
        b = rng.standard_normal(k)
        c = rng.standard_normal(k)
        d3 = (18.0 * a * b * c - 4.0 * a * a * a * c + a * a * b * b
              - 4.0 * b * b * b - 27.0 * c * c)
        hits += int(np.count_nonzero(d3 > 0.0))
        done += k
    return hits, n


def run_mc(total, procs=28, seed0=0xC0FFEE, nstream=None):
    """Independent substreams via SeedSequence.spawn (not sequential integer seeds)."""
    nstream = nstream or procs
    children = np.random.SeedSequence(seed0).spawn(nstream)
    per = total // nstream
    tasks = [(children[i], per) for i in range(nstream)]
    tasks[-1] = (children[-1], total - per * (nstream - 1))
    with Pool(procs) as pool:
        out = pool.map(_count, tasks)
    hits = sum(h for h, _ in out)
    n = sum(k for _, k in out)
    p = hits / n
    se = np.sqrt(p * (1 - p) / n)
    # chi-square over substreams: are the per-stream rates mutually consistent?
    chi2 = sum((h - k * p) ** 2 / (k * p * (1 - p)) for h, k in out)
    return hits, n, p, se, out, float(chi2)


def precision_probe(n=20_000_000, seed=12345):
    """Recompute D3 in float128 and with numpy.roots; count disagreements."""
    rng = np.random.default_rng(seed)
    a = rng.standard_normal(n)
    b = rng.standard_normal(n)
    c = rng.standard_normal(n)
    d64 = (18.0 * a * b * c - 4.0 * a * a * a * c + a * a * b * b
           - 4.0 * b * b * b - 27.0 * c * c)
    A = a.astype(np.longdouble); B = b.astype(np.longdouble); C = c.astype(np.longdouble)
    d80 = (18 * A * B * C - 4 * A * A * A * C + A * A * B * B
           - 4 * B * B * B - 27 * C * C)
    dis = np.count_nonzero((d64 > 0) != (d80 > 0))
    return n, dis, float((d64 > 0).mean()), float((d80 > 0).mean())


def roots_probe(n=300_000, seed=999):
    rng = np.random.default_rng(seed)
    a, b, c = rng.standard_normal((3, n))
    ok = 0
    for i in range(n):
        r = np.roots([1.0, a[i], b[i], c[i]])
        if np.all(np.abs(r.imag) < 1e-9 * (1.0 + np.abs(r.real))):
            ok += 1
    p = ok / n
    return n, p, np.sqrt(p * (1 - p) / n)


if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=float, default=4e9)
    ap.add_argument("--procs", type=int, default=28)
    args = ap.parse_args()
    total = int(args.n)

    t0 = time.time()
    hits, n, p, se, per_stream, chi2 = run_mc(total, args.procs, nstream=112)
    el = time.time() - t0
    print(f"[MC discriminant] n = {n:,}   hits = {hits:,}")
    print(f"  p_hat = {p:.9f}   se = {se:.2e}   [{el:.0f}s]")
    k = len(per_stream)
    print(f"  substream consistency: chi2 = {chi2:.1f} on {k-1} dof "
          f"(expect ~{k-1} +- {np.sqrt(2*(k-1)):.0f})")

    npb, dis, p64, p80 = precision_probe()
    print(f"[float64 vs float128 probe] n = {npb:,}  sign disagreements = {dis} "
          f"({dis/npb:.2e})   p64 = {p64:.7f}  p128 = {p80:.7f}")

    nr, pr, ser = roots_probe()
    print(f"[numpy.roots probe] n = {nr:,}  p = {pr:.6f} +- {ser:.2e}")

    QUAD = 0.16992938262347950265644315713176190213405726145463  # 50 digits, see quad json
    sig = (p - QUAD) / se
    print(f"\n[quadrature] P_A = {QUAD!r}")
    print(f"  MC - quad = {p - QUAD:+.3e}   =  {sig:+.3f} sigma")

    out = dict(
        method="Monte Carlo, sign of cubic discriminant, float64, vectorized numpy",
        samples=n, hits=hits,
        estimate=repr(p), standard_error=repr(float(se)),
        seconds=round(el, 1), procs=args.procs, base_seed="0xC0FFEE",
        substreams=len(per_stream), chi2_substreams=round(chi2, 2),
        quadrature_value=repr(QUAD),
        mc_minus_quad=repr(float(p - QUAD)),
        sigma_discrepancy=repr(float(sig)),
        float64_vs_float128_probe=dict(n=npb, sign_disagreements=dis,
                                       p_float64=p64, p_float128=p80),
        numpy_roots_probe=dict(n=nr, estimate=pr, standard_error=float(ser)),
    )
    os.makedirs(os.path.join(ROOT, "results"), exist_ok=True)
    with open(os.path.join(ROOT, "results", "gaussian_cubic_mc.json"), "w") as fh:
        json.dump(out, fh, indent=2)
    print("\nwrote results/gaussian_cubic_mc.json")
