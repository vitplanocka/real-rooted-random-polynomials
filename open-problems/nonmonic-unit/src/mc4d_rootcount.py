#!/usr/bin/env python3
"""
INDEPENDENT Monte-Carlo estimate of

    P = Pr( a x^3 + b x^2 + c x + d  has three real roots ),   a,b,c,d iid U[0,1].

*** This script deliberately never forms the degree-4 discriminant polynomial. ***
It counts real roots numerically instead.

Method (B)  -- primary, vectorized, used for the 2e9-sample run
------------------------------------------------------------------
a > 0 a.s.  Substitute y = a*x (an increasing bijection of R, so the number of
real roots is unchanged) and multiply by a^2:

    a x^3 + b x^2 + c x + d  ->  g(y) = y^3 + b y^2 + (a c) y + (a^2 d)

which is monic with all coefficients in [0,1] -- i.e. perfectly scaled, unlike
dividing through by a (which blows up when a ~ 1e-8).  Then

    g'(y) = 3 y^2 + 2 b y + q,   q = a c,
    two distinct critical points  <=>  D := b^2 - 3 q > 0,
    y_- = (-b - sqrt(D))/3  (local max),   y_+ = (-b + sqrt(D))/3  (local min)

and g has three real roots  <=>  D > 0  and  g(y_-) * g(y_+) <= 0.
g is evaluated at the critical points by Horner.  No discriminant expansion.

For completeness the *literal* un-transformed form of the same test,
x_pm = (-b +- sqrt(b^2-3ac))/(3a) with f evaluated by Horner, is also
implemented ("B-raw") and compared on the cross-check run.

Method (A)  -- cross-check at N = 2e6
------------------------------------------------------------------
Eigenvalues of the 3x3 companion matrix (this is exactly what numpy.roots does,
but batched via np.linalg.eigvals on a stacked (N,3,3) array so that 2e6
samples are feasible).  A root is called real when |Im z| <= tol*(1+|z|).
Done both on the well-scaled monic g (A-scaled) and on the raw
x^3 + (b/a) x^2 + (c/a) x + (d/a) (A-raw).

Method (C)  -- deterministic cross-check
------------------------------------------------------------------
Integrating out d analytically (the condition on d is an interval) leaves a
3-dimensional integral over (a,b,c) which is evaluated by scrambled Sobol' QMC
with several independent scramblings.  Fully independent of the MC sampling.
"""

import os
import sys
import time
import math
import multiprocessing as mp

import numpy as np

# ----------------------------------------------------------------------------
# configuration
# ----------------------------------------------------------------------------
N_TOTAL      = 2_000_000_000      # 2e9 samples for the production run
N_WORKERS    = 6                  # shared machine: hard limit of 6
CHUNK        = 5_000_000          # samples per task
SEED         = 987_654_321        # deliberately NOT 12345
N_CROSS      = 2_000_000          # samples for the method (A) cross-check
CROSS_SEED   = 24_680_135

OUT = "/home/vit-planocka/math/nonmonic-01/results/mc4d_rootcount.txt"


# ----------------------------------------------------------------------------
# method (B): vectorized critical-point / sign test
# ----------------------------------------------------------------------------
def count_hits_B(a, b, c, d):
    """Boolean array: True iff a x^3+b x^2+c x+d has 3 real roots (multiplicity
    counted).  Uses the y = a x rescaling described above."""
    q = a * c                 # coeff of y   in g
    r = a * a * d             # constant     in g
    D = b * b - 3.0 * q       # = discriminant/4 of g' (also of f' up to a^2)
    ok = D > 0.0
    s = np.sqrt(np.where(ok, D, 0.0))
    ym = (-b - s) * (1.0 / 3.0)
    yp = (-b + s) * (1.0 / 3.0)
    # Horner:  g(y) = ((y + b) y + q) y + r
    gm = ((ym + b) * ym + q) * ym + r
    gp = ((yp + b) * yp + q) * yp + r
    return ok & (gm * gp <= 0.0)


def count_hits_B_raw(a, b, c, d):
    """Same test written literally on f, without the y = a x rescaling."""
    D = b * b - 3.0 * a * c
    ok = D > 0.0
    s = np.sqrt(np.where(ok, D, 0.0))
    inv = 1.0 / (3.0 * a)
    xm = (-b - s) * inv
    xp = (-b + s) * inv
    fm = ((a * xm + b) * xm + c) * xm + d
    fp = ((a * xp + b) * xp + c) * xp + d
    return ok & (fm * fp <= 0.0)


def worker(args):
    """One chunk: draw n samples from the given SeedSequence, return hit count."""
    seed_state, n = args
    rng = np.random.Generator(np.random.PCG64(seed_state))
    a = rng.random(n)
    b = rng.random(n)
    c = rng.random(n)
    d = rng.random(n)
    return int(np.count_nonzero(count_hits_B(a, b, c, d))), n


# ----------------------------------------------------------------------------
# method (A): batched companion-matrix eigenvalues
# ----------------------------------------------------------------------------
def real_root_count_companion(p2, p1, p0, tol=1e-7, batch=200_000):
    """Number of real roots of y^3 + p2 y^2 + p1 y + p0, via eigvals of the
    companion matrix.  Returns an int8 array of counts (1 or 3)."""
    n = p2.size
    out = np.empty(n, dtype=np.int8)
    for i in range(0, n, batch):
        j = min(i + batch, n)
        m = j - i
        C = np.zeros((m, 3, 3), dtype=np.float64)
        C[:, 0, 0] = -p2[i:j]
        C[:, 0, 1] = -p1[i:j]
        C[:, 0, 2] = -p0[i:j]
        C[:, 1, 0] = 1.0
        C[:, 2, 1] = 1.0
        w = np.linalg.eigvals(C)                       # (m,3) complex
        isreal = np.abs(w.imag) <= tol * (1.0 + np.abs(w))
        out[i:j] = isreal.sum(axis=1).astype(np.int8)
    return out


# ----------------------------------------------------------------------------
# method (C): analytic d-integral + scrambled Sobol' QMC over (a,b,c)
# ----------------------------------------------------------------------------
def d_measure(a, b, c):
    """For fixed (a,b,c), the Lebesgue measure of {d in [0,1] : 3 real roots}."""
    q = a * c
    D = b * b - 3.0 * q
    ok = D > 0.0
    s = np.sqrt(np.where(ok, D, 0.0))
    ym = (-b - s) / 3.0
    yp = (-b + s) / 3.0
    h = lambda y: ((y + b) * y + q) * y             # g minus its constant term
    lo = np.maximum(0.0, -h(ym))                    # r = a^2 d must be >= this
    hi = np.minimum(a * a, -h(yp))                  # ... and <= this
    length = np.maximum(0.0, hi - lo) / (a * a)     # convert r-length to d-length
    return np.where(ok, length, 0.0)


def qmc_estimate(m=22, n_scramble=12, seed=555_111):
    from scipy.stats import qmc
    vals = []
    for k in range(n_scramble):
        eng = qmc.Sobol(d=3, scramble=True, seed=seed + 7919 * k)
        u = eng.random_base2(m)
        vals.append(float(np.mean(d_measure(u[:, 0], u[:, 1], u[:, 2]))))
    vals = np.array(vals)
    return vals.mean(), vals.std(ddof=1) / math.sqrt(len(vals)), 2 ** m, n_scramble


# ----------------------------------------------------------------------------
# validation of the root counter against the three KNOWN cells of the table
# ----------------------------------------------------------------------------
def count_hits_general(a, b, c, d):
    """3-real-root test for arbitrary real a (a may be negative).  The real-root
    count of f and of -f coincide, so flip the sign when a < 0."""
    sgn = np.where(a < 0.0, -1.0, 1.0)
    return count_hits_B(a * sgn, b * sgn, c * sgn, d * sgn)


def validate(n=40_000_000, seed=13_579_246):
    """Reproduce Thm 1, Thm 2, Thm 3 with the SAME numerical root counter."""
    rng = np.random.default_rng(seed)
    out = []
    ln3 = math.log(3.0)

    # Thm 2: monic x^3 + a x^2 + b x + c, coeffs U[0,1]  ->  1/2880
    u = rng.random((3, n))
    h = count_hits_B(np.ones(n), u[0], u[1], u[2])
    out.append(("Thm2 monic  U[0,1]^3", h.mean(), n, 1.0 / 2880.0))
    del u, h

    # Thm 1: monic x^3 + a x^2 + b x + c, coeffs U[-1,1] -> 383/4860 + ln3/48
    u = 2.0 * rng.random((3, n)) - 1.0
    h = count_hits_B(np.ones(n), u[0], u[1], u[2])
    out.append(("Thm1 monic  U[-1,1]^3", h.mean(), n, 383.0 / 4860.0 + ln3 / 48.0))
    del u, h

    # Thm 3: a x^3 + b x^2 + c x + d, coeffs U[-1,1] -> 641/2430 - ln3/24
    u = 2.0 * rng.random((4, n)) - 1.0
    h = count_hits_general(u[0], u[1], u[2], u[3])
    out.append(("Thm3 nonmonic U[-1,1]^4", h.mean(), n, 641.0 / 2430.0 - ln3 / 24.0))
    del u, h
    return out


# ----------------------------------------------------------------------------
def wilson(k, n, z=1.959963984540054):
    """Wilson score interval (better than normal at small p)."""
    p = k / n
    den = 1.0 + z * z / n
    centre = (p + z * z / (2 * n)) / den
    half = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / den
    return centre - half, centre + half


def main():
    lines = []
    def say(s=""):
        print(s, flush=True)
        lines.append(s)

    say("=" * 78)
    say("INDEPENDENT Monte Carlo: P(a x^3 + b x^2 + c x + d has 3 real roots),")
    say("                          a,b,c,d iid U[0,1]")
    say("Real roots are COUNTED NUMERICALLY.  The degree-4 discriminant")
    say("polynomial is never formed anywhere in this script.")
    say("=" * 78)
    say(f"numpy {np.__version__}   python {sys.version.split()[0]}")
    say()

    # ---------------- validation on the three known cells ---------------------
    say("-" * 78)
    say("VALIDATION of the numerical root counter against the three KNOWN cells")
    say("-" * 78)
    t0 = time.time()
    for name, est, nn, exact in validate():
        se_v = math.sqrt(est * (1 - est) / nn)
        say(f"  {name:24s} N={nn}  est={est:.9f}  exact={exact:.9f}  "
            f"dev={(est-exact)/se_v:+6.2f} sigma")
    say(f"  elapsed {time.time()-t0:.1f}s")
    say()

    # ---------------- (A) vs (B) cross-check ---------------------------------
    say("-" * 78)
    say(f"CROSS-CHECK  (A) companion eigenvalues  vs  (B) critical-point test")
    say(f"N_cross = {N_CROSS}, seed = {CROSS_SEED}, same samples for both")
    say("-" * 78)
    t0 = time.time()
    rng = np.random.default_rng(CROSS_SEED)
    a = rng.random(N_CROSS); b = rng.random(N_CROSS)
    c = rng.random(N_CROSS); d = rng.random(N_CROSS)

    hitB      = count_hits_B(a, b, c, d)
    hitB_raw  = count_hits_B_raw(a, b, c, d)

    cntA      = real_root_count_companion(b, a * c, a * a * d)          # scaled
    hitA      = cntA == 3
    cntA_raw  = real_root_count_companion(b / a, c / a, d / a)          # raw
    hitA_raw  = cntA_raw == 3
    say(f"elapsed {time.time()-t0:.1f}s")
    say()
    say(f"  (B) scaled  hits = {int(hitB.sum())}    p = {hitB.mean():.9f}")
    say(f"  (B) raw     hits = {int(hitB_raw.sum())}    p = {hitB_raw.mean():.9f}")
    say(f"  (A) scaled  hits = {int(hitA.sum())}    p = {hitA.mean():.9f}")
    say(f"  (A) raw     hits = {int(hitA_raw.sum())}    p = {hitA_raw.mean():.9f}")
    say()

    def agree(name1, h1, name2, h2):
        dis = np.nonzero(h1 != h2)[0]
        rate = 1.0 - dis.size / N_CROSS
        say(f"  agreement {name1} vs {name2}: {N_CROSS - dis.size}/{N_CROSS}"
            f"  = {rate:.9f}   ({dis.size} disagreements)")
        return dis

    dis_AB      = agree("(A)scaled", hitA,     "(B)scaled", hitB)
    _           = agree("(B)scaled", hitB,     "(B)raw",    hitB_raw)
    _           = agree("(A)scaled", hitA,     "(A)raw",    hitA_raw)

    # how degenerate are the disagreements?  measure via the normalised
    # separation of the two critical values of the *scaled* monic cubic.
    if dis_AB.size:
        say()
        say("  disagreements (A)scaled vs (B)scaled -- degeneracy diagnostic")
        say("  (Delta4 = discriminant of the monic g, computed ONLY here, for")
        say("   diagnosis of near-degeneracy; it plays no role in any estimate)")
        i = dis_AB
        p2, p1, p0 = b[i], (a * c)[i], (a * a * d)[i]
        Delta4 = (18 * p2 * p1 * p0 - 4 * p2 ** 3 * p0 + p2 ** 2 * p1 ** 2
                  - 4 * p1 ** 3 - 27 * p0 ** 2)
        say(f"    count = {i.size}")
        say(f"    |Delta_g| : max = {np.abs(Delta4).max():.3e}, "
            f"median = {np.median(np.abs(Delta4)):.3e}")
        for k in range(min(10, i.size)):
            j = i[k]
            say(f"    a={a[j]:.17g} b={b[j]:.17g} c={c[j]:.17g} d={d[j]:.17g}"
                f"  Delta_g={Delta4[k]:+.3e}  A={cntA[j]} B={int(hitB[j])}")
    del a, b, c, d, hitB, hitB_raw, hitA, hitA_raw, cntA, cntA_raw
    say()

    # ---------------- (B) production run -------------------------------------
    say("-" * 78)
    say(f"PRODUCTION RUN -- method (B), {N_WORKERS} worker processes")
    say(f"N = {N_TOTAL}, chunk = {CHUNK}, master seed = {SEED}")
    say("-" * 78)
    n_chunks = N_TOTAL // CHUNK
    assert n_chunks * CHUNK == N_TOTAL
    ss = np.random.SeedSequence(SEED)
    children = ss.spawn(n_chunks)
    tasks = [(ch, CHUNK) for ch in children]

    t0 = time.time()
    hits = 0
    done = 0
    with mp.get_context("fork").Pool(processes=N_WORKERS) as pool:
        for h, n in pool.imap_unordered(worker, tasks, chunksize=1):
            hits += h
            done += n
            if done % (100 * CHUNK) == 0:
                el = time.time() - t0
                print(f"    {done:>13d}/{N_TOTAL}  hits={hits:>10d}  "
                      f"p={hits/done:.9f}  {el:7.1f}s", flush=True)
    el = time.time() - t0
    say(f"elapsed {el:.1f}s  ({N_TOTAL/el/1e6:.2f} Msamples/s)")
    say()

    n = done
    p = hits / n
    se = math.sqrt(p * (1 - p) / n)
    lo_n, hi_n = p - 1.959963984540054 * se, p + 1.959963984540054 * se
    lo_w, hi_w = wilson(hits, n)

    say(f"  N            = {n}")
    say(f"  hits         = {hits}")
    say(f"  p_hat        = {p!r}")
    say(f"  p_hat        = {p:.12f}")
    say(f"  std error    = {se:.3e}")
    say(f"  95% CI (normal) = [{lo_n:.12f}, {hi_n:.12f}]")
    say(f"  95% CI (Wilson) = [{lo_w:.12f}, {hi_w:.12f}]")
    say(f"  1/p_hat      = {1.0/p:.6f}")
    say()

    # ---------------- (C) deterministic QMC check ----------------------------
    say("-" * 78)
    say("DETERMINISTIC CROSS-CHECK -- d integrated out exactly, scrambled")
    say("Sobol' QMC over (a,b,c).  Independent of all sampling above.")
    say("-" * 78)
    t0 = time.time()
    try:
        q_mean, q_se, q_n, q_k = qmc_estimate()
        say(f"  {q_k} independent scramblings x {q_n} Sobol' points")
        say(f"  P_qmc        = {q_mean!r}")
        say(f"  P_qmc        = {q_mean:.12f}   (+- {q_se:.2e}, s.e. over scramblings)")
        say(f"  P_qmc - p_hat= {q_mean - p:+.3e}   "
            f"({(q_mean - p)/math.sqrt(se**2 + q_se**2):+.2f} combined sigma)")
    except Exception as e:                                   # pragma: no cover
        say(f"  QMC check failed: {e!r}")
    say(f"  elapsed {time.time()-t0:.1f}s")
    say()

    # ---------------- reference numbers --------------------------------------
    say("-" * 78)
    say("CONTEXT (not used in the estimate)")
    say(f"  1/5760              = {1/5760:.12f}")
    say(f"  p_hat - 1/5760      = {p - 1/5760:+.12f}   "
            f"=> S = 2*(p_hat - 1/5760) = {2*(p - 1/5760):.12f}")
    say("-" * 78)

    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    with open(OUT, "w") as f:
        f.write("\n".join(lines) + "\n")
    print(f"\nwritten to {OUT}")


if __name__ == "__main__":
    main()
