#!/usr/bin/env python
"""
Independent verification that

    F_a := vol_3 { (b,c,d) in [0,1]^3 : x^3 + b x^2 + c x + d has three real roots }

equals 1/2880 = 3.472222...e-4  (Theorem 2 of ~/math/real-rooted-random-polynomials).

Two structurally different computations:
  (1) plain Monte Carlo on [0,1]^3 using the sign of the cubic discriminant,
      N = 6e9, 6 worker processes;
  (2) deterministic mpmath 2-D quadrature of the d-band length over (b,c),
      >= 25 working digits, domain split at the non-smooth boundaries.
Plus (3) an exact symbolic derivation of the same 2-D integral (sympy), which is
      logically independent of both.

Usage:  face_a_check.py [mc|quad|sym|all]
        FACE_A_SEED=<int> face_a_check.py mc     # independent MC replicate
"""
import sys, os, time, math

TARGET_STR = "1/2880"

# ----------------------------------------------------------------------------
# Part 0: geometry of the d-band  (derived here, not assumed)
# ----------------------------------------------------------------------------
# f(x) = x^3 + b x^2 + c x + d,  f'(x) = 3x^2 + 2bx + c.
# f' has two distinct real roots iff b^2 - 3c > 0.  Put s = sqrt(b^2-3c);
#   x_- = (-b-s)/3  (local MAX, since f''(x_-) = -2s < 0)
#   x_+ = (-b+s)/3  (local MIN, since f''(x_+) = +2s > 0)
# f is affine in d with coefficient +1, so with g(x) := x^3+bx^2+cx,
#   f(x_-) >= 0  <=>  d >= -g(x_-) =: d_lo
#   f(x_+) <= 0  <=>  d <= -g(x_+) =: d_hi
# Writing u := -x_+ = (b-s)/3 and v := -x_- = (b+s)/3 and using 3u^2-2bu+c = 0
# (resp. for v) to eliminate c, one gets the compact forms
#   d_hi = u^2 (b - 2u),   d_lo = v^2 (b - 2v),
# and the band width
#   d_hi - d_lo = (4/27) (b^2 - 3c)^{3/2}          <-- 4/27, NOT 2/27.
# Both are verified symbolically in sym_checks().

def band(b, c, sqrt, zero):
    """Return (d_lo, d_hi) for given b,c with b^2>3c.  Generic (works for
    float and mpmath types).  Uses the u,v form."""
    s = sqrt(b*b - 3*c)
    u = (b - s)/3
    v = (b + s)/3
    return v*v*(b - 2*v), u*u*(b - 2*u)

def band_length(b, c, sqrt):
    """|[d_lo,d_hi] cap [0,1]|."""
    if b*b <= 3*c:
        return 0*b
    lo, hi = band(b, c, sqrt, 0)
    lo = max(lo, 0*b)
    hi = min(hi, 1 + 0*b)
    return hi - lo if hi > lo else 0*b

# ----------------------------------------------------------------------------
# Part 1: Monte Carlo
# ----------------------------------------------------------------------------
N_TOTAL   = 6_000_000_000
N_WORKERS = 6                     # shared machine: exactly 6, do not raise
CHUNK     = 10_000_000
BASE_SEED = int(os.environ.get("FACE_A_SEED", "20260818"))   # replicate run used FACE_A_SEED=777000111

def mc_worker(args):
    import numpy as np
    wid, n_this = args
    rng = np.random.default_rng([BASE_SEED, wid])
    hits = 0
    done = 0
    while done < n_this:
        n = min(CHUNK, n_this - done)
        b = rng.random(n); c = rng.random(n); d = rng.random(n)
        # discriminant of x^3+bx^2+cx+d :
        #   D = 18bcd - 4b^3 d + b^2 c^2 - 4c^3 - 27 d^2
        # D > 0  <=>  three distinct real roots.
        b2 = b*b
        t = 18.0*b*c
        t -= 4.0*b2*b
        t *= d
        t += b2*c*c
        t -= 4.0*c*c*c
        t -= 27.0*d*d
        hits += int(np.count_nonzero(t > 0.0))
        done += n
    return hits, done

def run_mc(log):
    from multiprocessing import Pool
    per = N_TOTAL // N_WORKERS
    jobs = [(w, per) for w in range(N_WORKERS)]
    jobs[-1] = (N_WORKERS-1, N_TOTAL - per*(N_WORKERS-1))
    t0 = time.time()
    with Pool(N_WORKERS) as pool:
        res = pool.map(mc_worker, jobs)
    el = time.time() - t0
    hits = sum(r[0] for r in res)
    n    = sum(r[1] for r in res)
    p    = hits / n
    se   = math.sqrt(p*(1-p)/n)
    tgt  = 1.0/2880.0
    dev  = p - tgt
    sig  = dev/se
    log("")
    log("=== (1) MONTE CARLO  (plain, discriminant sign, unstratified) ===")
    log("  samples N            = %d  (%d procs x %d chunks of %d)" % (n, N_WORKERS, -(-per//CHUNK), CHUNK))
    log("  wall time            = %.1f s" % el)
    log("  hits                 = %d" % hits)
    log("  estimate  F_a_MC     = %.12e" % p)
    log("  std error            = %.12e   (rel %.3e)" % (se, se/p))
    log("  target 1/2880        = %.12e" % tgt)
    log("  deviation            = %+.6e" % dev)
    log("  deviation / sigma    = %+.4f" % sig)
    log("  95%% CI               = [%.10e, %.10e]" % (p-1.96*se, p+1.96*se))
    return p, se, sig

# ----------------------------------------------------------------------------
# Part 1b: stratified / conditional MC (variance-reduced cross-check)
# ----------------------------------------------------------------------------
# Integrate out d analytically: conditional on (b,c) the d-measure is
# band_length(b,c).  So F_a = E_{b,c}[ L(b,c) ] with (b,c) ~ U[0,1]^2.
# This is a different estimator (structurally: 2-D MC of a known kernel),
# with far smaller variance.
def cmc_worker(args):
    import numpy as np
    wid, n_this = args
    rng = np.random.default_rng([BASE_SEED + 991, wid])
    tot = 0.0; tot2 = 0.0; done = 0
    while done < n_this:
        n = min(CHUNK, n_this - done)
        b = rng.random(n); c = rng.random(n)
        disc = b*b - 3.0*c
        m = disc > 0.0
        bb = b[m]; s = np.sqrt(disc[m])
        u = (bb - s)/3.0
        v = (bb + s)/3.0
        d_hi = u*u*(bb - 2.0*u)
        d_lo = v*v*(bb - 2.0*v)
        np.clip(d_lo, 0.0, 1.0, out=d_lo)
        np.clip(d_hi, 0.0, 1.0, out=d_hi)
        L = d_hi - d_lo
        np.maximum(L, 0.0, out=L)
        tot += float(L.sum()); tot2 += float((L*L).sum())
        done += n
    return tot, tot2, done

def run_cmc(log, n_total=6_000_000_000):
    from multiprocessing import Pool
    per = n_total // N_WORKERS
    jobs = [(w, per) for w in range(N_WORKERS)]
    jobs[-1] = (N_WORKERS-1, n_total - per*(N_WORKERS-1))
    t0 = time.time()
    with Pool(N_WORKERS) as pool:
        res = pool.map(cmc_worker, jobs)
    el = time.time() - t0
    tot = sum(r[0] for r in res); tot2 = sum(r[1] for r in res); n = sum(r[2] for r in res)
    mean = tot/n
    var  = max(tot2/n - mean*mean, 0.0)
    se   = math.sqrt(var/n)
    tgt  = 1.0/2880.0
    log("")
    log("=== (1b) CONDITIONAL / STRATIFIED MC  (d integrated out analytically) ===")
    log("  (b,c) samples        = %d,  wall %.1f s" % (n, el))
    log("  estimate  F_a_CMC    = %.14e" % mean)
    log("  std error            = %.4e   (rel %.3e)" % (se, se/mean))
    log("  deviation from 1/2880= %+.6e   (%+.3f sigma)" % (mean-tgt, (mean-tgt)/se))
    return mean, se

# ----------------------------------------------------------------------------
# Part 2: deterministic high-precision quadrature
# ----------------------------------------------------------------------------
def run_quad(log, dps=40):
    import mpmath as mp
    mp.mp.dps = dps
    sqrt = mp.sqrt

    # --- structural facts, verified numerically below ---
    # (i)  d_hi = u^2(b-2u) with u=(b-s)/3 in [0,b/3];  d/du[bu^2-2u^3]=2u(b-3u)>=0
    #      so d_hi <= b^3/27 <= 1/27 < 1  ==>  the upper clip d<=1 NEVER binds.
    # (ii) d_lo = v^2(b-2v) with v=(b+s)/3;  d_lo <= 0  <=>  v >= b/2  <=>  s >= b/2
    #      <=>  c <= b^2/4.  So the lower clip d>=0 binds exactly on c < b^2/4.
    # Hence for fixed b the inner integrand is
    #      c in (0, b^2/4)     : L = d_hi                       (lower clip active)
    #      c in (b^2/4, b^2/3) : L = d_hi - d_lo = (4/27) s^3   (no clip)
    # and L = 0 for c > b^2/3.  Split points: c = b^2/4 (kink) and c = b^2/3
    # (algebraic 3/2-power endpoint).

    def d_hi_f(b, c):
        s = sqrt(b*b - 3*c); u = (b - s)/3
        return u*u*(b - 2*u)
    def d_lo_f(b, c):
        s = sqrt(b*b - 3*c); v = (b + s)/3
        return v*v*(b - 2*v)
    def L_raw(b, c):
        """Completely naive |[d_lo,d_hi] cap [0,1]| -- no structural shortcuts."""
        if b*b <= 3*c:
            return mp.mpf(0)
        lo = max(d_lo_f(b, c), mp.mpf(0))
        hi = min(d_hi_f(b, c), mp.mpf(1))
        return hi - lo if hi > lo else mp.mpf(0)

    # --- structural verification sweep ---
    worst_hi = mp.mpf(0); bad_clip = 0
    ng = 400
    for i in range(1, ng):
        bb = mp.mpf(i)/ng
        for j in range(0, ng):
            cc = (mp.mpf(j)/ng) * (bb*bb/3)
            if bb*bb <= 3*cc: continue
            worst_hi = max(worst_hi, d_hi_f(bb, cc))
            neg = d_lo_f(bb, cc) < 0
            pred = cc < bb*bb/4
            if neg != pred and abs(cc - bb*bb/4) > mp.mpf('1e-20'):
                bad_clip += 1
    log("")
    log("=== (2) DETERMINISTIC QUADRATURE (mpmath, dps=%d) ===" % dps)
    log("  structural checks:")
    log("    max d_hi over region = %s   (< 1, so clip d<=1 never binds; bound 1/27=%s)"
        % (mp.nstr(worst_hi, 12), mp.nstr(mp.mpf(1)/27, 12)))
    log("    sign(d_lo) vs c<b^2/4 mismatches on %dx%d grid = %d" % (ng, ng, bad_clip))

    # --- 2-D integral, raw variables, split at the kink and the endpoint ---
    def inner(b):
        if b <= 0: return mp.mpf(0)
        c1 = b*b/4
        c2 = b*b/3
        I1 = mp.quad(lambda c: L_raw(b, c), [mp.mpf(0), c1])
        I2 = mp.quad(lambda c: L_raw(b, c), [c1, c2])
        return I1 + I2

    t0 = time.time()
    F_raw = mp.quad(inner, [mp.mpf(0), mp.mpf(1)])
    t1 = time.time()

    # --- second, structurally different evaluation: substitute c=(b^2-s^2)/3,
    #     dc = -(2s/3) ds, which removes the algebraic singularity entirely and
    #     makes the inner integrand polynomial.  s in (b/2,b) <-> c in (0,b^2/4).
    def inner_s(b):
        if b <= 0: return mp.mpf(0)
        # region A: s in (b/2, b),  L = d_hi = (b-s)^2 (b+2s)/27
        A = mp.quad(lambda s: ((b-s)**2*(b+2*s)/27) * (2*s/3), [b/2, b])
        # region B: s in (0, b/2),  L = (4/27) s^3
        B = mp.quad(lambda s: (mp.mpf(4)/27)*s**3 * (2*s/3), [mp.mpf(0), b/2])
        return A + B
    F_sub = mp.quad(inner_s, [mp.mpf(0), mp.mpf(1)])
    t2 = time.time()

    tgt = mp.mpf(1)/2880
    log("  F_a (raw (b,c) variables, nested tanh-sinh) =")
    log("      %s" % mp.nstr(F_raw, 30))
    log("      time %.1f s" % (t1-t0))
    log("  F_a (s-substituted, polynomial integrands)  =")
    log("      %s" % mp.nstr(F_sub, 30))
    log("      time %.1f s" % (t2-t1))
    log("  |raw - sub|                = %s" % mp.nstr(abs(F_raw-F_sub), 6))
    log("  1/2880                     = %s" % mp.nstr(tgt, 30))
    log("  F_raw - 1/2880             = %s" % mp.nstr(F_raw - tgt, 6))
    log("  F_sub - 1/2880             = %s" % mp.nstr(F_sub - tgt, 6))
    log("  relative dev (raw)         = %s" % mp.nstr((F_raw-tgt)/tgt, 6))
    log("  mpmath.identify(F_raw)     = %s" % str(mp.identify(F_raw)))
    log("  1/F_raw                    = %s" % mp.nstr(1/F_raw, 30))
    return F_raw, F_sub

# ----------------------------------------------------------------------------
# Part 3: exact symbolic evaluation of the same 2-D integral
# ----------------------------------------------------------------------------
def sym_checks(log):
    import sympy as sp
    b, c, d, x, s, t = sp.symbols('b c d x s t', positive=True)
    f  = x**3 + b*x**2 + c*x + d
    S  = sp.sqrt(b**2 - 3*c)
    xm, xp = (-b-S)/3, (-b+S)/3
    log("")
    log("=== (3) SYMBOLIC DERIVATION / EXACT INTEGRAL (sympy) ===")
    log("  f'(x_-) = %s ,  f'(x_+) = %s   (both must be 0)"
        % (sp.simplify(sp.diff(f,x).subs(x,xm)), sp.simplify(sp.diff(f,x).subs(x,xp))))
    log("  f''(x_-) = %s  (<0 => local max)" % sp.simplify(sp.diff(f,x,2).subs(x,xm)))
    d_lo = sp.solve(sp.Eq(f.subs(x,xm),0), d)[0]
    d_hi = sp.solve(sp.Eq(f.subs(x,xp),0), d)[0]
    w    = sp.simplify(sp.expand(d_hi - d_lo))
    log("  d_lo = %s" % sp.factor(sp.expand(d_lo)))
    log("  d_hi = %s" % sp.factor(sp.expand(d_hi)))
    log("  d_hi - d_lo = %s" % w)
    log("  ratio to (b^2-3c)^(3/2) = %s   <-- brief said 2/27; correct value is 4/27"
        % sp.simplify(w/(b**2-3*c)**sp.Rational(3,2)))
    log("  d_hi - u^2(b-2u)|u=(b-s)/3 : %s" % sp.simplify(d_hi - ((b-S)/3)**2*(b-2*(b-S)/3)))
    log("  d_lo - v^2(b-2v)|v=(b+s)/3 : %s" % sp.simplify(d_lo - ((b+S)/3)**2*(b-2*(b+S)/3)))

    # exact inner integral in s (c = (b^2-s^2)/3, dc = -(2s/3) ds)
    LA = ((b-s)**2*(b+2*s)/27) * (sp.Rational(2,3)*s)      # region A, s in (b/2,b)
    LB = (sp.Rational(4,27)*s**3) * (sp.Rational(2,3)*s)   # region B, s in (0,b/2)
    IA = sp.simplify(sp.integrate(LA, (s, b/2, b)))
    IB = sp.simplify(sp.integrate(LB, (s, 0, b/2)))
    inner = sp.simplify(IA + IB)
    tot = sp.simplify(sp.integrate(inner, (b, 0, 1)))
    log("  inner(b) region A = %s ;  region B = %s ;  sum = %s" % (IA, IB, inner))
    log("  F_a exact = int_0^1 inner(b) db = %s" % tot)
    log("  F_a - 1/2880 = %s   (must be 0)" % sp.simplify(tot - sp.Rational(1,2880)))
    return tot

# ----------------------------------------------------------------------------
def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "all"
    out = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                       "results", "face_a_check.txt")
    lines = []
    def log(msg):
        print(msg, flush=True)
        lines.append(msg)
    log("Face-A verification:  F_a =?= 1/2880")
    log("run mode = %s   started %s" % (mode, time.strftime("%Y-%m-%d %H:%M:%S")))
    if mode in ("sym", "all"):  sym_checks(log)
    if mode in ("quad", "all"): run_quad(log)
    if mode in ("mc", "all"):
        run_mc(log)
        run_cmc(log)
    log("")
    log("finished %s" % time.strftime("%Y-%m-%d %H:%M:%S"))
    mo = "a" if (mode != "all" and os.path.exists(out)) else "w"
    with open(out, mo) as fh:
        fh.write("\n".join(lines) + "\n")
    print("\n[written to %s]" % out)

if __name__ == "__main__":
    main()
