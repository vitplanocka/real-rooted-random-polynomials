"""Serious constant-recognition search for P_A at ~50 digits.

P_A = P(x^3 + a x^2 + b x + c has 3 distinct real roots), (a,b,c) iid N(0,1).

The point of this script is NOT to find a closed form (there probably isn't
one).  The point is to produce a *documented negative*: an explicit record of
the basis, the transformations, the term-counts and the coefficient bounds that
were searched, plus an honest over-determination test applied to anything PSLQ
coughs up.

Over-determination test used throughout
---------------------------------------
A relation  sum_i n_i * v_i = 0  among n reals, with integer coefficients of
size up to M, is expected to turn up *by chance* once the search space
M^n exceeds the precision, i.e. once  n * log10(M) >~ D  where D is the number
of correct digits available.  So we define

    spent  = sum_i log10(max(|n_i|, 1))       ("digits burned on coefficients")
    margin = D_confirmed - spent

and require margin to be large (>= 20 digits here) before a relation is even
worth a second look.  Everything else is junk by construction.
"""
import itertools
import json
import os
import sys
import time

from mpmath import mp, mpf, mpmathify

HERE = os.path.dirname(os.path.abspath(__file__))
RESULTS = os.path.join(HERE, "..", "results")

# ---------------------------------------------------------------- the value --
# 54 digits agreed by four mutually independent quadrature routes (plus a fifth
# mpmath-native tanh-sinh route).  We *search* with 50 and *verify* against 54.
P_A_54 = "0.169929382623479502656443157131761902134057261454631531"
P_A_50 = "0.16992938262347950265644315713176190213405726145463"
D_SEARCH = 50
D_CONFIRM = 54

MARGIN_REQUIRED = 20.0   # digits of over-determination demanded of a candidate


def constant_pool():
    """Named constants plausibly arising in Gaussian / real-root problems."""
    pi = mp.pi
    sqrt = mp.sqrt
    log = mp.log
    g = mp.gamma
    P = {}
    # --- powers of pi -------------------------------------------------------
    P["pi"] = pi
    P["pi^2"] = pi ** 2
    P["pi^3"] = pi ** 3
    P["1/pi"] = 1 / pi
    P["1/pi^2"] = 1 / pi ** 2
    P["sqrt(pi)"] = sqrt(pi)
    P["1/sqrt(pi)"] = 1 / sqrt(pi)
    # --- algebraic ----------------------------------------------------------
    P["sqrt2"] = sqrt(2)
    P["sqrt3"] = sqrt(3)
    P["sqrt5"] = sqrt(5)
    P["1/sqrt3"] = 1 / sqrt(3)
    P["2^(1/3)"] = mpf(2) ** (mpf(1) / 3)
    P["3^(1/3)"] = mpf(3) ** (mpf(1) / 3)
    P["sqrt2/pi"] = sqrt(2) / pi
    P["sqrt3/pi"] = sqrt(3) / pi
    P["sqrt3/(2pi)"] = sqrt(3) / (2 * pi)
    P["sqrt2/sqrt(pi)"] = sqrt(2) / sqrt(pi)
    # --- logs ---------------------------------------------------------------
    P["log2"] = log(2)
    P["log3"] = log(3)
    P["log5"] = log(5)
    P["log2/pi"] = log(2) / pi
    P["log3/pi"] = log(3) / pi
    P["log(1+sqrt2)"] = log(1 + sqrt(2))
    P["log(2+sqrt3)"] = log(2 + sqrt(3))
    P["sqrt2*log(1+sqrt2)"] = sqrt(2) * log(1 + sqrt(2))
    P["sqrt3*log(2+sqrt3)"] = sqrt(3) * log(2 + sqrt(3))
    P["log(1+sqrt2)/pi"] = log(1 + sqrt(2)) / pi
    P["log(2+sqrt3)/pi"] = log(2 + sqrt(3)) / pi
    # --- orthant-probability angles ----------------------------------------
    P["atan(sqrt2)/pi"] = mp.atan(sqrt(2)) / pi
    P["atan(1/sqrt2)/pi"] = mp.atan(1 / sqrt(2)) / pi
    P["atan(sqrt2)"] = mp.atan(sqrt(2))
    P["asin(1/3)/pi"] = mp.asin(mpf(1) / 3) / pi
    P["acos(-1/3)/pi"] = mp.acos(-mpf(1) / 3) / pi
    P["acos(1/3)/pi"] = mp.acos(mpf(1) / 3) / pi
    P["asin(1/4)/pi"] = mp.asin(mpf(1) / 4) / pi
    P["asin(1/sqrt3)/pi"] = mp.asin(1 / sqrt(3)) / pi
    P["asin(2/3)/pi"] = mp.asin(mpf(2) / 3) / pi
    P["asin(1/3)"] = mp.asin(mpf(1) / 3)
    P["atan(1/3)/pi"] = mp.atan(mpf(1) / 3) / pi
    P["atan(sqrt2/2)/pi"] = mp.atan(sqrt(2) / 2) / pi
    # --- "classical" transcendentals ---------------------------------------
    P["catalan"] = mp.catalan
    P["catalan/pi"] = mp.catalan / pi
    P["zeta(3)"] = mp.zeta(3)
    P["euler"] = mp.euler
    P["e"] = mp.e
    P["1/e"] = 1 / mp.e
    P["exp(-1/2)"] = mp.exp(mpf(-1) / 2)
    # --- Gamma values -------------------------------------------------------
    P["gamma(1/4)"] = g(mpf(1) / 4)
    P["gamma(1/4)^2"] = g(mpf(1) / 4) ** 2
    P["gamma(1/4)^2/pi^(3/2)"] = g(mpf(1) / 4) ** 2 / pi ** mpf(1.5)
    P["gamma(1/3)"] = g(mpf(1) / 3)
    P["gamma(1/3)^3"] = g(mpf(1) / 3) ** 3
    P["gamma(1/6)"] = g(mpf(1) / 6)
    # --- erf-adjacent -------------------------------------------------------
    P["erf(1)"] = mp.erf(1)
    P["erf(1/sqrt2)"] = mp.erf(1 / sqrt(2))
    return P


def transformations(x):
    """(name, value) pairs: a closed form often only appears after rescaling."""
    pi = mp.pi
    sqrt = mp.sqrt
    T = [
        ("x", x),
        ("pi*x", pi * x),
        ("x/pi", x / pi),
        ("pi^2*x", pi ** 2 * x),
        ("x*sqrt3", x * sqrt(3)),
        ("x*sqrt2", x * sqrt(2)),
        ("4*x", 4 * x),
        ("1/4 - x", mpf(1) / 4 - x),
        ("1/2 - x", mpf(1) / 2 - x),
        ("1 - 3*x", 1 - 3 * x),
        ("1 - x", 1 - x),
        ("1/x", 1 / x),
        ("x^2", x ** 2),
        ("exp(x)", mp.exp(x)),
        ("log(x)", mp.log(x)),
        ("x*sqrt(pi)", x * sqrt(pi)),
        # -- supplementary multiplicative normalisations (added after round 1) --
        ("pi^3*x", pi ** 3 * x),
        ("x/pi^2", x / pi ** 2),
        ("x/sqrt(pi)", x / sqrt(pi)),
        ("sqrt(x)", sqrt(x)),
        ("x*pi/sqrt3", x * pi / sqrt(3)),
    ]
    return T


# ------------------------------------------------------------------ helpers --

def spent_digits(rel):
    return sum(mp.log10(max(abs(int(v)), 1)) for v in rel)


def verify(rel, vals_hi):
    """Residual of the relation evaluated at higher precision."""
    s = mp.mpf(0)
    for n, v in zip(rel, vals_hi):
        s += int(n) * v
    scale = max(abs(int(n)) for n in rel)
    return s, s / scale


def pslq_sweep(tname, tval_fn, pool_names, pool_fn, k, maxcoeff, tol, log):
    """All k-subsets of the pool, relation [t, 1, c_1..c_k]."""
    hits = []
    tval = tval_fn()
    ncall = 0
    t0 = time.time()
    for combo in itertools.combinations(pool_names, k):
        vec = [tval, mpf(1)] + [pool_fn[c] for c in combo]
        ncall += 1
        rel = mp.pslq(vec, tol=tol, maxcoeff=maxcoeff, maxsteps=8000)
        if rel and rel[0] != 0:
            sp = float(spent_digits(rel))
            hits.append({
                "transform": tname, "constants": list(combo),
                "relation": [int(v) for v in rel],
                "layout": "[t, 1] + constants",
                "maxcoeff_allowed": maxcoeff,
                "spent_digits": round(sp, 2),
                "margin_vs_54": round(D_CONFIRM - sp, 2),
                "credible": bool(D_CONFIRM - sp >= MARGIN_REQUIRED),
            })
    log(f"    k={k} maxcoeff=1e{int(round(mp.log10(maxcoeff)))} "
        f"subsets={ncall} hits={len(hits)} ({time.time()-t0:.1f}s)")
    return hits


def run_campaign(xstr_search, xstr_confirm, label, log, k_specs,
                 do_transforms=True):
    mp.dps = 70
    x_s = mpmathify(xstr_search)
    x_c = mpmathify(xstr_confirm)
    pool = constant_pool()
    pool_names = sorted(pool.keys())

    out = {
        "label": label,
        "value_searched": xstr_search,
        "value_confirm": xstr_confirm,
        "digits_searched": D_SEARCH,
        "digits_confirm": D_CONFIRM,
        "pool_size": len(pool_names),
        "pool": pool_names,
        "term_specs": [{"named_constants": k, "total_terms": k + 2,
                        "maxcoeff": m, "pslq_tol": f"1e-{tt}"}
                       for (k, m, tt) in k_specs],
        "identify_hits": [],
        "pslq_hits": [],
    }

    transforms = transformations(x_s) if do_transforms else [("x", x_s)]
    out["transformations"] = [t[0] for t in transforms]

    # ---- 1. mpmath.identify -------------------------------------------------
    bases = [
        [], ["pi"], ["pi", "log(2)"], ["pi", "log(2)", "log(3)"],
        ["pi", "sqrt(2)", "sqrt(3)"],
        ["pi", "log(2)", "log(3)", "sqrt(2)", "sqrt(3)"],
        ["catalan", "pi"], ["gamma(0.25)", "pi"],
        ["log(3)"], ["log(2)"], ["sqrt(3)", "pi"],
        ["zeta(3)", "pi"], ["euler", "pi"],
    ]
    out["identify_bases"] = [b or ["<rationals only>"] for b in bases]
    out["identify_maxcoeff"] = 10 ** 5
    log("  -- mpmath.identify --")
    n_id = 0
    for tname, tval in transforms:
        for b in bases:
            for tol_exp in (44, 40):
                r = mp.identify(tval, b, tol=mpf(10) ** (-tol_exp),
                                maxcoeff=10 ** 5)
                if r:
                    n_id += 1
                    log(f"    {tname}: basis={b or 'rationals'} "
                        f"tol=1e-{tol_exp} -> {r}")
                    out["identify_hits"].append(
                        {"transform": tname, "basis": b or ["<rationals>"],
                         "tol": f"1e-{tol_exp}", "result": str(r)})
    if n_id == 0:
        log("    (no hit for any transform / basis / tolerance)")

    # ---- 2. PSLQ sweeps -----------------------------------------------------
    log("  -- PSLQ subset sweeps --")
    for tname, tval in transforms:
        log(f"   transform {tname}:")
        for (k, maxcoeff, tol_exp) in k_specs:
            tol = mpf(10) ** (-tol_exp)
            hits = pslq_sweep(tname, lambda tv=tval: tv, pool_names, pool,
                              k, maxcoeff, tol, log)
            out["pslq_hits"].extend(hits)

    # ---- 3. verify every hit against the 54-digit value ---------------------
    log("  -- verification of PSLQ hits against 54 digits --")
    tf_confirm = dict(transformations(x_c))
    mp.dps = 90
    survivors = []
    for h in out["pslq_hits"]:
        tv = tf_confirm[h["transform"]]
        vec = [tv, mpf(1)] + [pool[c] for c in h["constants"]]
        resid, rel_resid = verify(h["relation"], vec)
        h["residual_at_54_digits"] = mp.nstr(resid, 8)
        h["residual_scaled"] = mp.nstr(rel_resid, 8)
        h["survives"] = bool(h["credible"] and abs(rel_resid) < mpf(10) ** -48)
        if h["survives"]:
            survivors.append(h)
    out["n_pslq_hits"] = len(out["pslq_hits"])
    out["n_credible"] = sum(1 for h in out["pslq_hits"] if h["credible"])
    out["n_survivors"] = len(survivors)
    out["survivors"] = survivors
    log(f"    hits={out['n_pslq_hits']}  passing-margin={out['n_credible']}  "
        f"surviving={out['n_survivors']}")
    return out
