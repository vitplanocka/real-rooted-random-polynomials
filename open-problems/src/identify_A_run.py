"""Driver: calibration + full 50-digit search for P_A.  Writes results/identify_A_50digits.json"""
import itertools, json, math, os, sys, time
from multiprocessing import Pool

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from identify_A_search import (constant_pool, transformations, spent_digits,
                               P_A_50, P_A_54, D_CONFIRM, MARGIN_REQUIRED,
                               RESULTS)
from mpmath import mp, mpf, mpmathify

K_SPECS = [(1, 10 ** 10, 45), (2, 10 ** 8, 45), (3, 10 ** 6, 45)]
DEMO_SPEC = (1, 10 ** 16, 45)   # deliberately over-permissive, for illustration

IDENTIFY_BASES = [
    [], ["pi"], ["pi", "log(2)"], ["pi", "log(2)", "log(3)"],
    ["pi", "sqrt(2)", "sqrt(3)"],
    ["pi", "log(2)", "log(3)", "sqrt(2)", "sqrt(3)"],
    ["catalan", "pi"], ["gamma(0.25)", "pi"], ["log(3)"], ["log(2)"],
    ["sqrt(3)", "pi"], ["zeta(3)", "pi"], ["euler", "pi"], ["sqrt(2)"],
    ["log(1+sqrt(2))", "pi"],
]
IDENTIFY_MAXCOEFF = 10 ** 5


def _identify_worker(args):
    xstr, tname = args
    mp.dps = 70
    tval = dict(transformations(mpmathify(xstr)))[tname]
    hits = []
    for b in IDENTIFY_BASES:
        for tol_exp in (44, 40, 36):
            r = mp.identify(tval, b, tol=mpf(10) ** (-tol_exp),
                            maxcoeff=IDENTIFY_MAXCOEFF)
            if r:
                hits.append({"transform": tname, "basis": b or ["<rationals>"],
                             "tol": f"1e-{tol_exp}", "result": str(r)})
    return hits


def _worker(args):
    xstr, tname, k, maxcoeff, tol_exp = args
    mp.dps = 70
    x = mpmathify(xstr)
    tval = dict(transformations(x))[tname]
    pool = constant_pool()
    names = sorted(pool)
    tol = mpf(10) ** (-tol_exp)
    hits = []
    for combo in itertools.combinations(names, k):
        vec = [tval, mpf(1)] + [pool[c] for c in combo]
        rel = mp.pslq(vec, tol=tol, maxcoeff=maxcoeff, maxsteps=8000)
        if rel and rel[0] != 0:
            sp = float(spent_digits(rel))
            hits.append({"transform": tname, "constants": list(combo),
                         "relation": [int(v) for v in rel],
                         "layout": "coeffs multiply [t, 1, c_1, ..., c_k]",
                         "maxcoeff_allowed": maxcoeff,
                         "pslq_tol": f"1e-{tol_exp}",
                         "spent_digits": round(sp, 2),
                         "margin_vs_54_digits": round(D_CONFIRM - sp, 2),
                         "passes_margin_test": bool(D_CONFIRM - sp >= MARGIN_REQUIRED)})
    return (tname, k, len(hits), hits)


def campaign(xstr_search, xstr_confirm, label, k_specs, nproc=12,
             transform_names=None, demo=False):
    mp.dps = 70
    x_s = mpmathify(xstr_search)
    pool = constant_pool()
    names = sorted(pool)
    tfs = transformations(x_s)
    if transform_names is not None:
        tfs = [t for t in tfs if t[0] in transform_names]
    tnames = [t[0] for t in tfs]

    out = {"label": label, "value_searched": xstr_search,
           "value_for_verification": xstr_confirm,
           "digits_searched": len(xstr_search.split('.')[-1]),
           "digits_for_verification": len(xstr_confirm.split('.')[-1]),
           "pool_size": len(names), "pool": names,
           "transformations": tnames,
           "term_specs": [{"n_named_constants": k, "n_terms_total": k + 2,
                           "maxcoeff": m, "pslq_tol": f"1e-{t}",
                           "max_digits_spendable": round(float((k + 2) * mp.log10(m)), 1)}
                          for (k, m, t) in k_specs],
           "identify_bases": [b or ["<rationals only>"] for b in IDENTIFY_BASES],
           "identify_maxcoeff": IDENTIFY_MAXCOEFF,
           "margin_required_digits": MARGIN_REQUIRED,
           "identify_hits": [], "pslq_hits": []}

    # rationality check
    frac = mp.pslq([x_s, mpf(1)], tol=mpf(10) ** -45, maxcoeff=10 ** 24, maxsteps=10 ** 5)
    out["rational_check"] = {"maxcoeff": 10 ** 24,
                            "relation": [int(v) for v in frac] if frac else None}

    # identify (parallel over transforms)
    t0 = time.time()
    with Pool(nproc) as p:
        for hits in p.imap_unordered(_identify_worker,
                                     [(xstr_search, tn) for tn in tnames]):
            out["identify_hits"].extend(hits)
    print(f"  identify: {len(out['identify_hits'])} hits ({time.time()-t0:.1f}s)", flush=True)

    # pslq sweeps (parallel over transform x k)
    jobs = [(xstr_search, tn, k, m, t) for tn in tnames for (k, m, t) in k_specs]
    if demo:
        k, m, t = DEMO_SPEC
        jobs += [(xstr_search, "x", k, m, t)]
    t0 = time.time()
    with Pool(nproc) as p:
        for (tname, k, n, hits) in p.imap_unordered(_worker, jobs):
            if n:
                print(f"    {tname:12s} k={k}: {n} raw hits")
            out["pslq_hits"].extend(hits)
    print(f"  pslq sweeps: {len(jobs)} jobs, {len(out['pslq_hits'])} raw hits "
          f"({time.time()-t0:.1f}s)")

    # verification at higher precision against the 54-digit value
    mp.dps = 90
    x_c = mpmathify(xstr_confirm)
    tfc = dict(transformations(x_c))
    poolc = constant_pool()
    survivors = []
    for h in out["pslq_hits"]:
        vec = [tfc[h["transform"]], mpf(1)] + [poolc[c] for c in h["constants"]]
        s = mp.mpf(0)
        for n_, v_ in zip(h["relation"], vec):
            s += n_ * v_
        scale = max(abs(n_) for n_ in h["relation"])
        h["residual_at_54_digits"] = mp.nstr(s, 8)
        h["residual_over_maxcoeff"] = mp.nstr(s / scale, 8)
        h["verified_at_54_digits"] = bool(abs(s / scale) < mpf(10) ** -48)
        h["survives"] = bool(h["passes_margin_test"] and h["verified_at_54_digits"])
        if h["survives"]:
            survivors.append(h)
    # de-duplicate: a k=1 relation reappears in every k=2/k=3 subset that
    # contains its constant, padded with zero coefficients.  Collapse to support.
    seen = set()
    uniq = []
    for h in out["pslq_hits"]:
        support = [(c, n) for c, n in zip(["<t>", "<1>"] + h["constants"], h["relation"]) if n != 0]
        g = 0
        for _, n in support:
            g = math.gcd(g, abs(n))
        g = g or 1
        sup = tuple(sorted((c, n // g) for c, n in support))
        sup2 = tuple(sorted((c, -n // g) for c, n in support))
        key = (h["transform"], min(sup, sup2))
        h["reduced_support"] = [f"{n}*{c}" for c, n in support]
        if key in seen:
            h["duplicate_of_smaller_relation"] = True
            continue
        seen.add(key)
        h["duplicate_of_smaller_relation"] = False
        uniq.append(h)
    out["n_pslq_raw_hits_with_duplicates"] = len(out["pslq_hits"])
    out["pslq_hits"] = uniq
    out["n_pslq_raw_hits"] = len(out["pslq_hits"])
    out["n_passing_margin_test"] = sum(1 for h in out["pslq_hits"] if h["passes_margin_test"])
    out["n_verified_at_54"] = sum(1 for h in out["pslq_hits"] if h["verified_at_54_digits"])
    survivors = [h for h in out["pslq_hits"] if h["survives"]]
    out["n_survivors"] = len(survivors)
    out["survivors"] = survivors
    print(f"  raw={out['n_pslq_raw_hits']} margin-ok={out['n_passing_margin_test']} "
          f"verified54={out['n_verified_at_54']} SURVIVORS={out['n_survivors']}")
    return out


def algebraic_check(xstr_search, xstr_confirm, transform_names=None,
                    degrees=(2, 3, 4, 5, 6, 8), maxcoeffs=(10**12, 10**9, 10**7, 10**6, 10**5, 10**4)):
    """Is the (transformed) constant algebraic of low degree?  PSLQ on powers."""
    mp.dps = 70
    x = mpmathify(xstr_search)
    tfs = transformations(x)
    if transform_names is not None:
        tfs = [t for t in tfs if t[0] in transform_names]
    xc = mpmathify(xstr_confirm)
    tfc = dict(transformations(xc))
    res = {"degrees": list(degrees), "maxcoeff_by_degree": dict(zip(map(str, degrees), maxcoeffs)),
           "pslq_tol": "1e-45", "hits": []}
    for tname, tval in tfs:
        for d, mc in zip(degrees, maxcoeffs):
            vec = [tval ** i for i in range(d + 1)]
            rel = mp.pslq(vec, tol=mpf(10) ** -45, maxcoeff=mc, maxsteps=20000)
            if rel:
                sp = float(spent_digits(rel))
                mp.dps = 90
                tv = tfc[tname]
                s = sum(int(n) * tv ** i for i, n in enumerate(rel))
                mp.dps = 70
                res["hits"].append({"transform": tname, "degree": d,
                                    "maxcoeff": mc, "poly_coeffs_asc": [int(v) for v in rel],
                                    "spent_digits": round(sp, 2),
                                    "margin_vs_54_digits": round(D_CONFIRM - sp, 2),
                                    "passes_margin_test": bool(D_CONFIRM - sp >= MARGIN_REQUIRED),
                                    "residual_at_54_digits": mp.nstr(s, 8)})
    res["n_hits"] = len(res["hits"])
    res["n_passing_margin"] = sum(1 for h in res["hits"] if h["passes_margin_test"])
    return res
