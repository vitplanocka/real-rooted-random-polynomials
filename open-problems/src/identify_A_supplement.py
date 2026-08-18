"""Round 2: five further multiplicative normalisations, plus an explicit
over-permissive PSLQ probe on P_A itself (to show what a junk 'hit' would be)."""
import json, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from identify_A_run import campaign, K_SPECS
from identify_A_search import P_A_50, P_A_54, constant_pool
from mpmath import mp, mpf, mpmathify

R = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "results")
NEW = ["pi^3*x", "x/pi^2", "x/sqrt(pi)", "sqrt(x)", "x*pi/sqrt3"]

print("=== supplementary transforms ===", flush=True)
sup = campaign(P_A_50, P_A_54, "P_A, supplementary transforms", K_SPECS,
               nproc=10, transform_names=NEW)

# over-permissive probe on P_A itself
mp.dps = 70
x = mpmathify(P_A_50)
pool = constant_pool()
probe = {"note": "deliberately over-permissive: maxcoeff 1e25 on [P_A, 1, c]. "
                 "Any relation found here spends ~60+ digits on coefficients "
                 "against 54 available, i.e. NEGATIVE margin -- shown only to "
                 "document what junk looks like.",
         "maxcoeff": 10 ** 25, "pslq_tol": "1e-45", "runs": []}
for name in ["pi", "log2", "log3", "sqrt3", "catalan", "zeta(3)", "gamma(1/3)"]:
    rel = mp.pslq([x, mpf(1), pool[name]], tol=mpf(10) ** -45,
                  maxcoeff=10 ** 25, maxsteps=200000)
    sp = float(sum(mp.log10(max(abs(v), 1)) for v in rel)) if rel else None
    probe["runs"].append({"constant": name,
                          "relation": [int(v) for v in rel] if rel else None,
                          "spent_digits": None if sp is None else round(sp, 2),
                          "margin_vs_54_digits": None if sp is None else round(54 - sp, 2),
                          "credible": False if sp is None else bool(54 - sp >= 20)})
    print("  ", name, probe["runs"][-1]["spent_digits"], probe["runs"][-1]["margin_vs_54_digits"], flush=True)

main = json.load(open(os.path.join(R, "identify_A_50digits.json")))
main["transformations"] = main["transformations"] + NEW
main["supplementary_round"] = {
    "transformations": NEW,
    "identify_hits": sup["identify_hits"],
    "n_pslq_raw_hits": sup["n_pslq_raw_hits"],
    "n_survivors": sup["n_survivors"],
    "survivors": sup["survivors"],
    "term_specs": sup["term_specs"]}
main["overpermissive_probe_on_P_A"] = probe
main["n_pslq_raw_hits_total"] = main["n_pslq_raw_hits"] + sup["n_pslq_raw_hits"]
main["n_survivors_total"] = main["n_survivors"] + sup["n_survivors"]
main["note_on_rational_transforms"] = (
    "For the PSLQ sweeps the transformations 4*x, 1/4-x, 1/2-x, 1-3*x and 1-x "
    "are mathematically redundant with x -- a rational affine change is absorbed "
    "into the integer coefficient vector.  They were run anyway because they are "
    "NOT redundant for mpmath.identify, whose search over rationals/products is "
    "not affine-invariant.  The genuinely independent PSLQ normalisations are "
    "x, pi*x, pi^2*x, pi^3*x, x/pi, x/pi^2, x*sqrt2, x*sqrt3, x*pi/sqrt3, "
    "x*sqrt(pi), x/sqrt(pi), 1/x, x^2, sqrt(x), exp(x), log(x).")
json.dump(main, open(os.path.join(R, "identify_A_50digits.json"), "w"), indent=2)
print("supplement: raw hits", sup["n_pslq_raw_hits"], "survivors", sup["n_survivors"])
print("wrote results/identify_A_50digits.json")
