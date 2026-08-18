"""Full 50-digit constant-recognition campaign for P_A.  -> results/identify_A_50digits.json"""
import json, os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from identify_A_run import campaign, algebraic_check, K_SPECS, DEMO_SPEC, IDENTIFY_BASES, IDENTIFY_MAXCOEFF
from identify_A_search import P_A_50, P_A_54, MARGIN_REQUIRED
from mpmath import mp

t0 = time.time()
print("=== P_A campaign ===", flush=True)
out = campaign(P_A_50, P_A_54, "P_A = P(x^3+ax^2+bx+c has 3 distinct real roots), (a,b,c) iid N(0,1)",
               K_SPECS, nproc=10, demo=True)
print("=== algebraic-degree check ===", flush=True)
out["algebraic_check"] = algebraic_check(P_A_50, P_A_54)
out["overdetermination_test"] = (
    "A relation among n reals with integer coefficients of size <= M appears by "
    "chance once n*log10(M) >~ D, where D = digits available.  We define "
    "spent = sum_i log10(max(|n_i|,1)) and margin = 54 - spent, and require "
    f"margin >= {MARGIN_REQUIRED} digits AND |residual|/max|coeff| < 1e-48 when "
    "re-evaluated against the full 54 agreed digits.")
out["demo_sweep_note"] = (
    "One deliberately over-permissive sweep (transform 'x', 1 named constant, "
    "maxcoeff 1e16) is included to exhibit what junk looks like: such relations "
    "spend up to 3*16 = 48 of the 54 available digits and are meaningless.")
out["elapsed_seconds"] = round(time.time() - t0, 1)
calpath = os.path.join(os.path.dirname(__file__), "..", "results", "identify_A_calibration.json")
out["calibration_file"] = "results/identify_A_calibration.json"
try:
    cal = json.load(open(calpath))
    out["calibration_summary"] = {
        k: {kk: cal[k][kk] for kk in ("label", "expected", "value_searched",
                                      "n_pslq_raw_hits", "n_passing_margin_test",
                                      "n_verified_at_54", "n_survivors",
                                      "recovered_by_identify", "recovered_by_pslq",
                                      "PASSED") if kk in cal[k]}
        for k in cal if k.startswith("calibration_")}
    out["calibration_all_passed"] = cal.get("all_passed")
except Exception as e:  # merged in afterwards by identify_A_merge.py
    out["calibration_summary"] = f"pending ({e})"
path = os.path.join(os.path.dirname(__file__), "..", "results", "identify_A_50digits.json")
json.dump(out, open(path, "w"), indent=2)
print("wrote", path)
print("elapsed", out["elapsed_seconds"])
