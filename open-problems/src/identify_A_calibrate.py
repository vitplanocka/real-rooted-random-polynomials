"""Calibration: feed the pipeline constants whose closed form IS known.

If the pipeline cannot recover a known answer, a negative result on P_A is
worthless.  Three calibrators of increasing difficulty:
  CAL1  383/4860 + log(3)/48                      (1 named constant)
  CAL2  CAL1 + catalan/17                          (2 named constants)
  CAL3  1/7 + log(2)/5 + catalan/3 + sqrt(3)/11    (3 named constants)
Each is presented to the search at exactly 50 digits, as P_A is.
"""
import json, os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from identify_A_run import campaign, K_SPECS
from mpmath import mp, mpf

mp.dps = 90
CALS = [
    ("CAL1 = 383/4860 + log(3)/48", mpf(383) / 4860 + mp.log(3) / 48,
     "expected relation on [t,1,log3]: [19440, -1532, -405]"),
    ("CAL2 = 383/4860 + log(3)/48 + catalan/17",
     mpf(383) / 4860 + mp.log(3) / 48 + mp.catalan / 17,
     "expected relation on [t,1,catalan,log3]: [330480, -26044, -19440, -6885]"),
    ("CAL3 = 1/7 + log(2)/5 + catalan/3 + sqrt(3)/11",
     mpf(1) / 7 + mp.log(2) / 5 + mp.catalan / 3 + mp.sqrt(3) / 11,
     "expected relation on [t,1,catalan,log2,sqrt3]: [1155, -165, -385, -231, -105]"),
]

res = {}
for i, (label, val, expect) in enumerate(CALS, 1):
    v50 = mp.nstr(val, 50, strip_zeros=False)
    v54 = mp.nstr(val, 54, strip_zeros=False)
    print(f"=== calibration {i}: {label}", flush=True)
    print(f"    50-digit input: {v50}", flush=True)
    r = campaign(v50, v54, label, K_SPECS, nproc=12, transform_names=["x"])
    r["expected"] = expect
    r["recovered_by_identify"] = bool(r["identify_hits"])
    r["recovered_by_pslq"] = bool(r["survivors"])
    r["PASSED"] = bool(r["identify_hits"] or r["survivors"])
    res[f"calibration_{i}"] = r
    print(f"    identify hits: {sorted(set(h['result'] for h in r['identify_hits']))[:3]}", flush=True)
    for h in r["survivors"]:
        print(f"    SURVIVOR {h['reduced_support']}  margin={h['margin_vs_54_digits']}", flush=True)
    print(f"    PASSED={r['PASSED']}", flush=True)

res["all_passed"] = all(res[k]["PASSED"] for k in res if k.startswith("calibration_"))
json.dump(res, open(os.path.join(os.path.dirname(__file__), "..", "results",
                                 "identify_A_calibration.json"), "w"), indent=2)
print("ALL PASSED:", res["all_passed"])
