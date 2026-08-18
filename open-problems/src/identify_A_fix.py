"""Recompute the (de-duplicated) survivor lists in the result JSONs.

The first run of the campaign collected `survivors` before de-duplication, so a
single genuine relation appeared once per k-subset that contained its constant.
Every hit dict already carries `survives` and `duplicate_of_smaller_relation`,
so the corrected list is just a re-filter of the de-duplicated `pslq_hits`.
"""
import json, os, sys

R = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "results")


def fix(d):
    if not isinstance(d, dict) or "pslq_hits" not in d:
        return d
    surv = [h for h in d["pslq_hits"] if h.get("survives")]
    d["survivors"] = surv
    d["n_survivors"] = len(surv)
    d["n_passing_margin_test"] = sum(1 for h in d["pslq_hits"] if h.get("passes_margin_test"))
    d["n_verified_at_54"] = sum(1 for h in d["pslq_hits"] if h.get("verified_at_54_digits"))
    d["n_pslq_raw_hits"] = len(d["pslq_hits"])
    d["recovered_by_pslq"] = bool(surv)
    if "identify_hits" in d:
        d["recovered_by_identify"] = bool(d["identify_hits"])
        d["PASSED"] = bool(d["identify_hits"] or surv)
    return d


for fn in sys.argv[1:]:
    p = os.path.join(R, fn)
    d = json.load(open(p))
    fix(d)
    for k in list(d):
        if isinstance(d[k], dict):
            fix(d[k])
    if all(k.startswith("calibration_") or k == "all_passed" for k in d):
        d["all_passed"] = all(d[k].get("PASSED") for k in d if k.startswith("calibration_"))
    json.dump(d, open(p, "w"), indent=2)
    print("fixed", p)
