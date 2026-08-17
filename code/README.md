# Code

All numerical/symbolic evidence behind `paper/`, in plain Python
(numpy/scipy/sympy/mpmath — `pip install -r requirements.txt`).

## Theorems 1 & 2 (monic cubic)

```
python src/exact_anchors.py    # exact anchor values + structural identities (S1-S3)
python src/mc_engine.py         # vectorized antithetic Monte Carlo, 6 cases
python src/reduce_monic.py      # breakpoint-aware high-precision 2D quadrature
python src/closed_form.py       # the rigorous end-to-end symbolic proof (sympy)
```

`closed_form.py` is the important one: every step of the Theorem 1/2 proofs in
`paper/` is checked there in exact arithmetic (12/12 steps PASS).

## Theorem 3 (non-monic cubic)

```
python src/scout_face.py            # first double-precision scout of the answer
python src/face_exact.py            # exact symbolic derivation (cone / divergence theorem)
python src/face_verify.py           # cone identity check, F(s) cross-checks, blind PSLQ
python src/route1_closed_a.py       # fully independent numerical route (no face decomposition)
python src/nonmonic_vt.py           # V(t) and p(a) by nested high-precision quadrature
python src/vt_table.py              # V(t) table, t = 1...50, two integration orders
python src/nonmonic_mc.py           # 4x10^10-sample Monte Carlo, two estimators
python src/weighted_cone_check.py   # fixed-a weighted-cone identity, checked against a raw grid
python src/sweep_postmortem.py      # attempted reconstruction of the refuted 0.217993225 value
python src/finalize.py              # assembles VERDICT.md from the above
```

`face_exact.py` gives the closed form symbolically (sympy). `route1_closed_a.py`
is the independent 19-significant-digit numerical confirmation that shares no
step with it — the two together are the load-bearing evidence for Theorem 3.

## Results

`results/*.json` are the raw outputs of every script above; `results/*.log`
are a few verbose run transcripts kept for the record. `results/literature_sweep_raw.json`
is the structured output of the 8-agent literature search backing the paper's
novelty claims (Section 5).

## Reproducing the headline numbers

```
python src/closed_form.py
# ...
# all steps verified; Theorem 1 = 383/4860 + log(3)/48
# Theorem 2 = 1/2880

python src/face_exact.py
python src/route1_closed_a.py
# both should print 641/2430 - log(3)/24 to full working precision
```
