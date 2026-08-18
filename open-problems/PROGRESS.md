# PROGRESS — two open problems in random-polynomial real-rootedness

Follow-on to the non-monic cubic campaign (`TASK2.md` Phase 2). Timestamps via
`date '+%F %T'` (local). Methodology and evidence standard deliberately matched
to `reference/VERDICT.md` of the previous campaign: **nothing is called exact
without at least two structurally independent confirmations**, and a quadrature
routine's own error estimate is never treated as evidence.

## The two targets

* **Problem A — monic cubic, Gaussian coefficients.**
  `P( x³ + ax² + bx + c has 3 real roots )`, `(a,b,c) ~ N(0,1)` i.i.d.
  Prior best: Monte Carlo `0.169962 ± 4.2e-5`.
* **Problem B — monic quartic, uniform coefficients.**
  `P( x⁴ + bx³ + cx² + dx + e has 4 real roots )`, `(b,c,d,e) ~ U[-1,1]` i.i.d.
  Prior best: Monte Carlo `≈ 0.0054749 ± 9.0e-6`.

Both are genuinely open: no closed form and no proof is known to this campaign.

---

## 2026-08-18 00:25 — setup

Created `~/math/open-problems/` with `src/`, `results/`, and a `.venv`
(numpy 2.5.2, scipy 1.18.0, sympy 1.14.0, mpmath 1.3.0). Everything below runs
under `nice -n 10`.

**Reference material actually present** in the previous project's `reference/`
folder: `THEOREMS.md`, `VERDICT.md`, `PROGRESS.md`, `LITERATURE.md`,
`exact_anchors.py`, `closed_form.py`, `face_exact.py`, `face_verify.py`,
`route1_closed_a.py`, `mc_engine.py`. **`paper.tex` is *not* present**, so the
"Open problems" claim `TASK2.md` corrects could not be re-read at source; I am
taking `TASK2.md`'s correction of it at face value and not attempting the cone
trick on the monic quartic (its reasoning — that fixing the leading coefficient
destroys the homogeneity the cone argument needs — is plainly right, and matches
what I proved in Mission 1: `Δ₄_smul` scales *all four* coefficients together).

### The Problem A reduction, restated from Mission 1's proved lemmas

The band identity is distribution-free, and Mission 1 proved it in Lean. With
`s = √(a² − 3b)` (real exactly when `b ≤ a²/3`),

    27·c_hi(a,b) = (a − s)²(a + 2s),    27·c_lo(a,b) = (a + s)²(a − 2s)

(`NonmonicCubic.cHi_eq`, `cLo_eq`), and `Δ₃ > 0 ⟺ c_lo < c < c_hi`
(`NonmonicCubic.Δ₃_pos_iff`), with `Δ₃ < 0` when `b > a²/3`
(`NonmonicCubic.Δ₃_neg_of_lt`). Since `c ⊥ (a,b)`,

    P = E_{(a,b)} [ 1{b < a²/3} · ( Φ(c_hi) − Φ(c_lo) ) ]
      = (1/2π) ∫∫_{b < a²/3} e^{-(a²+b²)/2} (Φ(c_hi) − Φ(c_lo)) da db.

Smooth integrand, no clipping case splits — the cube walls that drove Theorems
1–3's `L1`/`L2` machinery simply are not there.

---

## 2026-08-18 00:30 — subagents launched (both problems, concurrently)

Per `TASK2.md`'s instruction to parallelize genuinely independent work, and
because the two problems share nothing, I launched both at once rather than
serially:

* **Agent A1** — Problem A: 30+ digit quadrature of the `Φ`-difference integral
  by **two structurally different methods**, plus a from-scratch ≥10⁸-sample
  Monte Carlo. (Explicitly told: agreement between different methods is the
  evidence, a routine's own error estimate is not — the previous campaign's
  post-mortem lesson.)
* **Agent B1** — Problem B: re-validate the `Δ>0 ∧ P<0 ∧ D<0` characterization,
  derive the quartic critical-point picture, hunt for a never-clipped structure
  by dense scan, and produce a defensible numeric with an MC cross-check.

Both were told to stay inside this directory and given disjoint filename
prefixes (`gaussian_cubic_*` vs `quartic_*`) so they cannot collide.

Why subagents here and not in Mission 1: in Mission 1 nearly every step depended
on the exact statement of the previous lemma, so parallelism would have created
merge conflicts for no gain. These two problems genuinely share no state.

## 2026-08-18 00:35 — Problem A: a third, independent route (done in main thread)

While the agents ran I worked out a representation that is *structurally*
independent of the `Φ`-difference integral, so it is a real cross-check and not
a re-run of the same reduction.

**Root-space form.** Writing `f(x) = (x−r₁)(x−r₂)(x−r₃)`, the coefficients are
`a = −e₁, b = e₂, c = −e₃`; the Jacobian of `(r₁,r₂,r₃) ↦ (e₁,e₂,e₃)` is the
Vandermonde `V = ∏_{i<j}(r_i−r_j)`; the map is 3!-to-1 onto the all-real region;
and the standard normal density is even. Hence

    P_A = (2π)^{-3/2} ∫_{r₁<r₂<r₃} V(r) · exp(−(e₁²+e₂²+e₃²)/2) dr.

This is a Vandermonde-weighted integral with a Gaussian in the *elementary
symmetric functions* rather than in the roots — an unusual weight, not a
β-ensemble.

**Numerically it needs one idea.** Imposing `r₁<r₂<r₃` with a mask leaves kinks
on the simplex faces and only algebraic convergence (0.169498 → 0.169893 from
n=120 to n=500, still climbing). Parametrising the simplex by its **gaps**
instead — `r₁ = u`, `r₂ = u+p`, `r₃ = u+p+q` with `p,q > 0`, unit Jacobian —
makes the Vandermonde the smooth positive polynomial `V = p q (p+q)` on a
*product* domain, and Gauss–Legendre then converges geometrically.

Result (`src/root_space_check.py`, `results/root_space_check.json`), at n=220
nodes per axis and three different truncations:

```
L=8,  M=7 : 0.16992938262283805
L=9,  M=8 : 0.16992938262346985
L=10, M=9 : 0.16992938262314095
```

**P_A ≈ 0.169929382623**, agreeing to ~12 digits across truncations — which is
the float64 ceiling, not a convergence limit. Consistent with the prior MC
`0.169962 ± 4.2e-5` at **−0.78σ**.

This already improves the known value by ~7 orders of magnitude in precision,
and it is an independent handle on whatever Agent A1 returns.

## 2026-08-18 00:40 — constant recognition: tooling built, first pass is inconclusive *by design*

`src/identify_constant.py` runs `mpmath.identify` over eight explicit bases plus
a 2-term PSLQ sweep against a 30-constant pool (π, 1/π, π², log 2/3/5, √2/√3/√5,
Catalan, Γ(1/4), Γ(1/3), Euler γ, erf(1), √π, and the arctan/arcsin/arccos-over-π
values that show up in Gaussian orthant probabilities). It records **the basis
actually tried**, so a negative is documented rather than shrugged off.

Run against the 12-digit root-space value, purely to exercise the tooling:

* `mpmath.identify` returned eight "hits", **all junk** — e.g.
  `(−215/2) + (141/4)π − 92 log2 + (221/4) log3`. With 12 digits and tolerance
  `1e-8`, PSLQ can hit anything if you let the coefficients grow; that is the
  documented failure mode, not a discovery.
* **2-term PSLQ found nothing** with coefficients below `1e6` against any
  constant in the pool. That *is* meaningful at this precision: it rules out
  `P_A = (p/q)·C` for every `C` in the pool.

Conclusion: constant recognition is not meaningful until Agent A1's 30+ digits
land. Deliberately not drawing any inference from the `identify` output.

## 2026-08-18 00:45 — a corollary of Mission 1 worth recording for Problem B

`TASK2.md` corrects `paper.tex`'s claim that the cone trick applies to the monic
quartic. I can confirm the correction independently and sharpen it, since I
proved the cone identity in Lean last phase.

The quartic discriminant of `a x⁴+b x³+c x²+d x+e` is homogeneous of degree 6 in
**all five** coefficients, so `{Δ>0} ⊆ ℝ⁵` *is* a cone — but the monic problem is
the slice `a = 1`, and a slice of a cone is not a cone. `TASK2.md` is right.

Running Mission 1's argument on the *non-monic* quartic gives, with `n = 5`:

    vol₅(R ∩ [-1,1]⁵) = (1/5) Σ_{10 faces} S_face

(so `2×5 = 10` faces, confirming `TASK2.md`'s correction of the paper's "2×4=8").
Central symmetry applies because `Δ` is homogeneous of *even* degree 6, so
`Δ(−x) = Δ(x)`; and coefficient reversal `(a,b,c,d,e) ↦ (e,d,c,b,a)` gives
`S_a = S_e`, `S_b = S_d`. Hence

    vol₅ = (2/5)(2 S_a + 2 S_b + S_c),      with   S_a = 16 · P_B.

So the non-monic quartic would need **Problem B as an input**, plus two further
3-dimensional face volumes (`S_b`, `S_c`) — it cannot produce `P_B`. Recorded
here because `reference/LITERATURE.md` §7 item 2 still recommends the cone trick
for the monic quartic; that recommendation needs correcting (deliverable 4).
