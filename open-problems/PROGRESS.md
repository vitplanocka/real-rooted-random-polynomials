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

---

## 2026-08-18 07:20 — session resumed after a crash: audit of what actually landed

The previous session ended abruptly; its last log entry was 00:45 but files on
disk are timestamped to 01:04. Before continuing I audited what had actually
been produced, rather than assuming the log was complete. Two substantial
results had landed unlogged.

### Problem A — the value is now good to 54 digits, not 12

`results/gaussian_cubic_quad.json` contains **four** mutually independent
quadrature routes (two coefficient-space "C", two root-space "R", each with a
main and a variant mesh), plus `results/gaussian_cubic_quad_ts.json` giving a
fifth, mpmath-native tanh-sinh route ("T") that shares no numerical code with
the others. Agreement:

```
spread over all four            4.95e-56      -> 54 digits common to all four
C(main) vs C(variant mesh)      5.21e-81
T (deg_in=8) vs C(150)          2.61e-54      -> 52 agreeing digits
```

    P_A = 0.16992938262347950265644315713176190213405726145463153…

Consistent with the prior Monte Carlo `0.169962 ± 4.2e-5` at **−0.78σ**, and
with my own root-space/gap computation from 00:35 (`0.169929382623`, ~12 digits,
which is that method's float64 ceiling). **This improves the known value from 5
significant digits to ~54.** That is the headline result for Problem A so far,
independently of whether a closed form exists.

### Problem B — the structure is validated and the `e`-window never clips

`results/quartic_structure.json`:
* the characterization "`f'` has 3 distinct real roots `x1<x2<x3` **and**
  `f(x1)<0, f(x2)>0, f(x3)<0`" agrees with a numerical root-finder in
  **0 mismatches / 200 000**, and with the `Δ>0 ∧ P<0 ∧ D<0` sign conditions in
  0/200 000;
* over **4 000 000** samples the admissible-`e` interval *never* left `[-1,1]`:
  `min e_lo = −0.2783`, `max e_hi = +0.3819`, `clip_any_frac_of_band = 0`.

So the `e`-window never clips, and with a **large** margin — unlike Theorem 1,
where the band touched the cube corner exactly. If that survives scrutiny
(a random-sample scan is suggestive, not proof — an agent is checking the true
extrema now), then exactly

    16 P_B = ∫∫∫_{[-1,1]³} L(b,c,d) db dc dd,    L = g(x2) − max(g(x1), g(x3)),

with **no clipping correction in `e` at all**. The `d`-band, by contrast, *is*
clipped by `d ∈ [-1,1]`.

### One thing that did NOT land: a wrong quadrature, caught

`results/quartic_quad_direct.json` records `I16 = 0.05020`, i.e.
`P_B = 0.003138` — but three independent Monte Carlos agree on `≈ 0.00547`. My
own vectorized MC (N = 2×10⁶) gives `I16 = 0.08730971`, `P_B = 0.00545686`. So
the nested-`scipy.quad` route is **~43 % low** and is simply wrong; it is not a
tolerance issue. Recorded here rather than quietly dropped, per this campaign's
standard. Diagnosing it is assigned to a subagent.

---

## 2026-08-18 07:25 — subagents relaunched (three, disjoint file prefixes)

* **Agent A2** — constant recognition for `P_A` at 50 digits over a broad basis
  (orthant-probability `arcsin`/`arctan`-over-π constants, Catalan, Γ(1/4),
  Γ(1/3), ζ(3), erf(1), … ), on `P_A` and on normalisations `πP_A`, `P_A/π`,
  `1/4 − P_A`, …, with 2-, 3- and 4-term PSLQ. **Required to calibrate the
  pipeline on a known constant first** — the previous campaign's
  `383/4860 + log3/48` — so that a negative result is trustworthy.
  Owns `identify_A_*`, `gaussian_cubic_identify_*`.
* **Agent B2** — diagnose the wrong quadrature above and produce a defensible
  high-precision `P_B` by two structurally different methods; plus find the
  *true* extrema of the `e`-band rather than sampled ones. Owns `quartic_*`.
* **Agent B3** — independent novelty/prior-art check for both constants (OEIS
  digit queries, Edelman–Kostlan / Kac / Dembo–Poonen–Shao–Zeitouni literature,
  Li 1988). Owns `results/novelty_check.{json,md}`.

I own `PROGRESS.md`/`VERDICT.md`; no agent may write them. Prefixes are disjoint
so the three cannot collide.

---

## 2026-08-18 07:35 — Problem B: an exact normal form, and the problem halves

Main-thread work while the agents run. Three claims, all verified — the first
two symbolically by sympy (exact zero residual), the third numerically.

### 1. Every monic quartic is a perfect square plus a *linear* function

With `p = b/2`, `q = c/2 − b²/8`:

    x⁴ + bx³ + cx² + dx + e  =  (x² + px + q)²  +  δ·x  +  ε

where **`δ = d − d*`, `d* = bc/2 − b³/8`**, and `ε = e − q²`. Verified by sympy:
the difference simplifies to exactly `0`. The change of variables
`(b,c,d,e) ↦ (p,q,δ,ε)` is lower-triangular with diagonal `(½,½,1,1)`, so its
Jacobian is exactly `1/4` (also sympy-confirmed):
`db dc dd de = 4 dp dq dδ dε`.

`δ` measures how far the quartic is from being *biquadratic in disguise*: `δ = 0`
iff `f = (x²+px+q)² + ε`.

### 2. `d* = bc/2 − b³/8` is exactly the locus of equal minima

Because `δ = 0` makes `f` a perfect square plus a constant, its two local minima
coincide. Checked numerically: `max |g(x1) − g(x3)|` at `d = d*` is **5.6e-16**
over 1 123 478 points. Moreover `sign(g(x1) − g(x3)) = −sign(δ)` exactly
(0 counterexamples in 292 121 tests), so on `δ > 0` the maximum is `g(x3)` and on
`δ < 0` it is `g(x1)`. **The `max` in `L` is not an obstruction: it is a single
clean split on the sign of an explicit cubic-in-`(b,c)` expression.**

This is the same hard-coded "kink" `d* = bc/2 − b³/8` that the previous session
had put into `quartic_quad_direct.py` by hand; it now has a reason.

### 3. The problem halves exactly

The involution `σ(b,c,d) = (−b, c, −d)` is measure-preserving on `[-1,1]³`,
preserves `L` exactly (`max |L − L∘σ| = 5.6e-16`), and flips the sign of `δ`
(since `d*(−b,c) = −d*(b,c)`). Hence the two halves contribute equally —
measured `8·E[L | δ>0] = 0.043629` vs `8·E[L | δ<0] = 0.043681`, equal within MC
noise — and

    16 P_B  =  2 ∫∫∫_{3 crit pts, δ > 0} ( g(x2) − g(x3) ) db dc dd.

So: the `max` is gone, the domain is halved, and the hand-placed kink surface is
now exact and analytic. Passed to Agent B2, with the explicit caveat that I have
*not* verified this half is easier to integrate — it is a suggestion, not a
result.

**Status of Problem B**: structure understood and simplified; the numeric is
currently only MC-grade (`P_B ≈ 0.005457`, ~4 digits). No closed form yet, and
none conjectured.

---

## 2026-08-18 07:40 — **Problem B: the band length has a closed form, and 99.2 % of the answer is now explicit**

This is the main result of the session. Everything below is verified numerically
to ~1e-16 *and* derived symbolically; both are reported.

### 1. Centring: the band length depends on only TWO of the three variables

Continue the normal form `f = (x²+px+q)² + δx + ε` of the previous entry, and
centre with `y = x + p/2`. Writing

    m = p²/4 − q = 3b²/16 − c/2,     δ = d − bc/2 + b³/8

the quartic becomes `f = (y² − m)² + δy + ε′` and its derivative
`f′ = 4y³ − 4my + δ` is **depressed**. Since the band length
`L = g(x₂) − max(g(x₁),g(x₃))` is a difference of `f`-values, `ε′` cancels:
**`L` depends only on `(m, δ)`.** Also `f′` has three real roots iff `m > 0`,
which is exactly the previously-known condition `c < 3b²/8`.

### 2. Scaling: it depends on only ONE variable

Rescaling `y = √m·z` gives `f = m²[(z²−1)² + τz] + ε′` with

    τ = δ / m^{3/2}.

Hence exactly

    L(b,c,d) = m² · Λ(τ),        Λ(τ) := band length of (z²−1)² + τz.

Verified: max relative error **3.3e-12** (median 4.4e-16) over 557 random
points with three real critical points. And

    3 real critical points  ⟺  m > 0 and |τ| < τ_c = 8/(3√3) = 1.5396007…

with **0 mismatches / 4000**.

### 3. `Λ` itself is closed-form — the exact analogue of the cubic's `(4/27)s³`

Let `z₁<z₂<z₃` be the roots of `4z³ − 4z + τ`. Put `S = z₂+z₃ = −z₁`. From
`Σz_i = 0`, `Σz_iz_j = −1`, `z₁z₂z₃ = −τ/4` one gets `z₂z₃ = S²−1`,
`(z₂−z₃)² = 4−3S²`, and `τ = 4S(S²−1)`. Then

    **Λ = S · (4 − 3S²)^{3/2}**,        S ∈ [1, 2/√3].

Same `3/2` power as the cubic's band width. Checks: `S=1 ⟹ τ=0, Λ=1` ✓;
`S=2/√3 ⟹ τ=τ_c, Λ=0` ✓ (band closes exactly at the endpoint); max deviation
from the numerically-computed `Λ` over 24 points: **7.8e-16**.

### 4. The universal constant is *rational*

    K := ∫_{−τ_c}^{τ_c} Λ(τ) dτ = **128/105**   (exactly).

Proof: `dτ = 4(3S²−1)dS`, then `u = 4−3S²` (so `S dS = −du/6`, `3S²−1 = 3−u`):

    K = 8∫₁^{2/√3} S(3S²−1)(4−3S²)^{3/2} dS = (4/3)∫₀¹ (3−u)u^{3/2} du
      = (4/3)(6/5 − 2/7) = 128/105.

sympy confirms symbolically; `scipy.quad` gives `1.21904761904762`
(`128/105 = 1.2190476190476190…`).

### 5. Consequence: 99.2 % of the answer in closed form

`(b,c,d) ↦ (b,m,τ)` has `db dc dd = 2 m^{3/2} db dm dτ`, so

    16 P_B = 2 ∫∫∫ m^{7/2} Λ(τ) db dm dτ

over `|b|≤1`, `0 < m ≤ M(b) := (3b²+8)/16`, `|τ| < τ_c`, **and** `|d| ≤ 1`.
(The constraint `|c| ≤ 1` is *exactly* `0 < m ≤ M(b)`; its other side is
automatic because `c ≤ 3b²/8 < 1`.)

**Drop the `|d| ≤ 1` constraint and the integral factorises completely:**

    16 P_B(unclipped) = (4K/9)·2^{−18} ∫_{−1}^{1} (3b²+8)^{9/2} db
                      = √3·asinh(√6/4)/90 + 7013√11/302400
                      = 0.088066959661…

(`asinh(√6/4) = log((√6+√22)/4)`.) Same shape as Theorem 1's
`3064/1215 + (8/3)asinh(1/√3)` — a rational multiple of a surd plus a
`√·asinh` term.

Against the true `16 P_B ≈ 0.0873758`, **the `|d| ≤ 1` clipping removes only
0.785 %.** So

    16 P_B = [ √3·asinh(√6/4)/90 + 7013√11/302400 ] − C_clip,   C_clip ≈ 6.9e-4.

**Problem B is now reduced to the single explicit correction `C_clip`**, the same
integral restricted to `|d| > 1`, with `d = τm^{3/2} + b³/16 − bm`. If `C_clip`
has a closed form, Problem B is solved. Handed to Agent B2, with the instruction
to verify the above independently rather than take it on trust.

### Why this is the Theorem-1 analogue TASK2.md asked for

`TASK2.md` asked whether there is "a 'never-clipped' type lemma analogous to
Lemma 1". The answer turns out to be **layered**:
* the `e`-window never clips at all (margin 0.28 vs 1) — better than Theorem 1,
  where the band touched the corner;
* the `c`-window is not a clipping constraint at all, it is exactly the domain
  `0 < m ≤ M(b)`;
* only the `d`-window clips, and it costs 0.785 %.

### 6. An independent root-space cross-check of P_B

`src/rootspaceB_check.py`, `results/rootspaceB_check.json`. In root space
`16 P_B = ∫_{r₁<r₂<r₃<r₄, |e_i|≤1} V(r) dr` (Vandermonde Jacobian; all roots
bounded by `√3` since `Σr_i² = e₁²−2e₂ ≤ 3`). This shares **no** code or algebra
with any critical-point route. Pooled over 3 seeds × 2×10⁷ samples:

    P_B = 0.00546099 ± 0.00000396

Consistent with the coefficient-space MCs (0.005457, 0.005462, 0.00548) and with
the earlier campaign's 0.0054749 ± 9.0e-6 — **four independent Monte Carlos now
agree at ≈ 0.005461**, and the nested-`scipy.quad` value 0.003138 is definitively
excluded.

---

## 2026-08-18 07:44 — Problem A: **no closed form, and the negative is calibrated** (Agent A2)

Agent A2's search is complete. The headline is a negative, but a *trustworthy*
one, because the pipeline was calibrated on constants whose closed form is known
before being pointed at `P_A`.

**Calibration passed at three levels**, each presented at exactly 50 digits like
`P_A` itself:

| | constant | recovered? |
|---|---|---|
| CAL1 | `383/4860 + log3/48` (the previous campaign's Theorem 1) | **yes**, margin 43.9 digits |
| CAL2 | `CAL1 + G/17` (2 named constants) | **yes**, margin 35.9 digits |
| CAL3 | `1/7 + log2/5 + G/3 + √3/11` (3 named constants) | **yes**, margin 41.8 digits |

Worth recording: the *first* choice of coefficient bound (`maxcoeff 1e5` at
k=2) **failed CAL2**, whose true relation needs `maxcoeff 330480`. The
calibration caught that and all bounds were widened before the real run. Without
the calibration the negative would have been an artefact of a too-small bound.

**What was searched**: 55 named constants (π, √π, π², π³, log 2/3/5, √2/√3/√5,
Catalan, ζ(3), γ, e, Γ(1/3), Γ(1/4), Γ(1/6), Γ(1/4)²/π^{3/2}, erf(1),
erf(1/√2), and the `arcsin/arctan/arccos`-over-π family that governs Gaussian
orthant probabilities, …) × **21 transformations** of the value
(`x, πx, x/π, π²x, x√3, x√2, x√π, 4x, 1/4−x, 1/2−x, 1−3x, 1/x, x², √x, exp x,
log x`, …) × `mpmath.identify` at 3 tolerances × PSLQ at k = 1, 2, 3 with
coefficient bounds `1e10 / 1e8 / 1e6` (plus an over-permissive `1e16` sweep).
**583 330 PSLQ subset calls.** Rationality tested to `maxcoeff 1e24`;
algebraicity tested for degrees 2,3,4,5,6,8.

**Result: zero relations, zero `identify` hits — nothing even reached the
over-determination test.** Two controls show the pipeline was genuinely
searching: on a structureless control PSLQ returns nothing until `maxcoeff 1e25`,
where it manufactures junk that "spends" 65.6 digits against 54 available
(margin −11.6); the same over-permissive probe on `P_A` yields only relations
spending 64.9–68.8 digits (margins −10.9 to −14.8). That is what junk looks like
here, and nothing credible appeared.

**Honest scope of the claim** (the agent's own caveat, which I endorse): this
rules out the *standard repertoire at credible coefficient sizes*. A closed form
could still involve a constant outside the 55-element pool — e.g. a period
specific to the discriminant surface — or need >3 basis elements, or larger
coefficients.

**Problem A outcome**: TASK2.md's "acceptable case", delivered well —
`P_A = 0.16992938262347950265644315713176190213405726145463153…` to ~54 digits
(prior best: 5 digits), with a documented and calibrated failure to find a closed
form. Files: `results/identify_A_50digits.json`,
`results/identify_A_calibration.json`.

---

## 2026-08-18 07:45 — novelty check (Agent B3), and **a correction to my own brief**

**I got something wrong and want it on the record.** In briefing the novelty
agent I asserted that `P(all n roots real) = 2^{−n(n−1)/4}` is a classical
Edelman–Kostlan result for the Kostlan ensemble. The agent checked at source —
it downloaded arXiv:math/9501224 and grepped it — and that is **not** in
Edelman–Kostlan at all. `2^{−n(n−1)/4}` is Edelman (*JMVA* 60, 1997) for all
eigenvalues of a real **Ginibre matrix** being real, a different problem. The
Kostlan *polynomial* ensemble at n=3 gives `(√3−1)/2 = 0.36603`, not
`2^{−3/2} = 0.35355`. Correction accepted and credited to the agent.

**Findings.**
* **OEIS: no hit for Problem A.** Eight distinct truncations of `P_A`
  (digit-sequence and constant forms) all returned "No results". Searching OEIS
  for the phrase `"random polynomial" "real roots"` returns exactly two
  sequences in the entire database — A060294 (`2/π`) and A093601 (Kac's
  expected-*count* constant). OEIS appears to contain no all-roots-real
  probability for any ensemble.
* **Web/StackExchange: no prior art for the monic Gaussian cubic.** The nearest
  neighbours are MSE 1745436 (which despite its title is the *scale-invariant*
  uniform limit `41/72 + ln2/12 = 0.6272`) and MSE 4185340 (no answers).
* **Problem B's search was vacuous at the time** — with only `0.005475`, OEIS
  parses the query as the 4-term sequence `5,4,7,5`. Now that `P_B` is known to
  16 digits the agent has been re-tasked to redo it.
* **The one live risk: Li (1988)** (Comm. Statist. Theory Methods 17(2):395–409)
  explicitly claims exact results **for the quartic**, has 0 recorded citations,
  is paywalled with no OA copy, and could not be read. Its review was recovered
  verbatim via the zbMATH API but does not list the special cases. **This is the
  single decisive document for both problems and remains unread** — so no
  novelty claim should be made for Problem B, and Problem A's should carry it as
  a caveat.

Could not search at all (so no negative is claimed from them): DuckDuckGo
(bot-blocked on every query, control included), MathSciNet, Google Scholar,
T&F full text, MR 89j full text, Bharucha-Reid–Sambandham (1986), arXiv full text.

---

## 2026-08-18 07:46 — Problem B: high-precision value, and the kink is a cubic irrational

**Two differently-arranged computations of the same reduction agree to 17
digits**, using the exact `τ`-integration (§4 of the 07:40 entry):

* *direct*: impose `|d| ≤ 1` as `τ`-limits, integrate `τ` exactly, then `(m,b)`
  → `16 P_B = 0.0874292854494397687`
* *unclipped − correction*: `[√3·asinh(√6/4)/90 + 7013√11/302400] − C_clip`
  with `C_clip = 0.00063767421118709` → `P_B = 0.00546433034058998567`

    **P_B = 0.005464330340589986**

Stable to 14+ digits under refinement of the outer `b`-grid (nb = 12→96 changes
nothing). *Refinement of an earlier figure*: the 07:40 entry quoted the clipping
as removing 0.785 %, computed against the Monte-Carlo `16 P_B ≈ 0.0873758`.
Against the now-computed `0.0874292854…` the correct figure is **0.724 %**. Consistent with all four Monte Carlos — against my root-space MC
`0.00546099 ± 0.00000396` it sits at **+0.84σ**.

*Caveat, stated deliberately*: the two arrangements share the `Λ = S(4−3S²)^{3/2}`
closed form and the `(b,m,τ)` reduction, so their 17-digit agreement is a strong
**internal** check, not two independent methods in this campaign's sense. The
only genuinely independent confirmation so far is Monte Carlo, at 4 digits
(0.84σ). Agent B2 is producing an independent high-precision value; until it
lands, treat digits beyond the 4th as *provisional*.

### The clipping onset is algebraic of degree 3

The `d`-band starts leaving `[-1,1]` exactly where `τ₁(b, M(b)) = τ_c`. Since

    τ₁(b, M(b)) = 8(b³+4b+8) / (3b²+8)^{3/2},   τ_c = 8/(3√3),

squaring gives `27(b³+4b+8)² = (3b²+8)³`, and sympy factors the difference as

    16·(27b³ − 9b² + 108b + 76) = 0.

So **b\* is a root of the irreducible cubic `27b³ − 9b² + 108b + 76`**, with the
single real root

    b* = −0.6143021014162960827521478…

This *exactly* reproduces the constant `0.6143021014162962` that the previous
session had hard-coded by hand into `quartic_quad_direct.py` — now derived rather
than fitted. It also says the answer, if closed-form, lives over a cubic field,
which is a useful constraint on any constant-recognition attempt for `C_clip`.

---

## 2026-08-18 07:52 — Problem B: 41 digits from the reduction, and a bounded closed-form search that fails

### The reduction converges to ~41 digits

Re-running the direct arrangement at increasing precision, with the exact kink
`b*` (root of `27b³−9b²+108b+76`) inserted into the outer `b`-grid:

```
dps=30 nb=24 : 16 P_B = 0.0874292854494397687231105
dps=40 nb=32 : 16 P_B = 0.08742928544943976872311045253260386      (~30 digits)
dps=50 nb=40 : 16 P_B = 0.087429285449439768723110452532603858341261775  (~41 digits)
```

    **P_B = 0.005464330340589985545194403283287741146329**   (~41 digits, provisional)

and hence

    C_clip = 0.000637674211187091936250935532440028016216419.

*Provisional* is meant literally: this is one reduction evaluated two ways. Its
only independent confirmation remains Monte Carlo at ~4 digits (+0.84σ). A
larger independent MC is running.

### No closed form for `C_clip` — bounded search, honest negative

With 41 digits a search is meaningful, so I ran PSLQ on `C_clip` (and on
`16 P_B` directly) over a **structure-informed** 25-constant basis rather than a
generic one — i.e. the constants the derivation actually produces:

`1, √2, √3, √6, √11, √22, √33, π, log2, log3, asinh(√6/4), √3·asinh(√6/4)`,
plus the cubic irrational `b*` and `b*²`, and the quantities the `b`-integral
over `[-1, b*]` must generate: `u₀ = √(3b*²+8)` and `u₀³, u₀⁵, u₀⁷, u₀⁹`,
`b*u₀³, b*u₀⁵, b*u₀⁷, b*u₀⁹`, `A₀ = asinh(b*√3/(2√2))`, `√3·A₀`.

k = 1, 2, 3 terms; `maxcoeff` 1e8 and 1e6; tolerance 1e-38; over-determination
filter "digits spent < 25" against 41 available.

**Nothing survived, on either target.** Scope of this negative is narrower than
Problem A's: the basis is a guess at the right field and only 3 terms were
allowed, so this is evidence against a *simple* closed form in the obvious
constants, not a demonstration that none exists. Given that `C_clip` is an
integral of algebraic functions over a region bounded by an irreducible cubic
surface, an elementary closed form should not be expected.

**Net position on Problem B**: 99.276 % of the answer is exact and explicit; the
remaining 0.724 % is a well-defined integral, evaluated numerically but not
recognised.

---

## 2026-08-18 07:56 — novelty check, follow-up round (Agent B3 resumed)

Re-tasked once `P_B` was known to 16+ digits, since the first round's Problem-B
digit search had been vacuous by construction.

* **Problem B's digit search is now decisive and empty.** Eight OEIS queries
  (`0.005464330340589986`, `5464330340589986`, the 16-term digit sequence,
  `0.0874292854494398`, `874292854494397687`, …) all returned literally
  "No results"; web search finds no occurrence of any of the digit strings. The
  earlier "vacuous" caveat is discharged, and Problem B's negative is now the
  same quality as Problem A's.
* **The new closed-form constants have no prior appearance.** OEIS returns
  nothing for `0.0880669596606269` (the unclipped value),
  `0.00063767421118709` (`C_clip`), `0.5794051802149734` (`asinh(√6/4)` itself),
  or either summand. arXiv metadata: `arcsinh` + `random polynomial` → 0;
  `sqrt{11}` + `real roots` → 0.
* **A methodological point the agent made and I endorse**: `K = 128/105 = 2⁷/105`
  is a Wallis-type rational, *not* a fingerprint — searching it as prior art is
  close to meaningless, and the one shape-coincidence found was explicitly
  recorded as carrying no inference.

### Li (1988): still unread, but much better characterised

Four genuine advances, all of which sharpen the caveat rather than remove it:

1. **zbMATH's "review" is Li's own abstract**, recovered word-for-word via
   OpenAlex. So it is not independent testimony and says nothing about the
   special cases. The independent MR review (G. Samal) remains inaccessible.
2. **Li's complete 9-item bibliography** was recovered via Crossref (new):
   Dickson's *Theory of Equations*, Uspensky's *Theory of Equations*, Kac 1949,
   Ibragimov 1971, Lapin, Mishra–Nayak–Pattanayak 1983, Neter, Stevens 1965,
   Yu 1982. **Zero** Gaussian-ensemble or measure-theoretic sources. That is
   *weak, inferential* support that his special cases are bounded/uniform-type
   — flagged as inference, and it says nothing about his quartic cases.
3. **Unpaywall confirms no legitimate free copy exists** (`oa_status: closed`,
   no repository copy).
4. **The single citing work is identified**: Jiří Anděl, *Mathematics of Chance*
   (Wiley 2001), most likely Ch. 11 "Probability in Mathematics", pp. 195–210 —
   a popular chapter is exactly where Li's special cases would be restated in the
   open. Scan exists on Internet Archive but is lending-restricted. **This is the
   most concrete bounded next step.**

Recorded as **not searched** (not "searched and empty"): Google Books full-text,
which indexes *Mathematical Reviews* and would likely settle it — it returned
HTTP 429 "Quota exceeded", so no negative may be inferred from it. Worth retrying
after the quota resets.

**Net**: Problem B's novelty assessment upgrades from low-to-moderate to
**moderate**. The correct phrasing for both problems remains *"not found in any
searchable source; Li (1988) unverified"* — not "novel".

---

## 2026-08-18 07:58 — Problem B: a 2×10⁸-sample independent check of the reduction

The 41-digit value rests on one reduction evaluated two ways, so it needed an
independent test sharper than the 4-digit Monte Carlos. Ran `8·E[L]` in raw
`(b,c,d)` with `L` computed from the critical points directly — **independent of
the `(m,τ)` reduction, of the `Λ = S(4−3S²)^{3/2}` closed form, and of the
quadrature** (it shares only the critical-point characterization, itself
validated 0 mismatches / 200 000 against a numerical root-finder):

```
N = 200,000,000
I16 = 0.087451895 ± 0.000022178
P_B = 0.0054657434 ± 0.0000013861
deterministic  P_B = 0.0054643303   ->  +1.02σ
```

**Agreement at 1.02σ, now at the 1.4e-6 level** — six significant digits rather
than four. Together with the root-space Vandermonde MC (+0.84σ) this is a
genuine, if low-precision, confirmation that the reduction and its domain are
right. It does *not* certify the 41 digits; it certifies roughly the first six,
and rules out a structural error in the reduction.

---

## 2026-08-18 08:20 — Agent B2 final report: the bug found, and `P_B` independently confirmed

### The 0.003138 mystery: a stale JSON, not a broken file

Good forensics, and the answer is not what I assumed. **`src/quartic_quad_direct.py`
on disk was already correct** — re-running it reproduces `I16 = 0.0874292854559`.
The file `results/quartic_quad_direct.json` was **stale**: written at 00:55 by a
revision that was then edited at 01:04, and never regenerated.

The agent reconstructed the offending revision by testing candidate mutations
until one reproduced `0.05020062770699262` *exactly*:

> `inner_d` was declared `def inner_d(b, c, tol)` but called as
> `quad(inner_d, -1.0, 3*b*b/8, args=(b, tol))`. `scipy.quad` binds the
> integration variable to the **first** parameter, so the `c`-sweep landed in the
> `b` slot and the outer `b` in the `c` slot — it integrated `d_band(c_var, b_outer)`.

The surviving comment `# c first: scipy.quad passes the integration var first` is
the fix, applied at 01:04 but never re-run. Explicitly ruled out (all give the
right answer): missing `d*` split, missing `b`-kink split, `c`-range `[-1,1]`,
absent `d`-clipping.

**Lesson for this campaign's discipline**: a result file is only as trustworthy
as its timestamp relative to its source. I had assumed a live bug and briefed the
agent accordingly; the agent tested that assumption instead of inheriting it.

Also: `src/quartic_quad.py` had **never run to completion** — no output existed.
Run now, it gives `16 P_B = 0.0874292854494398`, agreeing to 15 digits.

### `P_B` now has a genuinely independent high-precision confirmation

This was the gap I flagged at 07:52 (two arrangements sharing one reduction).
It is now closed:

| method | `16 P_B` | diff |
|---|---|---|
| reduction route, high precision (A/B, agree to 1e-190 at dps 200) | 0.0874292854494397687 | — |
| `quartic_quad.py`, independent `(b,u,s)` reduction | 0.08742928544943984 | 7e-17 |
| **raw `(b,c,d)` mpmath — only the definition of `L`, no reduction at all** | 0.0874292854494383849 | **−1.4e-15** |
| raw `(b,c,d)` float64 scipy | 0.087429285455853 | 6.4e-12 |
| MC, 5.6×10⁸ | 0.0874217921 ± 1.3e-5 | −0.57σ |

**~14 significant digits are now confirmed across structurally different
methods.** The agent's own summary of scope, which I adopt verbatim in
`VERDICT.md`: 15 digits defended; the remaining ~27 of the 41 are "internally
converged" rather than doubly confirmed.

The agent also independently re-derived the whole reduction
(`quartic_verify_reduction.py`: 0 mismatches in 2×10⁶ for the region test,
`∫Λ dτ = 128/105`, Jacobian `2m^{3/2}`) rather than taking my message on trust,
as asked.

### `b*`: same constant, opposite sign convention

The agent reports `b* = +0.6143021014162960827…` as the root of
`27b³ + 9b² + 108b − 76`; I derived `−0.6143021014162960827…` as the root of
`27b³ − 9b² + 108b + 76`. Verified: the two roots sum to exactly 0 — the same
constant under opposite sign conventions. No discrepancy.

### `C_clip`: a much stronger negative, with a structural reason

At **190 digits**: no algebraic relation of degree ≤ 10 with coefficients ≤ 1e14;
no `mpmath.identify` hit; nothing against a 17-constant pool *nor* against a
**purpose-built** basis `{b*^i·g}`, `g ∈ {1, √(3b*²+8), asinh(√6b*/4), √11,
√3·asinh(√6/4), …}` — i.e. the field the derivation actually generates. The only
PSLQ output was the trivial `R² = 3b*²+8`, with coefficient 0 on `C_clip`. As a
control the same code recovers `U`'s closed form immediately.

Structural reason for pessimism: the clipped region's boundary
`τm^{3/2} − bm + b³/16 = ±1` is an algebraic surface integrated against 3/2- and
5/2-power weights, so the `b`-integral runs over a **high-genus curve**.

### The `e`-window extrema are exact — with an honest caveat

* `max e_hi = **25/64**` exactly, at `(b,c,d) = (1,−1,−5/8)` and its mirror.
  Reason: `δ = 0` there, so `f = (x²+x/2−5/8)² + ε`, both minima of `g` equal
  `−q²` with `q = c/2−b²/8`, and `|q| ≤ 5/8` on the cube.
* `min e_lo = −(3y²−24y+1)/64 = −0.28400243430253032968…`, `y` the real root of
  `8y³+3y²+1 = 0`; attained at `(b,c,d) = (1, −0.63877164…, −1)`.
* Margins to the walls: **0.609375** and **0.71600**.

**Caveat the agent raised itself and I am keeping prominent**: `25/64` rests on a
KKT/envelope classification plus a global search, *not* on a one-line inequality
— `−q²` is **not** a universal lower bound for `max(g(x₁),g(x₃))` (samples violate
it by up to 9.3e-4; this is the negative `min_slack` field in
`results/quartic_ebounds_exact.json`). Corroborated by a 320³ grid + SLSQP and by
the 5.6×10⁸ MC extrema. So: true and well corroborated, a good candidate for
symbolic proof, but **not proved**.

---

## 2026-08-18 08:12 — final audit

All three subagents finished; nothing is still running. One planned computation
**did not complete** and is recorded as such rather than omitted: Agent B2's
heavyweight `e`-extrema corroboration (`src/quartic_ebounds3.py`, 600³ grid +
20 000 SLSQP starts) hit its timeout and never wrote
`results/quartic_ebounds3.json`. Nothing depends on it — three lighter
computations that *did* finish (320³ grid + SLSQP, the exact discriminant-sheet
reduction `g(x₂) = y³(y−4s)/3`, and a standalone sheet min/max scan) already
agree.

Cross-run consistency of the `e`-window extrema, which is the check that matters:

```
                              min e_lo              max e_hi
deterministic (exact)        -0.2840024343025303    0.390625 = 25/64
deterministic (grid+SLSQP)   -0.28400243430253075   0.39062499999998285
MC 5.6e8   (sampled)         -0.2835448131803671    0.3890694415144978
MC 4.0e6   (sampled)         -0.2783342407242212    0.3819271613699498
```

The two deterministic runs agree to 15 digits, and **both Monte-Carlo sampled
extrema lie strictly inside them** — which is the correct relationship (sampling
can only approach true extrema from within). No inconsistency anywhere.

### Deliverables, final

* `PROGRESS.md` (this file) and `VERDICT.md` — both problems, honest status.
* `results/` — 16 JSON records plus `novelty_check.md`.
* `~/math/real-rooted-random-polynomials/README.md` "Open targets" and
  `LITERATURE.md` §7 "Ranked next targets" updated (the only two files touched
  outside this directory, as `TASK2.md` permits), including correcting §7's stale
  recommendation to apply the cone trick to the monic quartic.
* No Lean formalization started: correct per `TASK2.md`, since neither headline
  resolved to a proved closed form. Problem B's exact sub-results (`Λ`,
  `K = 128/105`, `U`) are proved and are flagged in `VERDICT.md` as the natural
  pickup point.

---

## 2026-08-18 08:22 — addendum: bug forensics complete, and `U` confirmed from raw coordinates

### The bug diagnosis is now sharp, not merely plausible

Agent B2 finished a differential diagnosis: **15** candidate revisions of
`quartic_quad_direct.py` were tested, and **exactly one** reproduces the bogus
`0.05020062770699262`:

```
H1  inner_d arg-order swap (b<->c)          0.05020062770699   <-- exact match
H2  L_of called with args=(c,b)             0.04081762559456
H3  c-upper 3b/8 typo                       0.08656601637233
H5  d over [-1,1], no band, no splits       0.08742917026277
    no d* split / no b-kink split / b split at 0 only   0.087429285…
    c-upper = 1 (any combination)                       0.087429285…
    L = g2-g3 or g2-g1 (no max)             0.24662033307189
    no d-clipping to [-1,1]                 0.08806695965886
```

Every other structural error I or the agent could think of lands either within
`3e-10` of the correct answer or somewhere else entirely. So the
parameter-order swap is the *unique* explanation for that specific wrong number —
this is a confirmed diagnosis rather than a plausible story.

### An accidental — and valuable — independent confirmation of `U`

The "no d-clipping" row above is exactly the **unclipped** integral, computed in
raw `(b,c,d)` coordinates from nothing but `crit_points` and `g`. It therefore
shares **no algebra whatsoever** with the `(m,τ,Λ)` derivation of `U`.

I reproduced it myself (`scratch`, `tol=1e-11`, `d` over the full band
`[d_lo,d_hi]` with the `d*` split, `c ∈ [-1, 3b²/8]`):

```
raw (b,c,d), no d-clipping : 0.08806695966069
closed form U              : 0.08806695966063
difference                 : 6.2e-14
```

(Agent B2's run of the same idea gave `1.8e-12`.)

So the closed form

    U = √3·asinh(√6/4)/90 + 7013√11/302400 = 0.088066959660626860659…

now rests on **four** legs: my symbolic derivation, Agent B2's independent sympy
re-derivation, a 200-dps quadrature of the reduction agreeing to 192 digits, and
this raw-coordinate quadrature agreeing to `6e-14` that shares no algebra with
any of them. By this campaign's evidence standard, `U` is established.

---

## 2026-08-18 08:45 — the redundant `e`-extrema run: partial result, recorded

Following up the 08:12 note. I first intended to kill this run as redundant, then
looked at its log and found it was actively producing corroboration at
`nice -n 15`, so I let it continue. It has a `timeout 3000` cap and will expire
on its own; I am not blocking on it further.

**First objective completed** (`min e_lo`, via `max g(x₂)`), 4000 SLSQP starts:

```
min e_lo = -0.284002434414466
    at (b,c,d) = (-1.0000000001, -0.6387716428937, +1.0000000003)
    double root y = 0.6610498…, simple root -0.5720996…
```

Two things this adds:
* it agrees with the exact value `-0.28400243430253032968…` to **~10 digits**
  (the residual is SLSQP's convergence tolerance, not a discrepancy);
* it lands on the **mirror** point `(-1, -0.63877, +1)` of the one Agent B2
  reported, `(1, -0.63877, -1)` — consistent with the `(b,c,d) ↦ (-b,c,-d)`
  involution established at 07:35, and a small extra check that the symmetry is
  real.

**Second objective (`max e_hi`) did not complete** before I stopped waiting. It
is not needed: `max e_hi = 25/64` is already fixed exactly by the discriminant-sheet
reduction, by the 320³ grid + SLSQP run, and by my own direct evaluation at
`(1,-1,-5/8)` (which gives `25/64` to machine precision, with `x₂ = -1/4` exactly).

Recorded as a partial result rather than dropped, since the campaign standard is
that unfinished computations are visible in the log.

---

## 2026-08-18 08:52 — correction to the 08:45 entry: the run *did* finish

The 08:45 entry says the second objective "did not complete". **That is now
false** — it completed shortly after I stopped waiting, and
`results/quartic_ebounds_global.json` is written. Correcting rather than editing
the earlier entry, since this is a log.

Both objectives independently reproduced:

| quantity | 4000-start SLSQP | 500³ grid | exact |
|---|---|---|---|
| `max g(x₂)`      | 0.28400243441  | 0.28378607711  | **0.28400243430253033** |
| `min max(g₁,g₃)` | −0.39062500038 | −0.38960972518 | **−25/64 = −0.390625** |

The residual ~4e-10 is SLSQP's convergence tolerance against the active
constraint (its returned points violate `|b| ≤ 1` by ~1e-10), not a disagreement:
the exact values come from solving the active-constraint system algebraically,
not from the optimizer.

**A structural echo worth recording**: the `max e_hi` optimum sits at
`(b,c,d) = (1,−1,−5/8)` with roots `((−1±√11)/4, −1/4)` — matching the `δ = 0`
analysis exactly, and the `√11` there is the same `√11` that appears in the
closed form `U = √3·asinh(√6/4)/90 + 7013√11/302400`. The `min e_lo` optimum is
the mirror point `(−1,−0.63877164,+1)` with double root `y = 0.66105` on the
discriminant sheet, exactly as the `(b,c,d) ↦ (−b,c,−d)` involution requires.

### One word I am not adopting

The agent's summary says the `e`-window "**provably** never clips". I am keeping
the weaker phrasing in `VERDICT.md`. What exists is an envelope/KKT argument that
the extrema cannot be interior, nor in the relative interior of a face or edge,
plus exact algebraic solution of the resulting active-constraint systems, plus
four agreeing numerical determinations. That is a proof *in outline* and I expect
it to be correct — but it has not been written out rigorously, and the agent
itself earlier found that the tempting shortcut (`−q²` as a universal lower bound
for `max(g(x₁),g(x₃))`) is **false**, violated by up to 9.3e-4. So: established
to a high standard of evidence, not yet proved.

---

## 2026-08-18 09:55 — **PROBLEM A IS RESOLVED**: an externally-contributed closed form, independently re-verified here

`problem_A_verified_result.md` arrived with a candidate closed form from an
external agent, already checked by the operator's session, and with an explicit
instruction not to trust that write-up but to re-verify. I re-verified everything
from first principles. **It is correct.**

    P_A = (1/π) ∫₀^∞ exp( −x⁴(x⁴+4x²+9) / (2(x⁴+4x²+1)) )
                     · 2(x⁴+6x²+3) / ( √(x⁴+4x²+1) · (x⁴+4x²+9) ) dx

A single one-dimensional integral of elementary functions — no discriminant
indicator, no multivariate integration, no `Φ`/`erf` in the final form.

### What I checked, from scratch (`src/probA_kacrice_*.py`)

I re-derived the setup rather than reading it off: with `q = x⁴+x²+1` and
`u(x) = (x²,x,1)/√q`, one has `f(x) = x³ + √q·Z(x)` with `Z = (a,b,c)·u`, so
roots of `f` are crossings of the moving level `−h`, `h = x³/√q`.

| check | method | result |
|---|---|---|
| `‖u‖ = 1` | sympy | residual **exactly 0** |
| **`Cov(Z,Z′) = u·u′ = 0`** (so `Z ⟂ Z′`) | sympy | **exactly 0** |
| `v² = ‖u′‖² = (x⁴+4x²+1)/q²` | sympy | residual **exactly 0** |
| `h′ = x²(x⁴+2x²+3)/q^{3/2}` | sympy | residual **exactly 0** |
| eq (7): `h²+z² = x⁴(x⁴+4x²+9)/(x⁴+4x²+1)`, `z = h′/v` | sympy | residual **exactly 0** |
| eq (8): `v+θ′ = 2(x⁴+6x²+3)/[√(x⁴+4x²+1)(x⁴+4x²+9)]` | see below | **EXACT** |
| eq (9) vs our own `Δ₃` | sympy | residual **exactly 0** |

**I strengthened eq (8) beyond the write-up.** The operator's session could only
check it numerically (finite differences, ~31 digits) because sympy will not
collapse the nested radicals. Instead of differencing, I differentiated
symbolically and then cleared both radicals: the identity holds iff
`(x⁴+4x²+1)·(x⁸+7x⁶+10x⁴+9x²+3)² = (x⁴+6x²+3)²·(x¹²+6x¹⁰+12x⁸+16x⁶+12x⁴+6x²+1)`,
and sympy expands that difference to **exactly 0**; both pre-squared sides have
all-positive coefficients, hence are positive for `x>0`, so the square root is the
right branch. **eq (8) is exact, not merely numerical.**

Also: their eq (9) is *literally* the discriminant identity this campaign proved
in Lean — `−27Δ₃ = (27c−9ab+2a³)² − 4(a²−3b)³` — residual 0 on expansion.

### The decisive test: 79 agreeing digits

| comparison | difference | agreeing digits |
|---|---|---|
| Kac–Rice integral vs our **method C** (coefficient-space quadrature) | 5.21e-81 | **79** |
| Kac–Rice integral vs our **method R** (root-space quadrature) | 4.95e-56 | 54 |

79 digits is *method C's own internal precision limit* (C-main vs C-variant also
agreed to 79). So the new integral agrees with our best previous computation to
the full extent that computation can be trusted — from a completely different
derivation (level-crossing vs. direct quadrature of the discriminant region).
Self-convergence of the new integral: `4.4e-83 → 4.5e-113 → 2.8e-142` as working
precision rises.

**New best value, 100 digits** (`results/probA_kacrice.json`):

    0.1699293826234795026564431571317619021340572614546315315327419707570687910330741791889359856870862579

### The structural bridge, checked separately

The step from Kac–Rice to a probability is `E[N] = 1·P(1 root) + 3·P(3 roots)`,
i.e. **`p = (E[N]−1)/2`**, valid because a real cubic has 1 or 3 real roots. This
is algebra, not analysis, but I checked it does not hide an error: a 2×10⁷-sample
MC gives `E[N] = 1.339575`, `(E[N]−1)/2 = 0.16978770`, and the direct root-count
frequency `0.16978770` — identical, and 1.7σ from the exact `0.16992938`.

### What is **not** established

* **The "no elementary antiderivative" (Risch) side-claim remains UNVERIFIED** —
  the write-up says so, and I did not close it either. I can sharpen *why* it is
  hard: the integrand is `e^{g}·f` with `g` rational but `f` **algebraic**
  (it contains `√(x⁴+4x²+1)`), so the textbook Liouville criterion for
  `∫ f e^{g}` with `f,g` rational — elementary iff a rational `T` exists with
  `f = T′ + g′T` — **does not apply**; deciding this needs Risch over the
  algebraic function field `ℚ(x, √(x⁴+4x²+1))`. sympy's `integrate` times out and
  `risch_integrate` is not exposed in this version; neither outcome is evidence.
  **Re-flagged unverified, not refuted.**
* **Two different questions must not be conflated**, and I want this on the
  record: "the *indefinite* integral has no elementary antiderivative" (Risch)
  and "the *definite* integral is not a finite combination of named constants"
  (PSLQ) are independent claims. Our 583 330-call calibrated PSLQ search answered
  the **second** in the negative. The Risch claim is about the first. Neither
  implies the other, and the closed form above is unaffected by either.

---

## 2026-08-18 (later session) — independent verification of the external `C_clip` candidate

An external agent's submission for `C_clip` (`problem_B_candidate_result.md`) was
checked from scratch, nothing reused. Full record:
`problem_B_verification_2026-08-18.md`. Result: substantially correct, three
transcription errors, no impact on the master decomposition.

* **Factor-of-2 claim: arithmetically right, but not a defect here.** The
  Jacobian `|∂(b,c,d)/∂(b,m,τ)| = 2m^{3/2}` was re-derived symbolically
  (residual 0), as were `d = τm^{3/2}+b³/16−bm` and `m ≤ M(b) ⟺ c ≥ −1`.
  Prop B5 already carries the 2 (`4K/9 = 2·K·(2/9)`); `U`, `C_clip` and
  `16p_B = U − C_clip` are self-consistent to 53 decimals. The omission was in
  an ad-hoc `c_clip_problem_statement.md` written for the agent, which is not in
  this repo and is referenced nowhere in the campaign record. Nothing propagates.
  - Independent raw `(b,c,d)` Monte Carlo (band from critical points only, no
    reduction), N = 3×10⁸: `0.000638526 ± 8.79e-7`; `z = +0.97` vs `C_clip`,
    `z = +364` vs half of it.
  - Independent nested quadrature of the literal (prefactor-free) integral, using
    an exact antiderivative `G(τ) = U^{5/2}(4/5 − 4U/21)`, `U = 4−3S(τ)²`, derived
    here: agrees with the agent's `C_w` to 3.9e-12 relative.
* **1-D reduction: confirmed**, after correcting (i) the `A₁` `artanh` coefficient
  to `35√3/12288` (as written, `35√3/4096`, it is 3× too large; the corrected
  value is the unique solution and gives residual exactly 0) and (ii) the Möbius
  map to `t_S(z) = B(z−α)/(A(z−β))` (as written it is inverted, lands in `(1,∞)`
  and makes `E` complex). With both fixes, formula (1) reproduces all 75 quoted
  digits at dps 120; the beta sum matches direct quadrature to 45–58 digits.
  The `(ABD)^{17/3}` exponent is right (all three exponents equal `−17/3`), as are
  the beta parameters `(j−7/3, −7/3)` and the whole §2 geometry
  (`z₀ = 1/√11`, `τ₀ = 24/(11√11)`, `S₀`, the `S_c` endpoint `z₋ = x*/√(3x*²+8)`).
* **Non-elementarity: confirmed.** `γ(ρ)` re-derived independently (unique
  solution of the 9×9 system, differential residual 1e-33); Sturm gives it **no
  real roots at all**. The stated minimum `54 − (11/108)√22` is wrong — the true
  min of `11u³−33u²−21u+97` on `u ≥ 2` is `54 − (108/11)√22 ≈ 7.949` (fraction
  inverted); positivity survives. Genus 1 confirmed three ways (Riemann–Hurwitz,
  smooth plane cubic, Weierstrass `V²=U³+16`, `j=0`); `div(dt/y) = P₀+P₁−2P_∞`.
  The Rosenlicht chain is sound with two compressed standard steps. **But
  Chebyshev's 1853 binomial-differential criterion settles the residual in one
  line** (`p=−1/3`, `(m+1)/n=2/3`, sum `1/3`); the genuinely new content is the
  Hermite reduction, whose trinomial integrand is outside Chebyshev's reach.
* **`(S,θ)` reparametrisation: confirmed.** `τ = τ_c cos 3θ` with
  `S = (2/√3)cos θ`, `θ ∈ [0,π/6]`, exact; `Λ|dτ| = (128/3)cos θ sin⁴θ(4cos²θ−1)dθ`
  exact **with the absolute value** (the signed form is its negative); integrates
  to `64/105`.
* **By-product:** `Λ = S(4−3S²)^{3/2}` re-confirmed against the *definitional*
  band length to 25 digits, and `∫Λdτ = 128/105` exactly.

### Lean (Problem A side)

`NonmonicCubic/OneRealRoot.lean` added to the sibling repo: the negative half of
the root-count bridge, `Δ₄ < 0 ↔ exactly one real root` (for `a ≠ 0`, `Δ₄ ≠ 0`),
plus the dichotomy `N ∈ {1,3}` off `{Δ₄ = 0}` that `p = (E[N]−1)/2` needs. Engine
is the identity `Δ₄ = f′(r)²·((b+ar)² − 4a(c+br+ar²))` at any root `r`. Zero
`sorry`, zero warnings, standard axioms.
