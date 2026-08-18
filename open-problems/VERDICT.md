# Real-rootedness probabilities for random monic cubics and quartics

**Working paper draft — campaign of 2026-08-18.**
Follow-on to the non-monic cubic campaign. Full chronological log: `PROGRESS.md`.
The evidence document that preceded this draft is preserved verbatim at
`results/VERDICT_prepaper_backup.md`.

Evidence standard, applied throughout and stated so the reader can audit it:
**nothing is called exact without at least two structurally independent
confirmations**, and a quadrature routine's own error estimate is never treated
as evidence. Claims are graded explicitly as *proved*, *verified symbolically*,
*numerically established*, or *unverified*.

---

## Abstract

We study two real-rootedness probabilities that were open at the start of this
campaign.

**(A)** For `(a,b,c)` i.i.d. `N(0,1)`, we give a closed form for
`p_A = P(x³+ax²+bx+c has three real roots)` as a **single one-dimensional
integral of elementary functions**, and evaluate it to 100 digits. The formula
was contributed by an external agent and is independently re-verified here: every
algebraic step is checked symbolically (residual exactly 0), and the integral
agrees with this campaign's earlier, wholly unrelated quadrature to **79
significant digits**. Separately, a calibrated search shows `p_A` is *not* a
small-coefficient combination of 55 standard constants — so the closed form is a
definite integral, not a named-constant expression.

**(B)** For `(b,c,d,e)` i.i.d. `U[-1,1]`, we do not solve
`p_B = P(x⁴+bx³+cx²+dx+e has four real roots)`, but we reduce it substantially.
We show every monic quartic is a perfect square plus a linear function, that the
admissible-`e` band length factorises as `m²Λ(τ)` with `Λ(τ) = S(4−3S²)^{3/2}`
exactly, that `∫Λ dτ = 128/105` exactly, and hence that **99.28 % of the answer is
the closed form `√3·asinh(√6/4)/90 + 7013√11/302400`**. The residue is a single
explicit integral, evaluated to ~41 digits (~14 independently confirmed) and
resistant to a 190-digit closed-form search.

We also correct two claims in the surrounding literature/notes of this project.

---

## 1. Introduction

Let `N` denote the number of real roots. Two classical-looking questions were
open to this project:

* **Problem A** — `p_A = P(x³+ax²+bx+c has 3 real roots)`, `(a,b,c)` i.i.d. `N(0,1)`.
  Prior best: Monte Carlo `0.169962 ± 4.2e-5`.
* **Problem B** — `p_B = P(x⁴+bx³+cx²+dx+e has 4 real roots)`, `(b,c,d,e)` i.i.d. `U[-1,1]`.
  Prior best: Monte Carlo `0.0054749 ± 9.0e-6`.

Both are **monic**: the leading coefficient is fixed at 1 and only the lower
coefficients are random. This matters — the monic ensemble is distinct from the
Kac, Kostlan/Shub–Smale and Weyl ensembles for which the classical literature
gives results, and conflating them is a live source of error (§5.2).

The predecessor campaign solved the *non-monic* cubic on `[-1,1]⁴`,
`P = 641/2430 − ln3/24`, and formalized it in Lean 4 / Mathlib with zero `sorry`,
including the classical `sign Δ ↔ three distinct real roots` bridge that Mathlib
lacked. That development supplies several ingredients used below.

---

## 2. Problem A: a closed form

### 2.1 Result

> **Theorem A.** For `(a,b,c)` i.i.d. standard normal,
>
>     p_A = (1/π) ∫₀^∞ exp( −x⁴(x⁴+4x²+9) / (2(x⁴+4x²+1)) )
>                      · 2(x⁴+6x²+3) / ( √(x⁴+4x²+1) · (x⁴+4x²+9) )  dx

Numerically, to 100 digits:

    p_A = 0.1699293826234795026564431571317619021340572614546315
          315327419707570687910330741791889359856870862579

This is a closed form in the same sense that Owen's *T*-function or `erf` are
closed forms: a single definite integral of elementary functions, with no
discriminant indicator, no multivariate integration, and no normal CDF in the
final expression.

**Attribution.** The formula was **contributed by an external agent**, not derived
in this campaign. It was checked by the operator's session and handed here with
an explicit instruction to re-verify rather than trust the write-up. §2.3 is that
independent re-verification. The derivation route is Kac–Rice level-crossing plus
an exact cancellation using Owen's *T*-function; the external derivation's own
final display had formatting corruption, so everything below is assembled from
re-derived pieces, not transcribed.

### 2.2 Why the shape is what it is

Write `q(x) = x⁴+x²+1` and `u(x) = (x², x, 1)/√q`, a unit vector. Then

    f(x) = x³ + a x² + b x + c = x³ + √q(x) · Z(x),   Z(x) = (a,b,c)·u(x),

so `Z(x) ~ N(0,1)` pointwise and the real roots of `f` are exactly the crossings
of the *moving level* `−h(x)`, `h = x³/√q`. Two facts make Rice's formula
tractable here, both verified symbolically in §2.3:

* `‖u‖ ≡ 1`, hence `Cov(Z, Z′) = u·u′ = ½(‖u‖²)′ = 0`: **`Z` and `Z′` are
  independent**, so the conditional expectation in Rice's formula factorises.
* A real cubic has 1 or 3 real roots, so `E[N] = 1·P(N=1) + 3·P(N=3)`, i.e.

      p_A = (E[N] − 1)/2.

A naive Rice computation leaves a normal-CDF term (from `E|Z′+h′|`); the external
derivation removes it exactly via Owen's *T*, producing the CDF-free integrand
above.

### 2.3 Independent verification

All checks re-derived from first principles in `src/probA_kacrice_verify.py`,
`probA_kacrice_exact8.py`, `probA_kacrice_crosscheck.py`.

| # | claim | method | result |
|---|---|---|---|
| 1 | `‖u‖ = 1` | sympy | residual **exactly 0** |
| 2 | `Cov(Z,Z′) = u·u′ = 0` | sympy | **exactly 0** |
| 3 | `v² := ‖u′‖² = (x⁴+4x²+1)/q²` | sympy | residual **exactly 0** |
| 4 | `h′ = x²(x⁴+2x²+3)/q^{3/2}` | sympy | residual **exactly 0** |
| 5 | `h² + z² = x⁴(x⁴+4x²+9)/(x⁴+4x²+1)`, `z = h′/v` | sympy | residual **exactly 0** |
| 6 | `v + θ′ = 2(x⁴+6x²+3)/[√(x⁴+4x²+1)(x⁴+4x²+9)]`, `θ = arctan(z/h)` | see below | **exact** |
| 7 | their discriminant identity `≡` our Lean-proved `Δ₃` | sympy | residual **exactly 0** |

**Item 6 was strengthened here.** The operator's session could only check it
numerically (finite differences, ~31 digits) because sympy will not collapse the
nested radicals. Differentiating symbolically and then clearing both radicals,
the identity is equivalent to the polynomial statement

    (x⁴+4x²+1)·(x⁸+7x⁶+10x⁴+9x²+3)² = (x⁴+6x²+3)²·(x¹²+6x¹⁰+12x⁸+16x⁶+12x⁴+6x²+1),

whose difference sympy expands to **exactly 0**; both pre-squared sides have
all-positive coefficients, so are positive for `x>0` and the branch is correct.
**Item 6 is therefore exact, not merely numerical.**

**The decisive test.** The new integral is compared against this campaign's
earlier, entirely unrelated computation (direct high-precision quadrature of the
discriminant region, in two coordinate systems):

| comparison | difference | agreeing digits |
|---|---|---|
| Theorem A vs **method C** (coefficient-space quadrature) | 5.21e-81 | **79** |
| Theorem A vs **method R** (root-space quadrature) | 4.95e-56 | 54 |

79 digits is *method C's own internal precision ceiling* (C-main vs C-variant
mesh also agreed to 79). So Theorem A agrees with the previous best computation
to the full extent that computation can be trusted, from a completely different
derivation. Self-convergence of Theorem A's integral under rising working
precision: `4.4e-83 → 4.5e-113 → 2.8e-142`.

**The bridge, checked separately.** `p_A = (E[N]−1)/2` is algebra, not analysis,
but a 2×10⁷-sample Monte Carlo confirms it hides no error: `E[N] = 1.339575`,
`(E[N]−1)/2 = 0.16978770`, direct root-count frequency `0.16978770` — identical,
and 1.7σ from the exact value.

### 2.4 What is *not* claimed

Two negatives must be stated alongside Theorem A, because one does not erase the
other.

**(i) `p_A` is not a small-coefficient combination of standard constants.**
A calibrated search found nothing: 55 named constants (π, √π, log 2/3/5, √2/√3/√5,
Catalan, ζ(3), γ, Γ(1/3), Γ(1/4), Γ(1/6), erf(1), and the `arcsin/arctan/arccos`-
over-π family from Gaussian orthant probabilities, …) × 21 transformations of the
value × `mpmath.identify` at three tolerances × PSLQ at 1, 2 and 3 terms with
coefficient bounds `1e10/1e8/1e6` — **583 330 PSLQ subset calls**. Rationality
tested to `maxcoeff 1e24`; algebraicity for degrees 2,3,4,5,6,8. **Zero hits.**

The negative is trustworthy because the pipeline was **calibrated first** on
constants with known closed forms, each at exactly 50 digits: `383/4860+log3/48`
(recovered, margin 43.9 digits), `+ G/17` (35.9), `1/7+log2/5+G/3+√3/11` (41.8).
The first coefficient bound tried *failed* the second calibration (true relation
needs `maxcoeff 330480`); bounds were widened before the real run. A control shows
PSLQ only manufactures junk at `maxcoeff 1e25`, spending 65.6 digits against 54
available (margin −11.6); on `p_A` the same probe gives margins −10.9 to −14.8.

Scope: this excludes the *standard repertoire at credible coefficient sizes*. A
closed form could still need a constant outside the pool, more than three terms,
or larger coefficients.

**(ii) The "no elementary antiderivative" claim is UNVERIFIED.** The external
write-up closes with a Risch-algorithm argument; the operator's session did not
re-derive it, and neither did this one. We can sharpen *why* it is harder than it
looks: the integrand is `e^{g}·f` with `g` **rational** but `f` **algebraic** (it
contains `√(x⁴+4x²+1)`), so the textbook Liouville criterion for `∫ f e^{g}` with
`f,g` rational — elementary iff a rational `T` exists with `f = T′ + g′T` — **does
not apply**. Deciding it requires Risch over the algebraic function field
`ℚ(x, √(x⁴+4x²+1))`. sympy's `integrate` times out; that is not evidence.
**Re-flagged unverified, not refuted.**

**These are different questions.** "The *indefinite* integral has no elementary
antiderivative" (Risch) and "the *definite* integral is not a finite combination
of named constants" (PSLQ) are independent claims; (i) answers the second, the
external argument concerns the first, and Theorem A is unaffected by either.

---

## 3. Problem B: structure, and 99.28 % of the answer

Not solved. What follows is a reduction that removes almost all of the difficulty
and isolates the rest into one explicit integral.

Throughout, `f(x) = x⁴+bx³+cx²+dx+e`, `g = f − e`, and `x₁<x₂<x₃` are the
critical points of `f` when `f′ = 4x³+3bx²+2cx+d` has three real roots. Then `f`
has four distinct real roots iff `f′` does and `f(x₁)<0<f(x₂)`, `f(x₃)<0`
(validated: **0 mismatches in 200 000** against a numerical root-finder, and 0
against the `Δ>0 ∧ P<0 ∧ D<0` sign conditions). The admissible `e` form an
interval of length `L = g(x₂) − max(g(x₁),g(x₃))`.

### 3.1 Normal form (proved)

> **Proposition B1.** With `p = b/2`, `q = c/2 − b²/8`, `d* = bc/2 − b³/8`,
> `δ = d − d*`, `ε = e − q²`:
>
>     x⁴+bx³+cx²+dx+e = (x²+px+q)² + δ·x + ε.
>
> The map `(b,c,d,e) ↦ (p,q,δ,ε)` is lower-triangular with Jacobian exactly `1/4`.

sympy: residual exactly 0. So `δ` measures failure to be biquadratic-in-disguise:
`δ = 0` iff `f` is a perfect square plus a constant.

### 3.2 The band length factorises (proved)

Centring `y = x + p/2` gives `f = (y²−m)² + δy + ε′` with `m = 3b²/16 − c/2`, and
`f′ = 4y³−4my+δ` is *depressed*. Since `L` is a difference of `f`-values, `ε′`
cancels: `L` depends only on `(m,δ)`. Rescaling `y = √m·z` gives

> **Proposition B2.** `L(b,c,d) = m²·Λ(τ)` with `τ = δ/m^{3/2}`, where `Λ(τ)` is
> the band length of `(z²−1)² + τz`. Moreover `f′` has three real roots iff
> `m > 0` and `|τ| < τ_c = 8/(3√3)`.

Verified: `L` to median 4.4e-16; the region test **0 mismatches / 4000**.

### 3.3 `Λ` in closed form, and a rational constant (proved)

Let `z₁<z₂<z₃` solve `4z³−4z+τ=0` and put `S = z₂+z₃ = −z₁`. From the elementary
symmetric relations, `z₂z₃ = S²−1`, `(z₂−z₃)² = 4−3S²`, `τ = 4S(S²−1)`, whence

> **Proposition B3.** `Λ = S·(4 − 3S²)^{3/2}`, `S ∈ [1, 2/√3]`.

— the exact analogue of the cubic band width `(4/27)s³`, with the same `3/2`
power. Checks: `S=1 ⟹ τ=0, Λ=1`; `S=2/√3 ⟹ τ=τ_c, Λ=0`; max deviation from
numerics **7.8e-16**.

> **Proposition B4.** `K := ∫_{−τ_c}^{τ_c} Λ(τ) dτ = **128/105**` exactly.

*Proof.* `dτ = 4(3S²−1)dS`, then `u = 4−3S²` (so `S dS = −du/6`, `3S²−1 = 3−u`):
`K = 8∫₁^{2/√3} S(3S²−1)(4−3S²)^{3/2}dS = (4/3)∫₀¹(3−u)u^{3/2}du = (4/3)(6/5−2/7)`. ∎
sympy confirms; `scipy.quad` gives `1.21904761904762`.

### 3.4 The unclipped integral is closed-form (proved)

`db dc dd = 2m^{3/2} db dm dτ`, and `|c| ≤ 1` is *exactly* `0 < m ≤ M(b) := (3b²+8)/16`
(its other side is automatic since `c ≤ 3b²/8 < 1`). Dropping only `|d| ≤ 1`:

> **Proposition B5.**
>
>     U := (4K/9)·2^{−18} ∫_{−1}^{1}(3b²+8)^{9/2} db
>        = √3·asinh(√6/4)/90 + 7013√11/302400
>        = 0.088066959660626860659361388065043886357478194205026…
>
> and `16 p_B = U − C_clip`, where `C_clip` is the same integral over `|d| > 1`.

(`asinh(√6/4) = log((√6+√22)/4)`.) Same shape as the predecessor campaign's
`3064/1215 + (8/3)asinh(1/√3)`.

**`U` rests on four independent legs**: symbolic derivation; an independent sympy
re-derivation; a 200-dps quadrature of the reduction agreeing to **192 digits**;
and — sharing *no algebra at all* with the `(m,τ,Λ)` derivation — a raw `(b,c,d)`
quadrature over the unclipped `d`-band using only critical points, agreeing to
**6.2e-14**. By this paper's standard, `U` is established.

**`C_clip / U = 0.724 %`.** So Proposition B5 supplies 99.276 % of `p_B` exactly.

### 3.5 The `e`-window never clips

Unlike the predecessor campaign's Theorem 1, where the band touched the cube
corner exactly, here it is nowhere near the wall:

    max e_hi = **25/64** exactly, at (b,c,d) = (1,−1,−5/8)
    min e_lo = −(3y²−24y+1)/64,  8y³+3y²+1 = 0,  y ≈ −0.66105
             = −0.28400243430253032968…

Margins to `∓1`: **0.609** and **0.716**. The `max e_hi` point has `δ = 0`, so
`f = (x²+x/2−5/8)² + ε` and both minima of `g` equal `−q²` with `|q| ≤ 5/8`; its
roots are `((−1±√11)/4, −1/4)` — the same `√11` that appears in `U`.

*Status: established to a high standard of evidence, not proved.* Four
independent determinations agree (320³ grid + SLSQP; 500³ grid; 4000-start SLSQP;
5.6×10⁸ MC extrema), the last two landing on mirror-image optima as the
`(b,c,d) ↦ (−b,c,−d)` involution requires. There is a proof in outline
(envelope/KKT classification — `∇_{b,c,d} g(x_i) = (x_i³,x_i²,x_i)` vanishes only
at `x_i = 0`, so extrema lie on the active-constraint set — plus exact solution of
the resulting systems). It has not been written out, and the tempting shortcut is
**false**: `−q²` is not a universal lower bound for `max(g(x₁),g(x₃))`, being
violated by up to 9.3e-4.

### 3.6 The residual, and the numerical value

    C_clip = 0.000637674211187091936250935532440028016216419…
    p_B    = 0.0054643303405899855451944032832877411463288609119348…

The clipping onset is algebraic of degree 3: the `d`-band first leaves `[-1,1]`
where `8(b³+4b+8)/(3b²+8)^{3/2} = 8/(3√3)`, i.e. at the real root of the
irreducible cubic `27b³ − 9b² + 108b + 76`, `b* = −0.6143021014162960827521478…`
This *derives* a constant an earlier attempt had fitted by hand.

**Evidence for `p_B`.** ~41 digits are available; **~14 significant digits are
defended** by structurally independent routes:

| method | `16 p_B` | difference |
|---|---|---|
| reduction route, two arrangements (agree to 1e-190 at dps 200) | 0.0874292854494397687 | — |
| independent `(b,u,s)` reduction | 0.08742928544943984 | 7e-17 |
| **raw `(b,c,d)` mpmath — only the definition of `L`, no reduction** | 0.0874292854494383849 | −1.4e-15 |
| Monte Carlo, 5.6×10⁸ | 0.0874217921 ± 1.3e-5 | −0.57σ |
| Monte Carlo, 2×10⁸ | — | +1.02σ |
| root-space Vandermonde MC (shares no algebra with any critical-point route) | — | +0.84σ |

Digits beyond ~14 rest on the reduction plus the sympy-verified `U`, and are
"internally converged" rather than doubly confirmed.

**No closed form for `C_clip`.** At **190 digits**: no algebraic relation of degree
≤ 10 with coefficients ≤ 1e14; no `mpmath.identify` hit; nothing against a
17-constant pool nor against a purpose-built basis `{b*^i·g}` with
`g ∈ {1, √(3b*²+8), asinh(√6·b*/4), √11, √3·asinh(√6/4), …}` — the field the
derivation actually generates. The only PSLQ output was the trivial
`R² = 3b*²+8`. As a control the same code recovers `U` immediately. Structural
reason for pessimism: the clipped region's boundary `τm^{3/2} − bm + b³/16 = ±1`
is an algebraic surface integrated against 3/2- and 5/2-power weights, so the
`b`-integral runs over a curve of positive genus. (Refined below: the genus is
in fact **1**, not high — see §3.7.)

### 3.7 `C_clip` reduced to one dimension, and a non-elementarity result

An **external agent** (not this campaign) submitted a reduction of `C_clip` on
2026-08-18. It was verified here from scratch, to the same evidence standard as
Problem A; the full record is `problem_B_verification_2026-08-18.md`, and the
three transcription corrections plus the Chebyshev note are collected, in
copy-pasteable form, in **`problem_B_candidate_corrections.md`**. Summary of what
survived:

**A one-dimensional formula.** Substituting `z = x/(4√m)` (`x = −b`), which turns
the clipping condition into `m^{3/2}(τ + 4z(1−z²)) > 1`, and integrating `m` and
then `τ` exactly, gives

    C_clip = (16/5) ∫_{S₀}^{2/√3} W(S)·[ A₁(z₀) − A₁(z_L) + A₂(z_R) − A₂(z₀)
                                          − E(S; z_L, z_R) ] dS

with `W(S) = 4S(3S²−1)(4−3S²)^{3/2} = Λ·dτ/dS`, `z₀ = 1/√11`, `S₀` the root of
`4S(S²−1) = 24/(11√11)`, `A₁,A₂` elementary, and `E` a finite sum of nine
incomplete-beta differences of parameters `(j−7/3, −7/3)` coming from a Möbius
substitution on `4(S³−S+z−z³) = 4(S−z)(z−α)(z−β)`. **One integration variable.**
Verified: reproduces `C_clip` to **all 75 quoted digits** at dps 120, and the
beta sum matches direct quadrature to 45–58 digits pointwise.

**The inner integral is provably non-elementary.** Hermite reduction sends
`(1−ρt)⁸t^{−10/3}(1−t)^{−10/3}dt` to an exact differential plus
`γ(ρ)·t^{−1/3}(1−t)^{−1/3}dt` with

    γ(ρ) = −(10/7)(ρ²−ρ+1)(11ρ⁶−33ρ⁵+12ρ⁴+31ρ³+12ρ²−33ρ+11),

which by Sturm has **no real root at all** (`γ < 0` throughout). The residual
`∫t^{−1/3}(1−t)^{−1/3}dt` is non-elementary — by **Chebyshev's 1853 criterion**
for binomial differentials in one line (`p = −1/3`, `(m+1)/n = 2/3`, sum `1/3`,
none an integer). The submission's own genus-1/Rosenlicht proof of this is also
sound (curve `y³ = t(1−t)`, genus 1 confirmed three ways, `j = 0`,
`div(dt/y) = P₀+P₁−2P_∞`), but is over-engineered for the conclusion; the
genuinely new content is the Hermite step, since the trinomial
`(1−ρt)⁸t^{−10/3}(1−t)^{−10/3}` is outside Chebyshev's reach.

**This is not a closed form for `C_clip`.** It is non-elementarity of the inner
`z`-integral at fixed `S`, not of the final constant. The PSLQ negative above
stands — and is now *explained*: the intrinsic object is an incomplete elliptic
period at moving algebraic endpoints, so an elementary-logarithmic basis was
structurally too narrow.

**A factor-of-2 report, resolved.** The submission also reported that `C_clip` is
twice the triple integral "as displayed". That arithmetic is correct — the
displayed integrand was `m^{7/2}Λ` rather than `2m^{7/2}Λ` — but the omission was
in an ad-hoc problem statement written for the external agent, a file that does
not exist in this repository. The factor 2 is the Jacobian
`|∂(b,c,d)/∂(b,m,τ)| = 2m^{3/2}`, re-derived from scratch here, and Proposition
B5 already carries it inside `4K/9 = 2·K·(2/9)`. **No number in this document
changes.** Independent confirmation: a raw `(b,c,d)` Monte Carlo using only the
definition of the band, `N = 3×10⁸`, gives `0.000638526 ± 8.8e-7`, i.e. `z=+0.97`
against `C_clip` and `z=+364` against half of it.

---

## 4. Two corrections

### 4.1 The cone/divergence trick does not apply to the monic quartic

Project notes recommended applying the divergence-theorem/cone argument that
solved the non-monic cubic. It does not work. The quartic discriminant is
homogeneous of degree 6 in **all five** coefficients, so `{Δ>0} ⊆ ℝ⁵` *is* a cone
— but the monic problem is the slice `a = 1`, and a slice of a cone is not a cone.

Applied correctly to the *non-monic* quartic, the (Lean-verified) cone identity
gives `vol₅ = (1/5)·Σ over **10** faces` — correcting a "2×4 = 8 faces" claim —
and by central symmetry (degree 6 is even) plus coefficient reversal,
`vol₅ = (2/5)(2S_a + 2S_b + S_c)` with **`S_a = 16 p_B`**. That route therefore
*consumes* Problem B as an input and cannot produce it.

### 4.2 `2^{−n(n−1)/4}` is not a polynomial result

It is Edelman (*JMVA* 60, 1997) for all eigenvalues of a real **Ginibre matrix**
being real — not Edelman–Kostlan, and not the Kostlan polynomial ensemble (which
at `n=3` gives `(√3−1)/2 = 0.36603`, not `2^{−3/2} = 0.35355`). This was
established by downloading arXiv:math/9501224 and grepping it: it contains no
all-roots-real result. The error originated in this campaign's own briefing
material and is corrected here.

---

## 5. Novelty status

### 5.1 What was searched, and found empty

* **OEIS**: eight truncations of `p_A` and eight of `p_B` (including
  `0.005464330340589986` and `0.0874292854494398`) — all "No results". OEIS
  appears to contain no all-roots-real probability for *any* ensemble: searching
  `"random polynomial" "real roots"` returns exactly two sequences in the entire
  database, both about expected *counts*.
* **The new constants**: `0.0880669596606269` (`U`), `0.00063767421118709`
  (`C_clip`), `0.5794051802149734` (`asinh(√6/4)`) — nothing. arXiv metadata for
  `arcsinh`+`random polynomial` and `sqrt{11}`+`real roots`: 0.
* **Web / StackExchange**: no occurrence of any digit string. The nearest
  neighbours are a *scale-invariant uniform* limit (`41/72+ln2/12`) and an
  unanswered question.

Note `K = 128/105 = 2⁷/105` is a Wallis-type rational, not a fingerprint;
searching it as prior art would be meaningless and was treated as such.

### 5.2 The outstanding risk

**Li (1988)**, *Comm. Statist. Theory Methods* 17(2):395–409, explicitly claims
exact results for the **quartic**, and remains unread. Established about it:
what zbMATH carries as its "review" is **Li's own abstract** (recovered via
OpenAlex), so it is not independent testimony; Unpaywall confirms no free copy;
its 9-item bibliography is classical theory-of-equations plus elementary
statistics with **zero** Gaussian-ensemble sources (weak inferential support that
its cases are uniform-type); and its single citing work is Jiří Anděl,
*Mathematics of Chance* (Wiley 2001), likely Ch. 11 — a popular chapter, exactly
where the special cases would be restated in the open, but the scan is
lending-restricted.

**Novelty is therefore not asserted.** The correct phrasing for both problems is
*"not found in any searchable source; Li (1988) unverified"*.

**Not searched** (so no negative is inferred): Google Books full text (HTTP 429
quota), DuckDuckGo (bot-blocked), MathSciNet, Google Scholar, T&F full text,
MR 89j full text, Bharucha-Reid–Sambandham (1986), arXiv full text.

### 5.3 Theorem A: the formula and the technique searched separately

A third search round targeted the *formula* and the *technique* rather than the
decimal. Its conclusion sharpens — and narrows — what may be claimed.

**The formula: no prior appearance found.** Zero hits for the digit string in
OEIS, on the web, and in **IA Scholar full text**; zero for the derived constants
`1+2P`, `2P`, `1−P`; zero in IA Scholar for every polynomial-context phrasing of
"probability that all roots are real". No source gives `P(all roots real)` for the
monic Gaussian cubic at any degree.

**The technique: claim narrowly.** Neither ingredient is new. The non-central
Rice density with its `erf` remainder is Edelman–Kostlan Cor. 5.1 (1995), and
**E–K explicitly invite the reader to carry out the monic computation**; Owen's
*T* inside Rice/level-crossing work is established practice. What was *not* found
anywhere is Owen's *T* used as the device that **cancels** the `erf` term, nor any
Kac–Rice computation of a real-rootedness **probability** (as opposed to an
expected count), nor any exact evaluation of the monic-Gaussian Kac–Rice integral.

> **Recommended phrasing, adopted here.** Claim the closed form and the Owen's-T
> cancellation. Do **not** claim "applying Kac–Rice to the monic Gaussian cubic"
> (E–K signposted it in 1995), nor "using Owen's T in a Rice-formula context".

**Nearby results explicitly ruled out.** Akiyama–Pethő (*J. Math. Soc. Japan*
66(3), 2014) *do* compute exactly the probability that a **monic** polynomial is
totally real — but in the **contractive** ensemble (roots in the unit disc), via
Selberg integrals, not Kac–Rice: a different ensemble. Do–Nguyen–O'Rourke
(arXiv:2605.26402, 2026), "Real roots of non-centered random polynomials", is
closest in spirit but was downloaded and grepped: no "monic", no "Owen",
variance/CLT asymptotics only.

**Residual risks, stated plainly.** (i) No engine does literal math-string /
integrand-shape matching, so the most direct search *never ran*; (ii) because E–K
invite the computation, a textbook exercise or unindexed note doing it would be
invisible to every channel available; (iii) Li (1988) unread; (iv)
Bharucha-Reid–Sambandham and Farahmand unsearchable. **Not searched**: literal
math-string matching (no engine does it), arXiv full text (`search.arxiv.org`
dead), Google Books (HTTP 429 all day), Google Scholar, MathSciNet, T&F full
text, MR 89j body, HathiTrust, CORE, Mojeek, DuckDuckGo. Bing returns 200 but
silently drops phrase queries — a control failed, so **no Bing negative is
claimed**. One methodological gain: `scholar.archive.org` full-text search was
made to work, so this round's negatives are full-text, not metadata-only.

---

## 6. Open problems and next steps

1. **Prove `C_clip` has no elementary closed form**, or find one. §3.7 now
   supplies a 1-D reduction and proves the *inner* integral non-elementary; what
   remains is the outer `S`-integral of an incomplete elliptic period against
   `W(S)` over algebraic endpoints `z_L(S), z_R(S)` — the latter on the plane
   cubic `S³−S = 17z³−z`. A Rosenlicht argument at that level, or a
   Picard–Fuchs/period-relation attack, is the natural next move.
2. **Write out the `e`-window proof** (§3.5). The outline is complete; only the
   KKT case analysis needs to be made rigorous. `max e_hi = 25/64` is a clean
   target.
3. **Settle the Risch claim** for Theorem A's integrand (§2.4(ii)) over
   `ℚ(x, √(x⁴+4x²+1))`.
4. **Obtain Li (1988)**, or Anděl Ch. 11 — the single decisive document for the
   novelty question on both problems.
5. **Lean formalization.** Theorem A is now a legitimate target and a *different*
   one from the predecessor campaign's discriminant-volume statements: it is a
   Rice-formula identity plus an explicit definite integral. Problem B's exact
   sub-results (Propositions B1–B5, in particular `Λ = S(4−3S²)^{3/2}` and
   `K = 128/105`) are proved and are exactly the shape the existing Lean
   development handles. Flagged as a stretch goal, not started, consistent with
   the campaign's sequencing.

---

## Appendix: reproduction

| artifact | file |
|---|---|
| Theorem A verification (symbolic) | `src/probA_kacrice_verify.py`, `probA_kacrice_exact8.py` |
| Theorem A cross-check + 100 digits | `src/probA_kacrice_crosscheck.py`, `probA_kacrice_final.py`, `results/probA_kacrice.json` |
| `p_A` by independent quadrature | `results/gaussian_cubic_quad.json`, `gaussian_cubic_quad_ts.json` |
| `p_A` named-constant search | `results/identify_A_50digits.json`, `identify_A_calibration.json` |
| Problem B structure + validation | `src/quartic_common.py`, `results/quartic_structure.json` |
| Problem B high precision | `src/quartic_hiprec.py`, `results/quartic_final.json`, `quartic_hiprec.json` |
| Problem B independent MCs | `src/rootspaceB_check.py`, `quartic_gt_mc.py` |
| `e`-window extrema | `results/quartic_ebounds_exact.json`, `quartic_ebounds_global.json` |
| novelty | `results/novelty_check.json`, `novelty_check.md` |
| prior evidence document | `results/VERDICT_prepaper_backup.md` |
| full chronological log | `PROGRESS.md` |
