# Closed forms for the real-rootedness probability of a random cubic

*Theorems 1 and 2 derived 2026-08-17; every calculus identity is verified in exact
arithmetic by `src/closed_form.py` (12/12 steps PASS), confirmed by adaptive
quadrature (`src/reduce_monic.py`) and 2×10⁸-sample Monte Carlo (`src/mc_engine.py`).
Theorem 3 derived and verified the same day on a dedicated compute server (full
record: `VERDICT.md`, `PROGRESS.md`); its derivation and verification are
summarized below.*

## Statements

**Theorem 1.** Let (a,b,c) be i.i.d. uniform on [−1,1]. Then

> P( x³ + ax² + bx + c has three real roots ) = **383/4860 + ln(3)/48**
> = 0.10169434037605886959954086…

**Theorem 2.** Let (a,b,c) be i.i.d. uniform on [0,1]. Then

> P( x³ + ax² + bx + c has three real roots ) = **1/2880** = 0.000347222…

**Theorem 3.** Let (a,b,c,d) be i.i.d. uniform on [−1,1]. Then

> P( ax³ + bx² + cx + d has three real roots ) = **641/2430 − ln(3)/24**
> = 0.21801049620261477108898412335868…

Unlike Theorems 1 and 2, this *value* is not new — it is the closed form an
unrefereed, AI-assisted forum thread (dxdy.ru, June 2026) had already guessed.
What Theorem 3 supplies is the first verified derivation of it, and the
retraction of a conflicting quadrature estimate (0.217993225) that this
project's own literature sweep had produced and believed. See "Novelty status"
below for the full account.

## The reduction (common to both)

Write f(x) = x³ + ax² + bx + c and g(x) = x³ + ax² + bx, so f = g + c.
For b < a²/3 put s = √(a² − 3b); the critical points of f are

- x₋ = (−a − s)/3 (local max), x₊ = (−a + s)/3 (local min).

f has three real roots iff f(x₋) ≥ 0 ≥ f(x₊), i.e. iff c lies in the **band**

- c ∈ [c_lo, c_hi], c_lo = −g(x₋), c_hi = −g(x₊), with width
  c_hi − c_lo = (4/27) s³.  (identity S1)

This is not merely an implication but captures the discriminant exactly:
as a polynomial in c,

- Δ(a,b,c) = −27 (c − c_lo)(c − c_hi).  (identity S2, verified by expansion)

For b > a²/3 the quadratic in c has no real roots and Δ < 0 (one real root).
Hence for any c-window [w_lo, w_hi],

- Vol = ∫∫_{b < a²/3} len( [c_lo, c_hi] ∩ [w_lo, w_hi] ) db da.

## Proof of Theorem 1

**Never-clipped lemma.** On D = {(a,b) : a ∈ [−1,1], b ∈ [−1, a²/3]} we claim
c_hi ≤ 1, with equality only at (a,b) = (−1,−1).

1. ∂c_hi/∂a = −x₊² ≤ 0 (since ∂g/∂a at fixed x is x², and g′(x₊) = 0 kills the
   chain-rule term). So c_hi is non-increasing in a.
2. b ≤ a²/3 ≤ 1/3 for all a ∈ [−1,1], so for any (a,b) ∈ D the point (−1,b) is
   also in D, and by 1: c_hi(a,b) ≤ c_hi(−1,b).
3. On the edge a = −1: ∂c_hi/∂b = −x₊ with x₊ = (1 + √(1−3b))/3 > 0, so c_hi is
   strictly decreasing in b; its maximum over b ∈ [−1, 1/3] is at b = −1:
   c_hi(−1,−1) = 1 exactly.

The map (a,b,c) → (−a,b,−c) preserves Δ (checked by expansion) and the cube, and
sends c_hi to −c_lo; hence c_lo ≥ −1 on D as well. **The band never exits the
window [−1,1]**: it touches the boundary only at the two corner points
(∓1,−1,±1), a set of measure zero. Therefore

Vol = ∫_{−1}^{1} ∫_{−1}^{a²/3} (4/27)(a² − 3b)^{3/2} db da
    = (8/405) ∫_{−1}^{1} (a² + 3)^{5/2} da
    = 3064/1215 + (8/3)·asinh(1/√3).

With asinh(1/√3) = ln(1/√3 + 2/√3) = ln √3 = ln(3)/2:

P = Vol/8 = **383/4860 + ln(3)/48**. ∎

*Remark.* The corner-touching geometry is exactly why this was solvable: the
"obvious" program (main term plus clipping corrections) has all corrections
identically zero, so the naive upper bound is the answer. A Monte Carlo alone
would never reveal this; the quadrature landing on the upper bound to 16 digits
was the tell.

## Proof of Theorem 2

Domain: a ∈ [0,1], b ∈ [0, a²/3], window [0,1].

1. x₋ ≤ 0 and (since b ≥ 0 forces s ≤ a) x₊ ≤ 0.
2. c_hi ≥ 0: g(0) = 0 and g′(0) = b ≥ 0, and x₊ ≤ 0 is the local **min**
   location, so g(x₊) ≤ 0. Moreover c_hi ≤ 1/27 on the whole domain
   (max on the boundary curves b = a²/3, where c_hi = a³/27, and the a = 1 edge,
   where it increases in b to 1/27). So the top of the window never matters.
3. The bottom does: ∂c_lo/∂b = −x₋ ≥ 0, and c_lo = 0 exactly on **b = a²/4**
   (there x₋ = −a/2 and g(−a/2) = 0). So c_lo ≤ 0 for b ≤ a²/4 and c_lo ≥ 0 for
   a²/4 ≤ b ≤ a²/3: a single sign change.

Hence the overlap length is c_hi on [0, a²/4] and the full band width
(4/27)s³ on [a²/4, a²/3], and

∫_0^{a²/4} c_hi db + ∫_{a²/4}^{a²/3} (4/27)(a²−3b)^{3/2} db = a⁵/480

— all fractional powers cancel (this is the small miracle of Theorem 2; verified
symbolically). Integrating over a ∈ [0,1]:

P = ∫_0^1 a⁵/480 da = **1/2880**. ∎

## Proof of Theorem 3

Theorem 3 drops the monic restriction: the leading coefficient a is now free
on [−1,1] too, including near 0. This is a genuinely 4-dimensional problem, and
the never-clipped trick behind Theorem 1 does not apply directly — that trick
was special to a symmetric window of half-width exactly 1 around a *fixed*
leading coefficient. The route that works instead is structural, not a
generalization of Theorems 1–2's calculus.

**The set is a cone.** The discriminant

    Δ(a,b,c,d) = 18abcd − 4b³d + b²c² − 4ac³ − 27a²d²

is homogeneous of degree 4, so Δ(λx) = λ⁴Δ(x) and the real-rooted set
R = {Δ > 0} is invariant under x → λx (λ > 0). Apply the divergence theorem to
the vector field F = x/4 (div F = 1) on R ∩ [−1,1]⁴. By Euler's identity,
x·∇Δ = 4Δ, which vanishes on the lateral boundary {Δ = 0} — so that part of the
surface integral is identically zero, and only the eight faces of the cube
contribute:

    vol₄(R ∩ [−1,1]⁴) = (1/4) ∮ F·n dS = (1/4)·4·(sum of the 8 face integrals of x·n).

Central symmetry (a,b,c,d) → (−a,−b,−c,−d) pairs opposite faces (they contribute
equally), and the coefficient-reversal (a,b,c,d) → (d,c,b,a) — which sends a
root x to its reciprocal 1/x and so preserves both R and the cube — identifies
the a=1 face with the d=1 face, and the b=1 face with the c=1 face:

    S_a = S_d,   S_b = S_c,   vol₄(R∩[−1,1]⁴) = ½(S_a+S_b+S_c+S_d) = V(1) + S_b,
    P = vol₄/16 = ( V(1) + S_b ) / 16,

where V(1) = S_a = 766/1215 + ln(3)/6 is exactly 8× Theorem 1 (already proved),
and

    S_b = vol₃{ (a,c,d) ∈ [−1,1]³ : a x³ + x² + c x + d has 3 real roots }

is the volume on the face where the *second* coefficient is pinned to 1 — a new,
but purely 3-dimensional, problem, with no t → ∞ tail and no a → 0 endpoint
singularity (both of which sink a direct attack on P via ∫₀¹ (a³/8)V(1/a) da,
see the note at the end of this proof).

**S_b is elementary.** Substitute s = √(1 − 3ac) (so c = (1 − s²)/(3a)). The
admissible-d band for this face is [−K₋/u, K₊/u] with

    K₊ = (s−1)²(2s+1),   K₋ = (s+1)²(2s−1),   u = 27a²,   K₊ + K₋ = 4s³,

on the domain {s ∈ (0,2), a ∈ [|s²−1|/3, 1]}. The move that makes this tractable
is integrating over a *first*, at fixed s — a enters only through u = 27a², so
the a-integral is elementary once two clipping lemmas are settled:

- **L1 (never clips above).** d_hi ≤ 1 throughout: α₊ := √(K₊/27) < a₀ := |s²−1|/3
  reduces to 2s+1 < 3(s+1)², true for all s. The exact analogue of Theorem 1's
  never-clipped lemma.
- **L2 (clips below exactly for s ∈ (2/3, 2)).** α₋ := √(K₋/27) > a₀ reduces to
  (3s−2)(s−2) < 0; and α₋ < 1 reduces to (s+1)²(2s−1) < 27, i.e. s < 2, with
  equality precisely at s = 2.

With these, F(s) := ∫_{a₀}^1 (band length)/a da is elementary — the awkward term
−K₊/(2K₋) + 2s³/K₋ collapses to the constant 1/2 via K₊+K₋ = 4s³ — giving

    F(s) = (2s³/27)(1/a₀² − 1)                                 for s ≤ 2/3
    F(s) = K₊/(54a₀²) + 1/2 + ln(α₋/a₀) − 2s³/27               for 2/3 < s < 2

(continuous at s = 2/3: both sides equal 11264/18225). Then

    S_b = (4/3) ∫₀² s F(s) ds = 1454/405 − (5/6)ln(3),

and

    P = ( 766/1215 + ln(3)/6 + 1454/405 − (5/6)ln(3) ) / 16
      = **641/2430 − ln(3)/24**. ∎

*Verification of the cone step.* The divergence-theorem reduction is the one
genuinely new structural move, so it was tested against a case with an
independently known answer: applied to q² > 4pr on [−1,1]³ (also a cone, since
the quadratic discriminant is homogeneous), the three faces give
S_p = S_r = 13/6 and S_q = 5/2 + ln 2, and (1/3)·2·(S_p+S_q+S_r) works out to
41/9 + (2/3)ln2 — exactly 8·(41/72 + ln2/12), the known full-quadratic volume
(Theorem A3 in `exact_anchors.py`). Symbolic match; the step is an identity.

*Why not compute V(t) directly, as the natural-looking route P = ∫₀¹(a³/8)V(1/a)da
would suggest?* The cone's closed form exists specifically because *scale* is
integrated first; reversing that order leaves algebraic-function integrands whose
shape moves with the outer variable, which is not elementary in general.
Numeric evidence: p(a) := a³V(1/a)/8 = 0.173255634778455174251141172449419764456…
at a=1/2 and 0.227731231210036852659720324839651789782… at a=1/3 (both to 40
digits); PSLQ against {1, ln2, ln3, ln5, √2, √3, π} finds nothing. V(1) is
elementary only because t=1 is exactly where Theorem 1's corner-touching
geometry applies — not because V(t) is nice in general. (A 25-digit table of
V(t) for t = 1…50, computed two independent ways, is in `results/vt_table.json`
regardless.)

## Verification summary

| | Theorem 1 | Theorem 2 | Theorem 3 |
|---|---|---|---|
| symbolic (sympy, exact) | PASS (T1_closed_form) | PASS (T2_closed_form) | PASS (`P − candidate = 0`) |
| independent numerical route sharing no step with the proof | quadrature ~1e-16 | quadrature ~1e-13 | route 1 (leading-coefficient/V(t) order): 19 significant digits, diff 7.0e-20 |
| blind constant recognition | — | — | PSLQ on 22-digit S_b returns 1454/405 − (5/6)ln3 unprompted |
| Monte Carlo | 2×10⁸: 0.10172336 ± 2.31e-5 (+1.26σ) | 2×10⁸: 0.00034664 ± 1.30e-6 (−0.45σ) | 4×10¹⁰, raw sign(Δ): 0.218008985 ± 2.1e-6 (−0.73σ) |
| pipeline calibration | depressed-cubic anchor reproduced to 26 digits (2√3/45) | same pipeline | V(1), depressed anchor, and p(1)=Theorem 1 all reproduced through the new code paths to ≥1.1e-41 before any new number was believed |

Theorem 3's verification is unusually thorough because it corrected a wrong
number this project had itself produced: a literature-sweep quadrature had
claimed P = 0.217993225 ± 5e-8, off by +1.7271e-05 (~345× its own error bar).
A full post-mortem — including an honest admission that the specific failure
mode could not be reconstructed — is in `VERDICT.md`. Two general lessons from
that chase, worth keeping in mind for any future work on this integrand family:
(1) near a=0 the conditional probability has a √a endpoint singularity that a
plain Gauss rule loses ~7 digits on while reporting no warning; (2) a
quadrature routine's own convergence/error estimate is not evidence on this
integrand — only agreement between structurally independent computations is.

## Novelty status

Settled 2026-08-17 by an 8-agent literature sweep plus a targeted prior-art
search (full detail: LITERATURE.md §1):

- **Theorem 1**: the probability 383/4860 + ln(3)/48 has never been stated or
  published anywhere findable (OEIS direct query: no match; MSE/MO site
  searches: zero threads; digit searches empty). Two caveats: (a) the equivalent
  volume V₀ = 766/1215 + ln3/6 appears — unnormalized, uninterpreted as a
  probability — in an AI-derived dxdy.ru forum derivation of the non-monic case
  (June 2026, unrefereed, unindexed); (b) Li (1988) derived an exact expression
  for the cubic family x³+3ax²+3bx+2c with coefficients uniform on symmetric
  intervals, which specializes to our model at h=k=1/3, l=1/2 (established from
  the recovered MR 89j:60069 review); the paper is paywalled, essentially
  uncited, and no value from it has ever been reproduced — ILL check pending.
- **Theorem 2**: 1/2880 is **likely new** — Li's cubic special cases are all
  symmetric intervals (the one-sided [0,1] cube is not among them), and the
  value appears nowhere else.
- **Theorem 3**: the *value* 641/2430 − ln(3)/24 is not new — it is exactly the
  closed-form candidate the dxdy.ru forum thread (June 2026, unrefereed,
  AI-assisted, unindexed by any search engine) had already reached. What is new
  is the derivation above (the cone/divergence-theorem reduction, verified
  independently multiple ways) and the retraction of this project's own
  0.217993225 ± 5e-8 literature-sweep quadrature, which that derivation refutes
  by +1.7271e-05 — about 345× its claimed error bar. Full account, including an
  honest attempt (unsuccessful) to reconstruct exactly how the sweep went wrong,
  in `VERDICT.md`.
