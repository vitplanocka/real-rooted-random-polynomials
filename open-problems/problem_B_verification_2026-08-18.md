# Problem B / `C_clip`: independent verification of the external candidate

Written 2026-08-18. Subject: `problem_B_candidate_result.md` (external agent,
not this campaign). Every claim below was re-derived from scratch — no code,
constant or intermediate step of the submission was reused, except where the
task is explicitly "check the submission's own formula", in which case the
formula was re-implemented independently from its written statement.

**Headline.** The submission is substantially correct, and it contains one
genuinely new mathematical contribution. It does **not** implicate the master
decomposition `16 p_B = U − C_clip`, which is confirmed unchanged. Three
transcription-level errors were found and corrected.

---

## Claim 1 — the "factor of 2" — CONFIRMED as an arithmetic fact, REFUTED as a defect in this campaign

The submission asserts that the triple integral as displayed in the operator's
`c_clip_problem_statement.md` and the target `C_clip` "cannot both be correct".
That is true. It is **not** a bug in any of this campaign's derivations.

### What was checked, and how

**(a) The change of variables, re-derived from scratch** (`sympy`, nothing reused).
Depressing `f = x⁴+bx³+cx²+dx+e` and matching against `(y²−m)²+δy+ε′`:

    m       = 3b²/16 − c/2                             (matches VERDICT §3.2)
    c(b,m)  = 3b²/8 − 2m ,  and  c ≥ −1  ⟺  m ≤ (3b²+8)/16 = M(b)
    d(b,m,τ) = τ·m^{3/2} + b³/16 − b·m                 (residual exactly 0)
    |∂(b,c,d)/∂(b,m,τ)| = **2 m^{3/2}**                (residual exactly 0)

So the integrand of `16 p_B` is `L·|J| = m²Λ(τ)·2m^{3/2} = **2**·m^{7/2}Λ(τ)`.
The factor 2 is the Jacobian. It is mandatory.

**(b) `VERDICT.md` already carries it.** Proposition B5 defines
`U := (4K/9)·2^{−18}∫(3b²+8)^{9/2}db`, and `4K/9 = 2·K·(2/9)` is exactly
`2 · ∫₀^{M} m^{7/2}dm · ∫Λdτ` integrated over `b`. Numerically all three agree
to 40 digits:

| route | `U` |
|---|---|
| VERDICT Prop B5 integral, as written | 0.08806695966062686065936138806504388635748 |
| VERDICT closed form `√3·asinh(√6/4)/90 + 7013√11/302400` | (same) |
| re-derived here as `2∫db∫m^{7/2}dm·K` | (same) |

and `(U − C_clip)/16 − p_B = 2.0e-53` at dps 60. **The master decomposition is
internally consistent and unaffected.**

**(c) The correct `C_clip`, by a route sharing no algebra with the reduction.**
A from-scratch Monte Carlo in raw `(b,c,d)` using *only* the definition of the
band (critical points of `f`, `L = g(x₂) − max(g(x₁),g(x₃))`), N = 3×10⁸:

    C_raw = 0.000638526 ± 8.79e-7
      vs campaign C_clip = 0.000637674…   z = **+0.97**
      vs submission's literal C_w = 0.000318837…   z = **+363.6**

**(d) The literal integral, to high precision.** A nested `mpmath` quadrature of
the literal formula *without* the prefactor, using an exact antiderivative
`G(τ) = ∫_τ^{τ_c}Λ = U^{5/2}(4/5 − 4U/21)`, `U = 4−3S(τ)²`, derived here:

    I  = 0.0003188371055922925…   (rel. diff from submission's C_w: 3.9e-12)
    2I = 0.0006376742111845850…   (rel. diff from campaign C_clip:  3.9e-12)

and the submission's own formula (1), independently re-implemented from its
written statement with the two corrections below, reproduces
**all 75 quoted significant digits** of `I` at dps 120.

### Verdict

`C_w(literal, no prefactor) = C_clip / 2` — **confirmed to 75 digits**.

The missing 2 lives in `c_clip_problem_statement.md`, a file written ad hoc for
the external agent that **does not exist in this repository** and is referenced
nowhere in `PROGRESS.md` or `VERDICT.md`. There is therefore nothing to
propagate: none of the four independent derivations of `U` needs a fix, and no
number in `VERDICT.md` changes. The instruction in the submission to "replace
the prefactor 8/5 by 16/5" for the campaign's target is correct and is the whole
of the required adjustment.

### The symmetry rewrite is legitimate, and is not where the 2 hides

Checked separately, as asked. With `τ⁺ := (1 − b³/16 + bm)/m^{3/2}` (the `d>1`
threshold) and `τ⁻ := (−1 − b³/16 + bm)/m^{3/2}` (the `d<−1` threshold), one has
identically `τ⁺(−b, m) = −τ⁻(b, m)`, and `M(b)` is even. Since `Λ` is even, the
`d>1` and `d<−1` halves are exactly equal — a genuine involution identity, no
value change. The submission's bound ruling out `d>1` for `b ≥ 0` also checks:
`τ_c·(11/16)^{3/2} + 1/16 = 11√33/72 + 1/16 = 0.94016 < 1`.

---

## Claim 2 — the one-dimensional reduction — CONFIRMED, after two corrections

Verified symbolically (exact zero residuals) and numerically.

**Correct as written:**

* `4(S³−S+z−z³) = 4(S−z)(z−α)(z−β)`, `α,β = (−S±D)/2`, `D = √(4−3S²)` — exact;
  roots of `P_S` numerically confirmed to be `{S, α, β}` to 49 digits.
* `A = S−α = (3S−D)/2`, `B = S−β = (3S+D)/2`, `B−A = D`.
* The exponent bookkeeping: `A`, `B`, `D` each appear to the power `−17/3`
  (they must all be equal for the submission's `(ABD)^{17/3}` to be legitimate —
  they are), and `(B−At)^8`.
* Incomplete-beta parameters `(j − 7/3, −7/3)`.
* `A_2(z) = −1/(9·4¹⁰z⁹)`, `A_2′ = (4z)^{−10}` — exact.
* `W(S) = 4S(3S²−1)(4−3S²)^{3/2} = Λ(τ(S))·dτ/dS` — exact; `∫₁^{2/√3}W dS = 64/105`.
* The geometry of §2: `z = x/(4√m)`, `xm − x³/16 = 4z(1−z²)m^{3/2}`,
  `dx = 4√m dz`, `m ≤ 1/(2(1−3z²))`, `m ≤ 1/(16z²)`, crossover `z₀ = 1/√11`,
  `T(z)` on both branches, `τ₀ = T(z₀) = 24/(11√11)`, and the `S=S_c` endpoint
  `z₋ = x*/√(3x*²+8)` — all re-derived and confirmed.
* `S₀ = 1.0738485773747064866325892325163791366805`.

**ERROR 1 — the `A_1` `artanh` coefficient.** As written,

    A_1′(z) − [2(1−3z²)]^{−5}  =  35/(2048(1−3z²))  ≠ 0.

Solving the ansatz gives a *unique* correct constant:

    A_1(z) = z/(256h⁴) + 7z/(1536h³) + 35z/(6144h²) + 35z/(4096h)
             + (35√3/**12288**)·artanh(√3 z),        h = 1−3z²

i.e. the submission's `35√3/4096` is **3× too large**. With `35√3/12288` the
residual is exactly 0.

**ERROR 2 — the Möbius map is inverted.** As written,
`t_S(z) = A(z−β)/(B(z−α))` sends `(α,S)` to `(1,∞)`, all four Möbius identities
fail, and `E(S;·,·)` comes out complex (the `(1−t)^{−10/3}` branch cut). The
correct map is the reciprocal:

    t_S(z) = **B(z−α)/(A(z−β))** = [(z−α)/(z−β)]·[(S−β)/(S−α)]

With this, `t_S(α)=0`, `t_S(S)=1`, `t` is monotone increasing on `(α,S)`, and all
four stated identities

    z−α = tAD/(B−At),  z−β = BD/(B−At),  S−z = AB(1−t)/(B−At),
    dz  = ABD/(B−At)² dt

hold with **exact zero residuals**, and the beta sum matches direct quadrature
of `∫P_S^{−10/3}dz` to **45–58 digits** at every `S` tested.

**End-to-end.** With both corrections and the prefactor `8/5`, formula (1)
reproduces the literal integral to **all 75 quoted digits** at dps 120
(stable across dps 30/40/60/80/120). Diagnostic table:

| variant | value / target |
|---|---|
| 8/5, `35√3/12288`, corrected Möbius | **1.000000000000000** |
| 16/5, corrected | 2.000000000000000 |
| 8/5, `35√3/4096` | 1.45592697993183 |
| inverted Möbius | complex |

*Practical note:* the closed-form `E` is catastrophically ill-conditioned as
`D → 0` (an 8th-order finite difference times `(ABD)^{−17/3}`); near `S_c` it
needs substantial guard digits or the direct quadrature.

Also confirmed: `z_L(S)` never actually goes negative (it runs from `z₀ =
0.301510` down to `0.203447`), and `α < z_L < z_R < S` strictly, so the
`z`-integral is a **proper** integral with no endpoint singularity.

---

## Claim 3 — non-elementarity — CONFIRMED as sound; but largely classical

**The Hermite reduction — CONFIRMED exactly.** The relation

    t(1−t)R′ + (7/3)(2t−1)R + γ·t³(1−t)³ = (1−ρt)⁸,   deg R ≤ 7

was re-derived from scratch (the coefficient `7/3`, the sign of `(2t−1)` and the
power `t³(1−t)³` are all right); the 9×9 linear system has a unique solution;
and

    γ(ρ) = −(10/7)(ρ²−ρ+1)(11ρ⁶−33ρ⁵+12ρ⁴+31ρ³+12ρ²−33ρ+11)

is confirmed identically. Pointwise numerical check of the differential
identity: max residual 1.2e-33 at ρ=2/5, 4.8e-33 at ρ=4/5.

**`γ ≠ 0` — CONFIRMED, and stronger than claimed.** Sturm root-counting gives
`γ` **no real roots at all**; `γ < 0` on all of `(0,1)` (`γ(0)=γ(1)=−110/7`,
`γ(1/2)=−1215/896`). The palindromic substitution
`sextic = ρ³(11u³−33u²−21u+97)`, `u = ρ+1/ρ`, is exact (the constants `−21`,
`97` are correct).

**ERROR 3 — the stated minimum is wrong.** `q(u) = 11u³−33u²−21u+97` has
`q′ = 3(11u²−22u−7)`, critical point `u = 1 + 3√22/11 ≈ 2.2792`, and

    min_{u≥2} q(u) = **54 − (108/11)√22 ≈ 7.9486**

not the claimed `54 − (11/108)√22 ≈ 53.52` — the fraction is inverted. The
positivity conclusion is unaffected (`q(2) = 11`, no real root with `u ≥ 2`).
Note also that the submission *asserts* `γ ≠ 0` without proof; the Sturm
computation above supplies one.

**The geometry — CONFIRMED.** Genus of `y³ = t(1−t)` is **1**, by three
independent routes: Riemann–Hurwitz (totally ramified over `0`, `1`, `∞`, one
point over each, `2g−2 = 3(−2)+3·2 = 0`); the homogenisation is a *smooth* plane
cubic; and the Weierstrass form `V² = U³+16`, `Δ ≠ 0`, `j = 0`. The divisor is

    div(ω) = P₀ + P₁ − 2P_∞ ,  ω = dt/y      (degree 0 = 2g−2 ✓)

— one point over `t=∞`, a double pole there, simple zeros at `P₀,P₁`, all
residues zero. The submission's description is right. On the Weierstrass model
`ω` is the classical second-kind differential `x dx/y`, whose primitive is the
Weierstrass `ζ`; its non-exactness also follows from the Legendre relation, an
independent confirmation.

**The Rosenlicht/Riemann–Roch chain — sound, two steps compressed.**
`ℓ(P) = 1` for a degree-1 divisor on a genus-1 curve is right, `ω = dg` forces a
single simple pole, and the contradiction closes. Two standard justifications
are stated only as phrases and should be written out: (i) "choose the constants
`ℚ`-linearly independent" needs the integer-exponent rescaling *plus* "a
function with empty divisor on a **complete** curve is constant"; (ii)
Rosenlicht's no-new-constants hypothesis should be invoked explicitly.
Two smaller inaccuracies: the map to `y³ = t(1−t)` is **birational**, not
literally a Möbius map of `z` alone (`w` must be rescaled by `γt+δ` and by a cube
root of a constant); and "three distinct branch points" needs `S ≠ 1/√3`, which
is harmless here since `S ∈ (1.0738, 1.1547)`.

**But the conclusion is classical.** `∫t^{−1/3}(1−t)^{−1/3}dt` is a binomial
differential with `p = −1/3`, `(m+1)/n = 2/3`, `(m+1)/n + p = 1/3`. **Chebyshev's
1853 criterion**: elementary iff one of those three is an integer. None is.
Non-elementary, one line, no Riemann surfaces. The genus/Rosenlicht apparatus is
correct but over-engineered for what it concludes.

**What is genuinely new here** is therefore the *Hermite reduction* — the
integrand `(1−ρt)⁸t^{−10/3}(1−t)^{−10/3}` is a **trinomial**, outside Chebyshev's
reach — together with the explicit `γ(ρ)` and its non-vanishing. That step is
real work and it survives scrutiny.

---

## Claim 4 — the `(S,θ)` reparametrisation — CONFIRMED

* `S = (2/√3)cos θ  ⟹  τ = 4S(S²−1) = τ_c·cos(3θ)` — exact, **no sign flip**;
  `θ ∈ [0, π/6]` covers `S ∈ [1, 2/√3]` (`θ=0 ↔ S=S_c ↔ τ=τ_c`,
  `θ=π/6 ↔ S=1 ↔ τ=0`), traversed opposite to `τ`.
* `Λ(τ)|dτ| = (128/3)·cos θ·sin⁴θ·(4cos²θ − 1) dθ` — exact, **but only with the
  absolute value**: `dτ/dθ < 0` on `(0,π/6)`, so the raw signed `Λ dτ/dθ` is the
  negative of the stated expression.
* Consistency: `∫₀^{π/6}(128/3)cos θ sin⁴θ(4cos²θ−1)dθ = 64/105` exactly, matching
  `∫₀^{τ_c}Λ dτ`.

---

## By-products: campaign results independently re-confirmed

While checking the above, the following were re-established from scratch:

* `Λ(τ) = S(4−3S²)^{3/2}` (Prop B3) matches the *definitional* band length of
  `(z²−1)²+τz` (computed via `mp.polyroots`) to **25 digits** at seven values of `τ`.
* `∫_{−τ_c}^{τ_c}Λ dτ = 128/105` (Prop B4) — exact, and `G(−τ_c) = 128/105`.
* `M(b) = (3b²+8)/16` and its equivalence to `c ≥ −1`; `d = τm^{3/2}+b³/16−bm`;
  `|J| = 2m^{3/2}` (§3.4).
* `U` and `16 p_B = U − C_clip` self-consistent to 53 decimals.

## What this does *not* establish

No closed form for `C_clip`. The non-elementarity result is about the **inner
`z`-integral at fixed `S`**, not about the final constant, and the submission
says so itself. The PSLQ negative in `VERDICT.md` stands, and is now better
explained: the intrinsic object is an incomplete elliptic period (on a `j=0`
curve) at moving algebraic endpoints, so an elementary-logarithmic PSLQ basis was
structurally too narrow. That is an explanation of the negative result, not a
replacement for it.
