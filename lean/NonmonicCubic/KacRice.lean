/-
# Problem A: the Kac–Rice step, without Rice's formula

`GaussianCubic.lean` formalizes the algebraic skeleton of the derivation of

    P(x³ + a x² + b x + c has three real roots)
      = (1/π) ∫₀^∞ exp(−x⁴(x⁴+4x²+9)/(2(x⁴+4x²+1)))
                   · 2(x⁴+6x²+3)/(√(x⁴+4x²+1)(x⁴+4x²+9)) dx

for `(a,b,c)` i.i.d. `N(0,1)`, and records that the *probabilistic* content — the
Kac–Rice level-crossing step — was out of reach.

**This file exists because that assessment was too pessimistic.**  The Kac–Rice
step here does not need Rice's formula, or any theory of stochastic processes,
because `Z(x) = (a,b,c)·u(x)` is not a general process: it is a linear functional
of one fixed 3-dimensional Gaussian vector.  Concretely, the whole step is

1. integrate out `c` first — for fixed `(a,b)` the real roots of `f` are the
   solutions of `g(x) = −c` with `g(x) = x³ + a x² + b x`, a *deterministic*
   cubic, so this is the 1-D area formula and `g` has at most three monotone
   pieces;
2. swap the `x` and `(a,b)` integrals (Tonelli);
3. evaluate the inner `(a,b)` integral, which is an affine change of variables in
   `ℝ²` followed by the mean of a folded normal.

Nothing in that chain is a theorem about processes.  Step 3 in particular is
finite-dimensional linear algebra, and **this file proves its algebraic core**.

## The inner integral

With `A(x) = x³ + a x² + b x` and `B(x) = 3x² + 2 a x + b`, the inner integral is

    I(x) = ∫∫_{ℝ²} φ(a) φ(b) φ(A) |B| da db

where `φ` is the standard normal density.  Collecting the exponent
`a² + b² + A²` as a quadratic form in `(a,b)` gives the matrix, linear part and
constant

    M = ![![x⁴+1, x³], ![x³, x²+1]],   L = (2x⁵, 2x⁴),   K = x⁶,

so that `I(x) = (2π)^{-1/2} (det M)^{-1/2} exp(−R/2) · E|N(m, s²)|` with
`R = K − Lᵀ M⁻¹ L / 4` the residual exponent and `(m, s²)` the mean and variance
of `B` under the tilted Gaussian.  The four identities

    det M = q,   R = x⁶/q = h²,   m = x²(x⁴+2x²+3)/q,   s² = (x⁴+4x²+1)/q

are `detM_eq_qA`, `resid_eq_hA_sq`, `mB_eq` and `varB_eq` below, each a cleared
polynomial identity.  Together with `mB_eq_hA'_mul_sqrt` and `varB_eq_v_sq_mul`
— which say exactly `m = h′√q` and `s² = v²q`, hence `m/s = h′/v = z` — they
turn `I(x)` into the classical Kac–Rice integrand

    I(x) = φ(h) · [ v √(2/π) e^{−z²/2} + h′ (2Φ(z) − 1) ] .

The `√q` factors cancel because `E|N(λm, λ²s²)| = λ E|N(m,s²)|`: the
normalisation that makes `Z` unit-variance is exactly the normalisation that
makes `Z ⟂ Z′` (`GaussianCubic.dot_w_dw`), and it drops out of the ratio `m/s`.

## Status

Formalized here: the algebra of step 3 (this file).  Formalized in
`GaussianCubic.lean`: the algebra of the final assembly.  Formalized in
`OneRealRoot.lean`: the root-count dichotomy `N ∈ {1,3}` that turns `E[N]` into
`1 + 2p`.  **Not** formalized: the area formula of step 1, the Tonelli swap of
step 2, the folded-normal mean, and the Owen's-`T` cancellation.  See
`HANDOFF.md` for the current honest assessment of what each would cost.
-/
import NonmonicCubic.GaussianCubic

namespace NonmonicCubic.GaussianCubic

open Real

/-! ## The quadratic form of the inner integral

The exponent of the `(a,b)`-integrand of `I(x)` is `−(a² + b² + A²)/2` with
`A = x³ + a x² + b x`.  As a quadratic form in `(a,b)` this is
`½(a,b)ᵀ M (a,b) + ½ L·(a,b) + ½K` with `M`, `L`, `K` as in the header.  The
next three theorems verify that reading of the coefficients. -/

/-- The `(a,b)`-quadratic form really is `M`, `L`, `K`: expanding
`a² + b² + A²` with `A = x³ + a x² + b x` gives exactly
`(x⁴+1)a² + 2x³ab + (x²+1)b² + 2x⁵a + 2x⁴b + x⁶`. -/
theorem exponent_expand (x a b : ℝ) :
    a ^ 2 + b ^ 2 + (x ^ 3 + a * x ^ 2 + b * x) ^ 2
      = (x ^ 4 + 1) * a ^ 2 + 2 * x ^ 3 * (a * b) + (x ^ 2 + 1) * b ^ 2
        + 2 * x ^ 5 * a + 2 * x ^ 4 * b + x ^ 6 := by
  ring

/-- **`det M = q`.**  The determinant of the quadratic form is `x⁴+x²+1`, i.e.
exactly the `q` of `GaussianCubic`.  This is what makes the normalisation of
`I(x)` equal to `1/√q` — the standard deviation of `f(x)`. -/
theorem detM_eq_qA (x : ℝ) : (x ^ 4 + 1) * (x ^ 2 + 1) - x ^ 3 * x ^ 3 = qA x := by
  unfold qA; ring

/-- **The residual exponent is `h²`.**  Completing the square leaves
`R = K − Lᵀ M⁻¹ L / 4`.  Since `Lᵀ adj(M) L = 4x⁸(x²+1)`, clearing the single
denominator `det M = q` turns `R = x⁶/q` into this polynomial identity — and
`x⁶/q = h²` because `h = x³/√q`. -/
theorem resid_eq_hA_sq (x : ℝ) : x ^ 6 * qA x - x ^ 8 * (x ^ 2 + 1) = x ^ 6 := by
  unfold qA; ring

/-- The cofactor computation behind `resid_eq_hA_sq`: `Lᵀ adj(M) L = 4x⁸(x²+1)`
with `adj(M) = ![![x²+1, −x³], ![−x³, x⁴+1]]` and `L = (2x⁵, 2x⁴)`. -/
theorem L_adjM_L (x : ℝ) :
    (2 * x ^ 5) * ((x ^ 2 + 1) * (2 * x ^ 5) + (-x ^ 3) * (2 * x ^ 4))
      + (2 * x ^ 4) * ((-x ^ 3) * (2 * x ^ 5) + (x ^ 4 + 1) * (2 * x ^ 4))
      = 4 * x ^ 8 * (x ^ 2 + 1) := by
  ring

/-! ## The mean and variance of `B` under the tilted Gaussian

`B = 3x² + 2 a x + b`, i.e. `B = Bvec·(a,b) + 3x²` with `Bvec = (2x, 1)`.  Under
the Gaussian with quadratic form `M` and linear part `L` the mean of `(a,b)` is
`μ = −M⁻¹L/2` and the covariance is `M⁻¹`, so

    m  = Bvec·μ + 3x²,      s² = Bvecᵀ M⁻¹ Bvec.

Both are computed here in cleared form. -/

/-- `μ = −M⁻¹L/2 = (−x⁵/q, −x⁴/q)`, in cleared form: `M μ = −L/2`. -/
theorem M_mul_mu (x : ℝ) :
    (x ^ 4 + 1) * (-x ^ 5) + x ^ 3 * (-x ^ 4) = -(x ^ 5) * qA x ∧
      x ^ 3 * (-x ^ 5) + (x ^ 2 + 1) * (-x ^ 4) = -(x ^ 4) * qA x := by
  constructor <;> · unfold qA; ring

/-- **The mean.**  `m = Bvec·μ + 3x² = x²(x⁴+2x²+3)/q`, cleared of `q`. -/
theorem mB_eq (x : ℝ) :
    2 * x * (-x ^ 5) + (-x ^ 4) + 3 * x ^ 2 * qA x = x ^ 2 * (x ^ 4 + 2 * x ^ 2 + 3) := by
  unfold qA; ring

/-- **The variance.**  `s² = Bvecᵀ adj(M) Bvec / det M = (x⁴+4x²+1)/q`, cleared. -/
theorem varB_eq (x : ℝ) :
    (2 * x) * ((x ^ 2 + 1) * (2 * x) + (-x ^ 3) * 1)
        + 1 * ((-x ^ 3) * (2 * x) + (x ^ 4 + 1) * 1)
      = x ^ 4 + 4 * x ^ 2 + 1 := by
  ring

/-! ## Matching the normalised quantities

The Kac–Rice integrand is stated in terms of `h′` and `v`, which belong to the
*normalised* field `Z = (a,b,c)·u`.  The `(m, s²)` above belong to the raw
derivative `f′`.  The two differ by exactly one factor of `√q`, which cancels in
the ratio `m/s = h′/v = z` and against the `1/√q` in the normalisation. -/

/-- **`m = h′·√q`.**  With `h′ = x²(x⁴+2x²+3)/q^{3/2}` (`GaussianCubic.hasDerivAt_hA`)
and `m = x²(x⁴+2x²+3)/q`, this is the statement `m·q = x²(x⁴+2x²+3)`, i.e. one
factor of `√q` apart.  Stated in cleared form to avoid the radical. -/
theorem mB_eq_hA'_mul_sqrt (x : ℝ) :
    x ^ 2 * (x ^ 4 + 2 * x ^ 2 + 3) / qA x
      = (x ^ 2 * (x ^ 4 + 2 * x ^ 2 + 3) / (qA x * sqrt (qA x))) * sqrt (qA x) := by
  have hsq : sqrt (qA x) ≠ 0 := (Real.sqrt_pos.2 (qA_pos x)).ne'
  have hq : qA x ≠ 0 := qA_ne_zero x
  field_simp

/-- **`s² = v²·q`.**  With `v² = (x⁴+4x²+1)/q²` (`GaussianCubic.v_sq_eq`) and
`s² = (x⁴+4x²+1)/q`. -/
theorem varB_eq_v_sq_mul (x : ℝ) :
    (x ^ 4 + 4 * x ^ 2 + 1) / qA x = ((x ^ 4 + 4 * x ^ 2 + 1) / qA x ^ 2) * qA x := by
  field_simp

/-- **The ratio is `z`.**  Because `m = h′√q` and `s = v√q`, the argument of the
normal CDF in the Kac–Rice integrand is unchanged by the normalisation:
`m² / s² = (h′)² / v²`.  This is the reason the `√q` factors never appear in the
final formula.  Stated squared, so that no square roots occur. -/
theorem ratio_sq_aux {P W s : ℝ} (hW : W ≠ 0) (hs0 : s ≠ 0) :
    (P / (s * s)) ^ 2 / (W / (s * s)) = (P / (s * s * s)) ^ 2 / (W / (s * s) ^ 2) := by
  field_simp

/-- **The ratio is `z`.**  See `ratio_sq_aux`; here `s = √q`. -/
theorem ratio_sq_eq (x : ℝ) :
    (x ^ 2 * (x ^ 4 + 2 * x ^ 2 + 3) / qA x) ^ 2 / ((x ^ 4 + 4 * x ^ 2 + 1) / qA x)
      = (x ^ 2 * (x ^ 4 + 2 * x ^ 2 + 3) / (qA x * sqrt (qA x))) ^ 2
        / ((x ^ 4 + 4 * x ^ 2 + 1) / qA x ^ 2) := by
  have hq : (0 : ℝ) < qA x := qA_pos x
  have hs : sqrt (qA x) * sqrt (qA x) = qA x := Real.mul_self_sqrt hq.le
  have hs0 : sqrt (qA x) ≠ 0 := (Real.sqrt_pos.2 hq).ne'
  have hW : x ^ 4 + 4 * x ^ 2 + 1 ≠ 0 := by positivity
  have key := ratio_sq_aux (P := x ^ 2 * (x ^ 4 + 2 * x ^ 2 + 3))
    (W := x ^ 4 + 4 * x ^ 2 + 1) (s := sqrt (qA x)) hW hs0
  rwa [hs] at key


/-! ## The Owen's-`T` step is rational algebra

The final assembly needs `θ′` where `θ = arctan(z/h)`.  Written as
`θ′ = (h z′ − z h′)/(h² + z²)` it is a genuine `0/0` at `x = 0` — both `h` and
`z` vanish there (`h ≈ x³`, `z ≈ 3x²`), and `h² + z² = x⁴(x⁴+4x²+9)/(x⁴+4x²+1)`
vanishes to order `x⁴`.  But `θ′` has an explicit closed form with **no removable
singularity at all** (verified to 30 digits, 2026-08-18):

    θ′ = (x⁸ + 6x⁶ − 6x⁴ − 22x² − 3) / ( q · √(x⁴+4x²+1) · (x⁴+4x²+9) )

— the denominator being the factorisation `denom_theta_deriv` below of the
degree-12 polynomial that the raw quotient produces.  At `x = 0` this gives
`θ′(0) = −3/(1·1·9) = −1/3`, matching the limit.

Consequently **equation (8) is not a nested-radical identity at all**.  With
`v = √(x⁴+4x²+1)/q`,

    v + θ′ = [ (x⁴+4x²+1)(x⁴+4x²+9) + (x⁸+6x⁶−6x⁴−22x²−3) ]
             / ( q · √(x⁴+4x²+1) · (x⁴+4x²+9) )

and the target `2(x⁴+6x²+3)/(√(x⁴+4x²+1)(x⁴+4x²+9))` matches iff the numerator
equals `2(x⁴+6x²+3)·q`.  That is `eq8_numerator`, a one-line `ring`.

This supersedes `GaussianCubic.key_eq8`, which proved equation (8) by clearing
*both* nested radicals — the step the original verification could only check
numerically.  Given the closed form for `θ′`, no radical needs clearing. -/

/-- The degree-12 denominator produced by the raw quotient form of `θ′` factors
as `q · (x⁴+4x²+1) · (x⁴+4x²+9)`. -/
theorem denom_theta_deriv (x : ℝ) :
    x ^ 12 + 9 * x ^ 10 + 35 * x ^ 8 + 74 * x ^ 6 + 75 * x ^ 4 + 49 * x ^ 2 + 9
      = qA x * (x ^ 4 + 4 * x ^ 2 + 1) * (x ^ 4 + 4 * x ^ 2 + 9) := by
  unfold qA; ring

/-- **Equation (8), reduced to one polynomial identity.**  Over the common
denominator `q · √(x⁴+4x²+1) · (x⁴+4x²+9)`, the claim `v + θ′ = 2(x⁴+6x²+3) /
(√(x⁴+4x²+1)(x⁴+4x²+9))` is exactly this. -/
theorem eq8_numerator (x : ℝ) :
    (x ^ 4 + 4 * x ^ 2 + 1) * (x ^ 4 + 4 * x ^ 2 + 9)
        + (x ^ 8 + 6 * x ^ 6 - 6 * x ^ 4 - 22 * x ^ 2 - 3)
      = 2 * (x ^ 4 + 6 * x ^ 2 + 3) * qA x := by
  unfold qA; ring

/-- `θ′(0) = −1/3`: the closed form has no singularity at the origin, where the
quotient form `(h z′ − z h′)/(h² + z²)` is `0/0`. -/
theorem theta_deriv_at_zero :
    ((0 : ℝ) ^ 8 + 6 * 0 ^ 6 - 6 * 0 ^ 4 - 22 * 0 ^ 2 - 3)
        / (qA 0 * Real.sqrt (0 ^ 4 + 4 * 0 ^ 2 + 1) * (0 ^ 4 + 4 * 0 ^ 2 + 9))
      = -(1 / 3) := by
  norm_num [qA]

end NonmonicCubic.GaussianCubic
