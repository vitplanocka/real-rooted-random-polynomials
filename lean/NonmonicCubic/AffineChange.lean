/-
# Step 3d: the affine change of variables in `ℝ²`

The inner integral of the Kac–Rice route is

    I(x) = ∫∫ φ(a) φ(b) φ(A) |B| da db,
    A = x³ + a x² + b x  (= f(x) − c),   B = 3x² + 2 a x + b  (= f′(x)).

`KacRice.lean` proves the linear algebra behind its evaluation.  This file
supplies the analytic step, and the point is that **no 2×2 Jacobian is needed**:
the map `(a,b) ↦ (a, B)` is a *shear*, i.e. at fixed `a` it is a translation in
`b`, with Jacobian `1`.  After that shear the exponent is a quadratic in `a` at
fixed `β = B`, so the `a`-integral is an ordinary one-dimensional Gaussian
integral with a linear term, and what is left is a folded normal in `β` —
`FoldedNormal.integral_abs_scaled`.

Two ingredients, both proved here:

* `integral_exp_quadratic` — `∫ exp(−(W a² + 2 c a + d)/2) da = √(2π/W)·exp(−(d − c²/W)/2)`
  for `W > 0`, i.e. the Gaussian integral with a linear term (Mathlib has only
  the centred `integral_gaussian`);
* `exponent_completeSquare` — the exact completion of the square for the sheared
  exponent, which is where the affine change of variables actually happens:

      a² + b² + A²  =  W·(a + c(β)/W)²  +  (β − m)²/s²  +  h²

  with `b = β − 2ax − 3x²`, `W = x⁴+4x²+1`, and `m`, `s²`, `h²` exactly the
  quantities of `KacRice.lean` (`mB_eq`, `varB_eq`, `resid_eq_hA_sq`).  The
  residual is *independent of `a`*, which is the whole content of the step.

Composing them gives `I(x) = φ(h)·[2 v φ(z) + h′(2Φ(z) − 1)]`, the Kac–Rice
integrand; the assembly itself is not done here (see `HANDOFF.md`).
-/
import NonmonicCubic.FoldedNormal
import NonmonicCubic.KacRice

namespace NonmonicCubic.Gaussian

open MeasureTheory Real
open NonmonicCubic.GaussianCubic

/-- **The Gaussian integral with a linear term.**  Mathlib has only the centred
`integral_gaussian`; completing the square and translating gives this. -/
theorem integral_exp_quadratic {W c d : ℝ} (hW : 0 < W) :
    ∫ a : ℝ, Real.exp (-(W * a ^ 2 + 2 * c * a + d) / 2)
      = Real.sqrt (2 * π / W) * Real.exp (-(d - c ^ 2 / W) / 2) := by
  have hW0 : W ≠ 0 := hW.ne'
  have key : ∀ a : ℝ, Real.exp (-(W * a ^ 2 + 2 * c * a + d) / 2)
      = Real.exp (-(d - c ^ 2 / W) / 2) * Real.exp (-(W / 2) * (a + c / W) ^ 2) := by
    intro a
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  simp_rw [key]
  rw [MeasureTheory.integral_const_mul]
  have hshift : (∫ a : ℝ, Real.exp (-(W / 2) * (a + c / W) ^ 2))
      = ∫ t : ℝ, Real.exp (-(W / 2) * t ^ 2) :=
    MeasureTheory.integral_add_right_eq_self (fun t => Real.exp (-(W / 2) * t ^ 2)) (c / W)
  rw [hshift, integral_gaussian, show π / (W / 2) = 2 * π / W by field_simp]
  ring

/-- The linear coefficient produced by the shear, `c(β) = x(2x⁴ + 6x² − βx² − 2β)`. -/
def shearLin (x β : ℝ) : ℝ := x * (2 * x ^ 4 + 6 * x ^ 2 - β * x ^ 2 - 2 * β)

/-- **The affine change of variables, algebraically.**  Substituting
`b = β − 2ax − 3x²` (the shear `(a,b) ↦ (a,B)`, Jacobian `1`) and completing the
square in `a` leaves a residual that does not involve `a`:

    a² + b² + A²  =  (x⁴+4x²+1)·(a + c(β)/(x⁴+4x²+1))²  +  (β − m)²/s²  +  h²

with `m = x²(x⁴+2x²+3)/q`, `s² = (x⁴+4x²+1)/q`, `h² = x⁶/q`. -/
theorem exponent_completeSquare (x a β : ℝ) :
    a ^ 2 + (β - 2 * a * x - 3 * x ^ 2) ^ 2
        + (x ^ 3 + a * x ^ 2 + (β - 2 * a * x - 3 * x ^ 2) * x) ^ 2
      = (x ^ 4 + 4 * x ^ 2 + 1)
          * (a + shearLin x β / (x ^ 4 + 4 * x ^ 2 + 1)) ^ 2
        + ((β - x ^ 2 * (x ^ 4 + 2 * x ^ 2 + 3) / qA x) ^ 2
            / ((x ^ 4 + 4 * x ^ 2 + 1) / qA x) + x ^ 6 / qA x) := by
  have hq : qA x ≠ 0 := qA_ne_zero x
  have hW : (x : ℝ) ^ 4 + 4 * x ^ 2 + 1 ≠ 0 := by positivity
  unfold shearLin qA
  field_simp
  ring


/-- The residual left after the `a`-integration: `(β − m)²/s² + h²`, independent
of `a`.  This is the exponent of the Gaussian in `β` that the shear produces. -/
noncomputable def resid (x β : ℝ) : ℝ :=
  (β - x ^ 2 * (x ^ 4 + 2 * x ^ 2 + 3) / qA x) ^ 2 / ((x ^ 4 + 4 * x ^ 2 + 1) / qA x)
    + x ^ 6 / qA x

/-- The sheared exponent written in the `W a² + 2ca + d` form that
`integral_exp_quadratic` and `integrable_exp_quadratic` expect. -/
theorem exponent_shear_expand (x a β : ℝ) :
    a ^ 2 + (β - 2 * a * x - 3 * x ^ 2) ^ 2
        + (x ^ 3 + a * x ^ 2 + (β - 2 * a * x - 3 * x ^ 2) * x) ^ 2
      = (x ^ 4 + 4 * x ^ 2 + 1) * a ^ 2 + 2 * shearLin x β * a
        + (shearLin x β ^ 2 / (x ^ 4 + 4 * x ^ 2 + 1) + resid x β) := by
  have hW0 : x ^ 4 + 4 * x ^ 2 + 1 ≠ 0 := by positivity
  have hq : qA x ≠ 0 := qA_ne_zero x
  rw [exponent_completeSquare x a β]
  unfold resid
  field_simp
  ring_nf

/-- **Integrability** of the Gaussian with a linear term. -/
theorem integrable_exp_quadratic {W c d : ℝ} (hW : 0 < W) :
    Integrable (fun a : ℝ => Real.exp (-(W * a ^ 2 + 2 * c * a + d) / 2)) := by
  have hW0 : W ≠ 0 := hW.ne'
  have hbase : Integrable (fun t : ℝ => Real.exp (-(W / 2) * t ^ 2)) :=
    integrable_exp_neg_mul_sq (by positivity)
  have hshift := hbase.comp_add_right (c / W)
  refine (hshift.const_mul (Real.exp (-(d - c ^ 2 / W) / 2))).congr
    (Filter.Eventually.of_forall fun a => ?_)
  simp only [← Real.exp_add]
  congr 1
  field_simp
  ring

/-- **The `a`-integral.**  At fixed `β`, integrating out `a` leaves a Gaussian in
`β` with the residual exponent, times the constant `√(2π/(x⁴+4x²+1))`.  This is
the affine change of variables carried out: the `a`-direction is gone. -/
theorem integral_a_exp (x β : ℝ) :
    ∫ a : ℝ, Real.exp (-(a ^ 2 + (β - 2 * a * x - 3 * x ^ 2) ^ 2
        + (x ^ 3 + a * x ^ 2 + (β - 2 * a * x - 3 * x ^ 2) * x) ^ 2) / 2)
      = Real.sqrt (2 * π / (x ^ 4 + 4 * x ^ 2 + 1)) * Real.exp (-resid x β / 2) := by
  have hW : (0 : ℝ) < x ^ 4 + 4 * x ^ 2 + 1 := by positivity
  have hW0 : x ^ 4 + 4 * x ^ 2 + 1 ≠ 0 := hW.ne'
  have hq : qA x ≠ 0 := qA_ne_zero x
  simp_rw [exponent_shear_expand x _ β]
  rw [integral_exp_quadratic hW]
  congr 2
  field_simp
  ring


/-- **The `β`-integral.**  Rescaling `β = m + σ t` turns the shifted Gaussian
weight into the standard one, so `FoldedNormal.integral_abs_scaled` applies:

    ∫ |β| e^{−(β−m)²/(2σ²)} dβ = σ√(2π)·[2σ φ(m/σ) + m(2Φ(m/σ) − 1)].

Together with `integral_a_exp` this is the whole inner integral. -/
theorem integral_abs_gaussian_shift (m σ : ℝ) (hσ : 0 < σ) :
    ∫ β : ℝ, |β| * Real.exp (-(β - m) ^ 2 / (2 * σ ^ 2))
      = σ * Real.sqrt (2 * π) * (2 * σ * φ (m / σ) + m * (2 * Φ (m / σ) - 1)) := by
  have hσ0 : σ ≠ 0 := hσ.ne'
  have hT : (∫ t : ℝ, |t + m| * Real.exp (-(t + m - m) ^ 2 / (2 * σ ^ 2)))
      = ∫ β : ℝ, |β| * Real.exp (-(β - m) ^ 2 / (2 * σ ^ 2)) :=
    MeasureTheory.integral_add_right_eq_self
      (fun β => |β| * Real.exp (-(β - m) ^ 2 / (2 * σ ^ 2))) m
  have hS := MeasureTheory.Measure.integral_comp_mul_left
      (fun t : ℝ => |t + m| * Real.exp (-(t + m - m) ^ 2 / (2 * σ ^ 2))) σ
  rw [hT] at hS
  have hpt : ∀ t : ℝ, |σ * t + m| * Real.exp (-(σ * t + m - m) ^ 2 / (2 * σ ^ 2))
      = Real.sqrt (2 * π) * (|m + σ * t| * φ t) := by
    intro t
    have e1 : σ * t + m - m = σ * t := by ring
    have e2 : -(σ * t) ^ 2 / (2 * σ ^ 2) = -t ^ 2 / 2 := by field_simp
    have e3 : |σ * t + m| = |m + σ * t| := by rw [add_comm]
    rw [e1, e2, e3]
    unfold φ
    field_simp
  simp_rw [hpt] at hS
  rw [MeasureTheory.integral_const_mul, integral_abs_scaled m σ hσ, smul_eq_mul,
    abs_of_pos (inv_pos.2 hσ)] at hS
  field_simp at hS
  simp only [neg_div]
  rw [← hS]
  ring


/-- Integrability in `a` of the sheared exponent, at fixed `β`. -/
theorem integrable_a_exp (x β : ℝ) :
    Integrable (fun a : ℝ => Real.exp (-(a ^ 2 + (β - 2 * a * x - 3 * x ^ 2) ^ 2
      + (x ^ 3 + a * x ^ 2 + (β - 2 * a * x - 3 * x ^ 2) * x) ^ 2) / 2)) := by
  have hW : (0 : ℝ) < x ^ 4 + 4 * x ^ 2 + 1 := by positivity
  simp_rw [exponent_shear_expand x _ β]
  exact integrable_exp_quadratic hW

end NonmonicCubic.Gaussian
