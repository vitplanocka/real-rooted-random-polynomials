/-
# Step 5: assembling the Kac–Rice integrand

Steps 3a–3d supply every factor of the inner integral

    I(x) = ∫∫ φ(a) φ(b) φ(A) |B| da db,   A = x³+ax²+bx,  B = 3x²+2ax+b.

This file puts them together.  The route is the one of `AffineChange.lean`:
shear `b ↦ β = B` (a translation at fixed `a`), swap the order, integrate `a`
(`integral_a_exp`), then integrate `β` (`integral_abs_gaussian_shift`).  The swap
is free because everything is nonnegative, so the whole chain runs in `ℝ≥0∞`.

The constants that come out are `√(2π/W)`, `1/√(2π)³` and `s√(2π)`, and
`const_arith` is the one-line fact that they collapse to `1/(√(2π)·√q)` — i.e. to
`φ(h)/√q`, the Kac–Rice normalisation.  The last step, `kacRice_normalisation`,
rewrites `φ(h)/√q · [2s φ(z) + m(2Φ(z)−1)]` into the familiar
`φ(h) · [2v φ(z) + h′(2Φ(z)−1)]` using `s = v√q` and `m = h′√q`
(`KacRice.varB_eq_v_sq_mul`, `KacRice.mB_eq_hA'_mul_sqrt`).
-/
import NonmonicCubic.AffineChange

namespace NonmonicCubic.Gaussian

open MeasureTheory Real
open scoped ENNReal
open NonmonicCubic.GaussianCubic

/-! ## The mean, the standard deviation and their ratio -/

/-- `m(x) = x²(x⁴+2x²+3)/q`, the conditional mean of `f′(x)`. -/
noncomputable def mB (x : ℝ) : ℝ := x ^ 2 * (x ^ 4 + 2 * x ^ 2 + 3) / qA x

/-- `s(x) = √((x⁴+4x²+1)/q)`, its conditional standard deviation. -/
noncomputable def sB (x : ℝ) : ℝ := Real.sqrt ((x ^ 4 + 4 * x ^ 2 + 1) / qA x)

/-- `z(x) = m/s`, the argument of the normal CDF in the Kac–Rice integrand. -/
noncomputable def zB (x : ℝ) : ℝ := mB x / sB x

theorem sB_pos (x : ℝ) : 0 < sB x := by
  unfold sB
  exact Real.sqrt_pos.2 (by have := qA_pos x; positivity)

theorem sB_sq (x : ℝ) : sB x ^ 2 = (x ^ 4 + 4 * x ^ 2 + 1) / qA x := by
  unfold sB
  exact Real.sq_sqrt (by have := qA_pos x; positivity)

/-- `s·√q = √(x⁴+4x²+1)`: the one square-root identity the assembly needs. -/
theorem sB_mul_sqrt_qA (x : ℝ) :
    sB x * Real.sqrt (qA x) = Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) := by
  have hq : (0 : ℝ) < qA x := qA_pos x
  unfold sB
  rw [← Real.sqrt_mul (by positivity)]
  congr 1
  field_simp

/-! ## The pointwise density -/

/-- Three standard normal densities multiply to a single exponential:
`φ(a)φ(b)φ(A) = exp(−(a²+b²+A²)/2)/√(2π)³`. -/
theorem three_φ (a b A : ℝ) :
    φ a * φ b * φ A = Real.exp (-(a ^ 2 + b ^ 2 + A ^ 2) / 2) / Real.sqrt (2 * π) ^ 3 := by
  have h : Real.exp (-(a ^ 2 + b ^ 2 + A ^ 2) / 2)
      = Real.exp (-a ^ 2 / 2) * Real.exp (-b ^ 2 / 2) * Real.exp (-A ^ 2 / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  unfold φ
  rw [h]
  ring

/-! ## The constants collapse -/

/-- **The Kac–Rice normalisation.**  The three constants produced by the chain —
`√(2π/W)` from the `a`-integral, `1/√(2π)³` from the three densities, and
`s√(2π)` from the `β`-integral — collapse to `1/(√(2π)·√q)`, which is exactly
`φ(h)/√q` once the `exp(−h²/2)` is put back. -/
theorem const_arith (x : ℝ) :
    Real.sqrt (2 * π / (x ^ 4 + 4 * x ^ 2 + 1)) / Real.sqrt (2 * π) ^ 3
        * (sB x * Real.sqrt (2 * π))
      = 1 / (Real.sqrt (2 * π) * Real.sqrt (qA x)) := by
  have hP : (0 : ℝ) < Real.sqrt (2 * π) := Real.sqrt_pos.2 (by positivity)
  have hq : (0 : ℝ) < Real.sqrt (qA x) := Real.sqrt_pos.2 (qA_pos x)
  have h1 : Real.sqrt (2 * π / (x ^ 4 + 4 * x ^ 2 + 1))
      * Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) = Real.sqrt (2 * π) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  have key : Real.sqrt (2 * π / (x ^ 4 + 4 * x ^ 2 + 1)) * (sB x * Real.sqrt (qA x))
      = Real.sqrt (2 * π) := by rw [sB_mul_sqrt_qA x]; exact h1
  rw [div_mul_eq_mul_div, div_eq_div_iff (by positivity) (by positivity)]
  linear_combination Real.sqrt (2 * π) ^ 2 * key

/-! ## From `(m, s)` to `(h′, v)` -/

/-- `h²  = x⁶/q`, the residual exponent of `KacRice.resid_eq_hA_sq`. -/
theorem hA_sq (x : ℝ) : hA x ^ 2 = x ^ 6 / qA x := by
  unfold hA
  rw [div_pow, Real.sq_sqrt (qA_pos x).le]
  ring

/-- **`s/√q = v`.**  The one piece of real content in the normalisation:
`v = √(x⁴+4x²+1)/q` is `s` divided by `√q`. -/
theorem sB_div_sqrt_qA (x : ℝ) :
    sB x / Real.sqrt (qA x) = Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) / qA x := by
  have hq : (0 : ℝ) < qA x := qA_pos x
  have hsq : (0 : ℝ) < Real.sqrt (qA x) := Real.sqrt_pos.2 hq
  have h : Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) / qA x
      = sB x * Real.sqrt (qA x) / (Real.sqrt (qA x) * Real.sqrt (qA x)) := by
    rw [sB_mul_sqrt_qA x, Real.mul_self_sqrt hq.le]
  rw [h, mul_div_mul_right _ _ hsq.ne']

/-- **`m/√q = h′`.**  Immediate: `m = x²(x⁴+2x²+3)/q`. -/
theorem mB_div_sqrt_qA (x : ℝ) :
    mB x / Real.sqrt (qA x)
      = x ^ 2 * (x ^ 4 + 2 * x ^ 2 + 3) / (qA x * Real.sqrt (qA x)) := by
  unfold mB
  rw [div_div]

/-- Distributing the `1/√q` across the bracket — pure algebra, `√q` an atom. -/
theorem kacRice_normalisation (x : ℝ) :
    φ (hA x) / Real.sqrt (qA x) * (2 * sB x * φ (zB x) + mB x * (2 * Φ (zB x) - 1))
      = φ (hA x) * (2 * (sB x / Real.sqrt (qA x)) * φ (zB x)
          + mB x / Real.sqrt (qA x) * (2 * Φ (zB x) - 1)) := by
  have hsq : (0 : ℝ) < Real.sqrt (qA x) := Real.sqrt_pos.2 (qA_pos x)
  field_simp

/-- **The Kac–Rice integrand in its usual form.**  Combining the three previous
lemmas, `φ(h)/√q · [2 s φ(z) + m(2Φ(z)−1)]` is

    φ(h) · [2 v φ(z) + h′ (2Φ(z) − 1)],

with `v = √(x⁴+4x²+1)/q` and `h′ = x²(x⁴+2x²+3)/(q√q)` exactly as in
`GaussianCubic` (`v_sq_eq`, `hasDerivAt_hA`). -/
theorem kacRice_integrand (x : ℝ) :
    φ (hA x) / Real.sqrt (qA x) * (2 * sB x * φ (zB x) + mB x * (2 * Φ (zB x) - 1))
      = φ (hA x) * (2 * (Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) / qA x) * φ (zB x)
          + x ^ 2 * (x ^ 4 + 2 * x ^ 2 + 3) / (qA x * Real.sqrt (qA x))
            * (2 * Φ (zB x) - 1)) := by
  rw [kacRice_normalisation x, sB_div_sqrt_qA x, mB_div_sqrt_qA x]


/-! ## The `β`-integral evaluated

`AffineChange.integral_a_exp` leaves `√(2π/W)·exp(−resid(β)/2)`.  Splitting
`resid` and applying `integral_abs_gaussian_shift` finishes the inner integral. -/

/-- `resid` in the `(m, s, h)` form. -/
theorem resid_eq (x β : ℝ) : resid x β = (β - mB x) ^ 2 / sB x ^ 2 + hA x ^ 2 := by
  rw [sB_sq, hA_sq]; rfl

/-- **The inner integral, evaluated.**  Everything after the `a`-integration:

    ∫ |β|/√(2π)³ · √(2π/W) · exp(−resid(β)/2) dβ
      = φ(h)/√q · [2 s φ(z) + m (2Φ(z) − 1)].

Combined with `kacRice_integrand` this is `φ(h)·[2vφ(z) + h′(2Φ(z)−1)]`, the
Kac–Rice integrand. -/
theorem beta_integral_eq (x : ℝ) :
    ∫ β : ℝ, |β| / Real.sqrt (2 * π) ^ 3
        * (Real.sqrt (2 * π / (x ^ 4 + 4 * x ^ 2 + 1)) * Real.exp (-resid x β / 2))
      = φ (hA x) / Real.sqrt (qA x)
        * (2 * sB x * φ (zB x) + mB x * (2 * Φ (zB x) - 1)) := by
  have hP : (0 : ℝ) < Real.sqrt (2 * π) := Real.sqrt_pos.2 (by positivity)
  have hR : (0 : ℝ) < Real.sqrt (qA x) := Real.sqrt_pos.2 (qA_pos x)
  have hs : (0 : ℝ) < sB x := sB_pos x
  have hca := const_arith x
  set C : ℝ := Real.sqrt (2 * π / (x ^ 4 + 4 * x ^ 2 + 1)) * Real.exp (-hA x ^ 2 / 2)
      / Real.sqrt (2 * π) ^ 3 with hC
  have hpt : ∀ β : ℝ, |β| / Real.sqrt (2 * π) ^ 3
      * (Real.sqrt (2 * π / (x ^ 4 + 4 * x ^ 2 + 1)) * Real.exp (-resid x β / 2))
      = C * (|β| * Real.exp (-(β - mB x) ^ 2 / (2 * sB x ^ 2))) := by
    intro β
    rw [resid_eq, show -((β - mB x) ^ 2 / sB x ^ 2 + hA x ^ 2) / 2
        = -hA x ^ 2 / 2 + -(β - mB x) ^ 2 / (2 * sB x ^ 2) by field_simp; ring,
      Real.exp_add, hC]
    ring
  simp_rw [hpt]
  rw [MeasureTheory.integral_const_mul, integral_abs_gaussian_shift (mB x) (sB x) hs]
  have harith : C * (sB x * Real.sqrt (2 * π)) = φ (hA x) / Real.sqrt (qA x) := by
    have hφ : φ (hA x) = Real.exp (-hA x ^ 2 / 2) / Real.sqrt (2 * π) := rfl
    rw [hC, hφ, show Real.sqrt (2 * π / (x ^ 4 + 4 * x ^ 2 + 1)) * Real.exp (-hA x ^ 2 / 2)
          / Real.sqrt (2 * π) ^ 3 * (sB x * Real.sqrt (2 * π))
        = Real.exp (-hA x ^ 2 / 2)
          * (Real.sqrt (2 * π / (x ^ 4 + 4 * x ^ 2 + 1)) / Real.sqrt (2 * π) ^ 3
             * (sB x * Real.sqrt (2 * π))) from by ring, hca]
    ring
  simp only [zB]
  rw [← harith]
  ring


/-! ## The inner integral, assembled

Stated with the `β`-integral outermost — i.e. *after* the shear — so that the
whole chain is evaluation and no Fubini or integrability side condition is
needed.  Connecting this to `∫⁻` over `ℝ²` of the original `(a,b)` integrand is
the shear (`lintegral_add_right_eq_self`) plus the swap
(`lintegral_lintegral_swap`); see `HANDOFF.md`. -/

/-- **The inner integral of the Kac–Rice route, assembled.**

    ∫∫ φ(a) φ(β−2ax−3x²) |β| φ(x³+ax²+(β−2ax−3x²)x) da dβ
      = φ(h)/√q · [2 s φ(z) + m (2Φ(z) − 1)]

— the `a`-integral by `AffineChange.integral_a_exp`, the `β`-integral by
`beta_integral_eq`. -/
theorem inner_iterated_eq (x : ℝ) :
    ∫ β : ℝ, ∫ a : ℝ, φ a * φ (β - 2 * a * x - 3 * x ^ 2) * |β|
        * φ (x ^ 3 + a * x ^ 2 + (β - 2 * a * x - 3 * x ^ 2) * x)
      = φ (hA x) / Real.sqrt (qA x)
        * (2 * sB x * φ (zB x) + mB x * (2 * Φ (zB x) - 1)) := by
  have hinner : ∀ β : ℝ, (∫ a : ℝ, φ a * φ (β - 2 * a * x - 3 * x ^ 2) * |β|
      * φ (x ^ 3 + a * x ^ 2 + (β - 2 * a * x - 3 * x ^ 2) * x))
      = |β| / Real.sqrt (2 * π) ^ 3
        * (Real.sqrt (2 * π / (x ^ 4 + 4 * x ^ 2 + 1)) * Real.exp (-resid x β / 2)) := by
    intro β
    have hpt : ∀ a : ℝ, φ a * φ (β - 2 * a * x - 3 * x ^ 2) * |β|
        * φ (x ^ 3 + a * x ^ 2 + (β - 2 * a * x - 3 * x ^ 2) * x)
        = |β| / Real.sqrt (2 * π) ^ 3
          * Real.exp (-(a ^ 2 + (β - 2 * a * x - 3 * x ^ 2) ^ 2
              + (x ^ 3 + a * x ^ 2 + (β - 2 * a * x - 3 * x ^ 2) * x) ^ 2) / 2) := by
      intro a
      rw [show φ a * φ (β - 2 * a * x - 3 * x ^ 2) * |β|
            * φ (x ^ 3 + a * x ^ 2 + (β - 2 * a * x - 3 * x ^ 2) * x)
          = φ a * φ (β - 2 * a * x - 3 * x ^ 2)
              * φ (x ^ 3 + a * x ^ 2 + (β - 2 * a * x - 3 * x ^ 2) * x) * |β| from by ring,
        three_φ]
      ring
    simp_rw [hpt]
    rw [MeasureTheory.integral_const_mul, integral_a_exp]
  simp_rw [hinner]
  exact beta_integral_eq x

/-- **The Kac–Rice integrand for the monic Gaussian cubic, proved.**

    ∫∫ φ(a) φ(b) |B| φ(A) = φ(h) · [2 v φ(z) + h′ (2Φ(z) − 1)]

(after the shear `b = β − 2ax − 3x²`, so `B = β`), with
`v = √(x⁴+4x²+1)/q` and `h′ = x²(x⁴+2x²+3)/(q√q)` as in `GaussianCubic`.
This is the Kac–Rice formula for this problem, obtained from the definition of
the Gaussian measure — no Rice's formula, no level-crossing theory. -/
theorem inner_iterated_kacRice (x : ℝ) :
    ∫ β : ℝ, ∫ a : ℝ, φ a * φ (β - 2 * a * x - 3 * x ^ 2) * |β|
        * φ (x ^ 3 + a * x ^ 2 + (β - 2 * a * x - 3 * x ^ 2) * x)
      = φ (hA x) * (2 * (Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) / qA x) * φ (zB x)
          + x ^ 2 * (x ^ 4 + 2 * x ^ 2 + 3) / (qA x * Real.sqrt (qA x))
            * (2 * Φ (zB x) - 1)) := by
  rw [inner_iterated_eq x, kacRice_integrand x]


/-! ## 5c: the shear and the Fubini swap

Restating `inner_iterated_kacRice` over `ℝ²` in the original `(a,b)` variables.
The shear `b = β − 2ax − 3x²` is a translation at fixed `a`
(`lintegral_add_right_eq_self`); the reorder is `lintegral_lintegral_swap`, free
because the integrand is nonnegative.  The two descents from `ℝ≥0∞` to Bochner
have 1-D integrability obligations only. -/

/-- The integrand after the shear. -/
noncomputable def shearInt (x a β : ℝ) : ℝ :=
  φ a * φ (β - 2 * a * x - 3 * x ^ 2) * |β|
    * φ (x ^ 3 + a * x ^ 2 + (β - 2 * a * x - 3 * x ^ 2) * x)

theorem shearInt_nonneg (x a β : ℝ) : 0 ≤ shearInt x a β := by
  unfold shearInt
  exact mul_nonneg (mul_nonneg (mul_nonneg (φ_pos a).le
    (φ_pos (β - 2 * a * x - 3 * x ^ 2)).le) (abs_nonneg β))
    (φ_pos (x ^ 3 + a * x ^ 2 + (β - 2 * a * x - 3 * x ^ 2) * x)).le

theorem continuous_shearInt (x : ℝ) : Continuous fun p : ℝ × ℝ => shearInt x p.1 p.2 := by
  unfold shearInt; fun_prop

theorem shearInt_eq (x a β : ℝ) :
    shearInt x a β = |β| / Real.sqrt (2 * π) ^ 3
      * Real.exp (-(a ^ 2 + (β - 2 * a * x - 3 * x ^ 2) ^ 2
        + (x ^ 3 + a * x ^ 2 + (β - 2 * a * x - 3 * x ^ 2) * x) ^ 2) / 2) := by
  unfold shearInt
  rw [show φ a * φ (β - 2 * a * x - 3 * x ^ 2) * |β|
        * φ (x ^ 3 + a * x ^ 2 + (β - 2 * a * x - 3 * x ^ 2) * x)
      = φ a * φ (β - 2 * a * x - 3 * x ^ 2)
        * φ (x ^ 3 + a * x ^ 2 + (β - 2 * a * x - 3 * x ^ 2) * x) * |β| from by ring,
    three_φ]
  ring

theorem integrable_shearInt_a (x β : ℝ) : Integrable fun a : ℝ => shearInt x a β := by
  simp_rw [shearInt_eq]
  exact (integrable_a_exp x β).const_mul _

theorem integral_a_shearInt (x β : ℝ) :
    ∫ a : ℝ, shearInt x a β = |β| / Real.sqrt (2 * π) ^ 3
      * (Real.sqrt (2 * π / (x ^ 4 + 4 * x ^ 2 + 1)) * Real.exp (-resid x β / 2)) := by
  simp_rw [shearInt_eq]
  rw [MeasureTheory.integral_const_mul, integral_a_exp]

/-- Integrability of `|β|·exp(−(β−m)²/(2σ²))`, by domination with
`(|β−m| + |m|)·exp(−(β−m)²/(2σ²))`. -/
theorem integrable_abs_gaussian_shift (m σ : ℝ) (hσ : 0 < σ) :
    Integrable fun β : ℝ => |β| * Real.exp (-(β - m) ^ 2 / (2 * σ ^ 2)) := by
  have hcpos : (0 : ℝ) < 1 / (2 * σ ^ 2) := by positivity
  have h1 : Integrable fun u : ℝ => |u| * Real.exp (-(1 / (2 * σ ^ 2)) * u ^ 2) := by
    refine ((integrable_mul_exp_neg_mul_sq hcpos).abs).congr
      (Filter.Eventually.of_forall fun u => ?_)
    simp only [abs_mul, abs_of_pos (Real.exp_pos (-(1 / (2 * σ ^ 2)) * u ^ 2))]
  have h2 : Integrable fun u : ℝ => |m| * Real.exp (-(1 / (2 * σ ^ 2)) * u ^ 2) :=
    (integrable_exp_neg_mul_sq hcpos).const_mul |m|
  refine Integrable.mono' ((h1.add h2).comp_add_right (-m))
    (by fun_prop) (Filter.Eventually.of_forall fun β => ?_)
  have hexp : Real.exp (-(β - m) ^ 2 / (2 * σ ^ 2))
      = Real.exp (-(1 / (2 * σ ^ 2)) * (β + -m) ^ 2) := by
    congr 1; field_simp; ring
  have habs : |β| ≤ |β + -m| + |m| := by
    have h : ‖β + -m + m‖ ≤ ‖β + -m‖ + ‖m‖ := norm_add_le _ _
    simpa [Real.norm_eq_abs] using h
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hexp]
  have hmul := mul_le_mul_of_nonneg_right habs
    (Real.exp_pos (-(1 / (2 * σ ^ 2)) * (β + -m) ^ 2)).le
  simp only [Pi.add_apply]
  linarith [hmul]

theorem beta_integrand_eq (x β : ℝ) :
    |β| / Real.sqrt (2 * π) ^ 3
        * (Real.sqrt (2 * π / (x ^ 4 + 4 * x ^ 2 + 1)) * Real.exp (-resid x β / 2))
      = Real.sqrt (2 * π / (x ^ 4 + 4 * x ^ 2 + 1)) * Real.exp (-hA x ^ 2 / 2)
          / Real.sqrt (2 * π) ^ 3
        * (|β| * Real.exp (-(β - mB x) ^ 2 / (2 * sB x ^ 2))) := by
  have hs : (0 : ℝ) < sB x := sB_pos x
  rw [resid_eq, show -((β - mB x) ^ 2 / sB x ^ 2 + hA x ^ 2) / 2
      = -hA x ^ 2 / 2 + -(β - mB x) ^ 2 / (2 * sB x ^ 2) by field_simp; ring, Real.exp_add]
  ring

theorem beta_integrand_nonneg (x β : ℝ) :
    0 ≤ |β| / Real.sqrt (2 * π) ^ 3
      * (Real.sqrt (2 * π / (x ^ 4 + 4 * x ^ 2 + 1)) * Real.exp (-resid x β / 2)) := by
  have hP : (0 : ℝ) < Real.sqrt (2 * π) := Real.sqrt_pos.2 (by positivity)
  positivity

theorem integrable_beta_integrand (x : ℝ) :
    Integrable fun β : ℝ => |β| / Real.sqrt (2 * π) ^ 3
      * (Real.sqrt (2 * π / (x ^ 4 + 4 * x ^ 2 + 1)) * Real.exp (-resid x β / 2)) := by
  simp_rw [beta_integrand_eq]
  exact (integrable_abs_gaussian_shift (mB x) (sB x) (sB_pos x)).const_mul _

/-- **The shear**, at fixed `a`: a translation in `b`. -/
theorem lintegral_b_shear (x a : ℝ) :
    ∫⁻ b : ℝ, ENNReal.ofReal (φ a * φ b * |3 * x ^ 2 + 2 * a * x + b|
        * φ (x ^ 3 + a * x ^ 2 + b * x))
      = ∫⁻ β : ℝ, ENNReal.ofReal (shearInt x a β) := by
  have h := MeasureTheory.lintegral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun b : ℝ => ENNReal.ofReal (φ a * φ b * |3 * x ^ 2 + 2 * a * x + b|
      * φ (x ^ 3 + a * x ^ 2 + b * x))) (-(2 * a * x + 3 * x ^ 2))
  rw [← h]
  refine lintegral_congr fun β => ?_
  have e1 : β + -(2 * a * x + 3 * x ^ 2) = β - 2 * a * x - 3 * x ^ 2 := by ring
  have e2 : 3 * x ^ 2 + 2 * a * x + (β - 2 * a * x - 3 * x ^ 2) = β := by ring
  simp only [shearInt, e1, e2]

/-- **5c.**  `inner_iterated_kacRice` restated over `ℝ²` in the original `(a,b)`
variables: the Kac–Rice identity for the monic Gaussian cubic. -/
theorem inner_lintegral_eq (x : ℝ) :
    ∫⁻ a : ℝ, ∫⁻ b : ℝ, ENNReal.ofReal (φ a * φ b * |3 * x ^ 2 + 2 * a * x + b|
        * φ (x ^ 3 + a * x ^ 2 + b * x))
      = ENNReal.ofReal (φ (hA x) * (2 * (Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) / qA x) * φ (zB x)
          + x ^ 2 * (x ^ 4 + 2 * x ^ 2 + 3) / (qA x * Real.sqrt (qA x))
            * (2 * Φ (zB x) - 1))) := by
  have hmeas : AEMeasurable (Function.uncurry fun a β : ℝ => ENNReal.ofReal (shearInt x a β))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    (ENNReal.measurable_ofReal.comp (continuous_shearInt x).measurable).aemeasurable
  simp_rw [lintegral_b_shear x]
  rw [MeasureTheory.lintegral_lintegral_swap hmeas]
  have step3 : ∀ β : ℝ, (∫⁻ a : ℝ, ENNReal.ofReal (shearInt x a β))
      = ENNReal.ofReal (|β| / Real.sqrt (2 * π) ^ 3
          * (Real.sqrt (2 * π / (x ^ 4 + 4 * x ^ 2 + 1)) * Real.exp (-resid x β / 2))) := by
    intro β
    rw [← integral_a_shearInt x β]
    exact (ofReal_integral_eq_lintegral_ofReal (integrable_shearInt_a x β)
      (Filter.Eventually.of_forall fun a => shearInt_nonneg x a β)).symm
  simp_rw [step3]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_beta_integrand x)
    (Filter.Eventually.of_forall fun β => beta_integrand_nonneg x β)]
  rw [beta_integral_eq x, kacRice_integrand x]

end NonmonicCubic.Gaussian
