/-
# Step 2: the Tonelli swap, and the fibre of the Kac–Rice integrand

`AreaFormula.lean` (step 1) evaluates, for **fixed** `(a,b)`, the `x`-integral of
`|cub′| · u ∘ cub`.  `KacRice.lean` explains why the remaining inner `(a,b)`
integral is elementary.  What connects them is the swap of the `x` integral with
the `(a,b)` integral — step 2 of the route.  This file does that swap, with the
measurability side condition discharged, and evaluates the fibre.

Everything stays in `ℝ≥0∞`: the integrand is nonnegative, so `lintegral` needs
no integrability hypotheses anywhere (`lintegral_lintegral_swap` asks only for
`AEMeasurable`), which is much cheaper than carrying `Integrable` through a
product space.

The two results:

* `lintegral_kacRice_swap` — the swap itself;
* `lintegral_x_kacRice` — at fixed `(a,b)`,

      ∫⁻ x, kacRice a b x = φ(a)φ(b) · (1 + 2 ∫⁻_{Icc B A} φ)

  where `Icc B A` is the band of `AreaFormula.lintegral_cub`.  The bracket is
  `E[N | a, b]`: the `1` is the root every cubic has, and the band term is twice
  the probability that `−c` lands between the two critical values.

Composing the two gives `∫⁻ x, ∫⁻ (a,b), kacRice = E[N]`, which is the Kac–Rice
identity for this problem.  What is still missing before the 1-D formula is the
*evaluation* of the inner `(a,b)` integral at fixed `x` — its algebra is
`KacRice.lean` and its analysis needs `FoldedNormal.integral_abs_scaled` plus an
affine change of variables in `ℝ²`.
-/
import NonmonicCubic.AreaFormula
import NonmonicCubic.FoldedNormal

namespace NonmonicCubic.KacRiceIntegral

open MeasureTheory Set Filter
open scoped ENNReal
open NonmonicCubic.AreaFormula NonmonicCubic.Gaussian

/-- The Kac–Rice integrand for the monic Gaussian cubic:
`φ(a) φ(b) · |cub′ a b x| · φ(cub a b x)`, as an extended nonnegative real. -/
noncomputable def kacRice (a b x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (φ a * φ b * |dcub a b x| * φ (cub a b x))

theorem continuous_kacRiceReal :
    Continuous fun q : (ℝ × ℝ) × ℝ =>
      φ q.1.1 * φ q.1.2 * |dcub q.1.1 q.1.2 q.2| * φ (cub q.1.1 q.1.2 q.2) := by
  unfold cub dcub
  fun_prop

theorem measurable_kacRice :
    Measurable fun q : (ℝ × ℝ) × ℝ => kacRice q.1.1 q.1.2 q.2 :=
  ENNReal.measurable_ofReal.comp continuous_kacRiceReal.measurable

/-- **Step 2: the Tonelli swap.**  Nonnegativity means `lintegral_lintegral_swap`
needs only joint measurability — no integrability side condition. -/
theorem lintegral_kacRice_swap :
    ∫⁻ p : ℝ × ℝ, ∫⁻ x : ℝ, kacRice p.1 p.2 x
      = ∫⁻ x : ℝ, ∫⁻ p : ℝ × ℝ, kacRice p.1 p.2 x :=
  lintegral_lintegral_swap measurable_kacRice.aemeasurable

/-- `∫⁻ φ = 1`, in `ℝ≥0∞`. -/
theorem lintegral_ofReal_φ : ∫⁻ y : ℝ, ENNReal.ofReal (φ y) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal integrable_φ
    (Filter.Eventually.of_forall fun y => (φ_pos y).le), integral_φ, ENNReal.ofReal_one]

/-- **The fibre.**  At fixed `(a,b)`,

    ∫⁻ x, kacRice a b x = φ(a) φ(b) · (1 + 2 ∫⁻_{Icc B A} φ),

the bracket being `E[N | a, b]` by `AreaFormula.lintegral_cub`. -/
theorem lintegral_x_kacRice (a b : ℝ) :
    ∃ B A : ℝ, ∫⁻ x : ℝ, kacRice a b x
      = ENNReal.ofReal (φ a * φ b)
        * (1 + 2 * ∫⁻ y in Icc B A, ENNReal.ofReal (φ y)) := by
  obtain ⟨B, A, hBA⟩ := AreaFormula.lintegral_cub a b fun y => ENNReal.ofReal (φ y)
  refine ⟨B, A, ?_⟩
  have hpull : ∀ x : ℝ, kacRice a b x
      = ENNReal.ofReal (φ a * φ b)
        * (ENNReal.ofReal |dcub a b x| * ENNReal.ofReal (φ (cub a b x))) := by
    intro x
    unfold kacRice
    rw [← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_mul (mul_pos (φ_pos a) (φ_pos b)).le]
    ring_nf
  simp_rw [hpull]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hBA, lintegral_ofReal_φ]

end NonmonicCubic.KacRiceIntegral
