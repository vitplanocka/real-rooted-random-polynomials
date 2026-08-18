/-
# The band is exactly the three-real-roots region

`AreaFormula.lintegral_cub` produces the band `Icc (cub x₂) (cub x₁)` between the
two critical values.  To read that as "the cubic has three real roots" one needs

    x³ + a x² + b x + c has three distinct real roots  ↔  cub x₂ < −c < cub x₁ ,

which is what this file proves.  The route is the discriminant, avoiding any
appeal to Rolle's theorem: with `f′ = 3(x−x₁)(x−x₂)`,

    f(x₁)·f(x₂) = −Δ₃/27          (`critValue_prod`)
    f(x₁) − f(x₂) = (x₂−x₁)³/2    (`critValue_sub`)

so `Δ₃ > 0 ↔ f(x₁)f(x₂) < 0 ↔ f(x₂) < 0 < f(x₁)` (the second step using
`f(x₁) > f(x₂)`), and `Δ₃ > 0 ↔ three distinct real roots` is
`DiscriminantRootCount.Δ₃_pos_iff_three_distinct_real_roots`.
-/
import NonmonicCubic.AreaFormula
import NonmonicCubic.DiscriminantRootCount

namespace NonmonicCubic.AreaFormula

open Set MeasureTheory
open scoped ENNReal

/-- The two coefficient relations implied by `f′ = 3(x−x₁)(x−x₂)`. -/
theorem coeff_of_factorisation {a b x₁ x₂ : ℝ}
    (hfac : ∀ x, dcub a b x = 3 * (x - x₁) * (x - x₂)) :
    2 * a = -3 * (x₁ + x₂) ∧ b = 3 * (x₁ * x₂) := by
  have h0 := hfac 0
  have h1 := hfac 1
  unfold dcub at h0 h1
  constructor <;> nlinarith [h0, h1]

/-- **`f(x₁)·f(x₂) = −Δ₃/27`.** -/
theorem critValue_prod {a b x₁ x₂ c : ℝ} (ha : 2 * a = -3 * (x₁ + x₂))
    (hb : b = 3 * (x₁ * x₂)) :
    (cub a b x₁ + c) * (cub a b x₂ + c) = -Δ₃ a b c / 27 := by
  have ha' : a = -3 * (x₁ + x₂) / 2 := by linarith
  unfold cub Δ₃
  rw [ha', hb]
  ring

/-- **`f(x₁) − f(x₂) = (x₂−x₁)³/2`**, so the local max exceeds the local min. -/
theorem critValue_sub {a b x₁ x₂ : ℝ} (ha : 2 * a = -3 * (x₁ + x₂))
    (hb : b = 3 * (x₁ * x₂)) :
    cub a b x₁ - cub a b x₂ = (x₂ - x₁) ^ 3 / 2 := by
  have ha' : a = -3 * (x₁ + x₂) / 2 := by linarith
  unfold cub
  rw [ha', hb]
  ring

/-- **The band is the three-real-roots region.** -/
theorem three_distinct_iff_mem_band {a b c x₁ x₂ : ℝ} (hlt : x₁ < x₂)
    (hfac : ∀ x, dcub a b x = 3 * (x - x₁) * (x - x₂)) :
    HasThreeDistinctRealRoots 1 a b c ↔ cub a b x₂ < -c ∧ -c < cub a b x₁ := by
  obtain ⟨ha, hb⟩ := coeff_of_factorisation hfac
  have hprod := critValue_prod (c := c) ha hb
  have hsub := critValue_sub (a := a) (b := b) ha hb
  have hgt : cub a b x₂ < cub a b x₁ := by
    have h3 : (0 : ℝ) < (x₂ - x₁) ^ 3 / 2 := by
      have hx : (0 : ℝ) < x₂ - x₁ := by linarith
      positivity
    linarith
  rw [← Δ₃_pos_iff_three_distinct_real_roots]
  constructor
  · intro hΔ
    have hneg : (cub a b x₁ + c) * (cub a b x₂ + c) < 0 := by
      rw [hprod]; linarith
    rcases mul_neg_iff.1 hneg with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by linarith, by linarith⟩
    · linarith
  · rintro ⟨h1, h2⟩
    have hneg : (cub a b x₁ + c) * (cub a b x₂ + c) < 0 :=
      mul_neg_of_pos_of_neg (by linarith) (by linarith)
    rw [hprod] at hneg
    linarith


/-! ## The area formula, stated by root count

`lintegral_cub` produces a band; `three_distinct_iff_mem_band` identifies it.
This restates the area formula with the three-real-roots set in place of the
band, which is the form the probabilistic assembly needs. -/

/-- When `a² ≤ 3b` the cubic never has three distinct real roots: the
completed-square identity forces `Δ₃ ≤ 0`. -/
theorem not_three_of_le {a b c : ℝ} (hab : a ^ 2 ≤ 3 * b) :
    ¬ HasThreeDistinctRealRoots 1 a b c := by
  rw [← Δ₃_pos_iff_three_distinct_real_roots]
  have hcs : -27 * Δ₃ a b c = (27 * c - 9 * a * b + 2 * a ^ 3) ^ 2 - 4 * (a ^ 2 - 3 * b) ^ 3 := by
    unfold Δ₃; ring
  have h1 : (a ^ 2 - 3 * b) ^ 3 ≤ 0 := by nlinarith [sq_nonneg (a ^ 2 - 3 * b)]
  have h2 : (0 : ℝ) ≤ (27 * c - 9 * a * b + 2 * a ^ 3) ^ 2 := sq_nonneg _
  intro h
  nlinarith [hcs, h1, h2, h]

/-- The strict form of the factorisation, when `3b < a²`. -/
theorem exists_factorisation_dcub_lt (a b : ℝ) (hab : 3 * b < a ^ 2) :
    ∃ x₁ x₂ : ℝ, x₁ < x₂ ∧ ∀ x, dcub a b x = 3 * (x - x₁) * (x - x₂) := by
  set s := Real.sqrt (a ^ 2 - 3 * b) with hs
  have hspos : 0 < s := Real.sqrt_pos.2 (by linarith)
  have hs2 : s ^ 2 = a ^ 2 - 3 * b := Real.sq_sqrt (by linarith)
  refine ⟨(-a - s) / 3, (-a + s) / 3, by linarith, fun x => ?_⟩
  unfold dcub
  field_simp
  nlinarith [hs2]

/-- **The area formula by root count.** -/
theorem lintegral_cub_roots (a b : ℝ) (u : ℝ → ℝ≥0∞) :
    ∫⁻ x, ENNReal.ofReal (|dcub a b x|) * u (cub a b x)
      = (∫⁻ y, u y)
        + 2 * ∫⁻ y in {y : ℝ | HasThreeDistinctRealRoots 1 a b (-y)}, u y := by
  rcases le_or_gt (a ^ 2) (3 * b) with hab | hab
  · have hempty : {y : ℝ | HasThreeDistinctRealRoots 1 a b (-y)} = ∅ := by
      ext y; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact not_three_of_le hab
    rw [lintegral_cub_of_le a b hab u, hempty]
    simp
  · obtain ⟨x₁, x₂, hlt, hfac⟩ := exists_factorisation_dcub_lt a b hab
    have hset : {y : ℝ | HasThreeDistinctRealRoots 1 a b (-y)}
        = Set.Ioo (cub a b x₂) (cub a b x₁) := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_Ioo]
      rw [three_distinct_iff_mem_band hlt hfac, neg_neg]
    rw [lintegral_cub_eq hfac hlt.le u, hset,
      MeasureTheory.setLIntegral_congr Ioo_ae_eq_Icc]

end NonmonicCubic.AreaFormula
