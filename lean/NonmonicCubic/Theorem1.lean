/-
# Theorem 1

> Let `(a,b,c)` be i.i.d. uniform on `[-1,1]`.  Then
> `P( x³ + a x² + b x + c has three real roots ) = 383/4860 + log 3 / 48`.

Formalized as a statement about the Lebesgue measure of the region of the cube
`[-1,1]³` on which the discriminant `Δ₃` is positive (`volume_T1Set`), together
with the probability restatement `theorem1_probability`.

The proof is the one in `reference/THEOREMS.md` ("Proof of Theorem 1"):

1. Slice by `a`.  For fixed `a ∈ [-1,1]` the slice is exactly the region
   between the two curves `cLo a` and `cHi a` over `b ∈ [-1, a²/3]`
   (`slice_eq`) — this uses the **never-clipped lemma** (`cHi_le_one`,
   `neg_one_le_cLo` in `Basic.lean`) to know the band never leaves the window
   `c ∈ [-1,1]`.
2. The band width is `(4/27)(a²-3b)^{3/2}` (identity S1), so the slice has area
   `(8/405)(a²+3)^{5/2}` (`integral_band_width`).
3. Integrate over `a ∈ [-1,1]` (`integral_p52_shift`) to get
   `766/1215 + log 3 / 6`, which is `8 ×` the probability.
-/
import NonmonicCubic.Integrals

namespace NonmonicCubic

open Real Set MeasureTheory intervalIntegral

/-- The real-rooted region of the cube `[-1,1]³` for the monic cubic
`x³ + a x² + b x + c`, coordinates `(a,b,c)`. -/
def T1Set : Set (ℝ × ℝ × ℝ) :=
  {p | p.1 ∈ Icc (-1 : ℝ) 1 ∧ p.2.1 ∈ Icc (-1 : ℝ) 1 ∧ p.2.2 ∈ Icc (-1 : ℝ) 1 ∧
    0 < Δ₃ p.1 p.2.1 p.2.2}

theorem continuous_Δ₃ : Continuous fun p : ℝ × ℝ × ℝ => Δ₃ p.1 p.2.1 p.2.2 := by
  unfold Δ₃; fun_prop

theorem measurableSet_T1Set : MeasurableSet T1Set := by
  have h : T1Set = ((Prod.fst ⁻¹' Icc (-1 : ℝ) 1)
      ∩ ((fun p : ℝ × ℝ × ℝ => p.2.1) ⁻¹' Icc (-1 : ℝ) 1)
      ∩ ((fun p : ℝ × ℝ × ℝ => p.2.2) ⁻¹' Icc (-1 : ℝ) 1))
      ∩ {p : ℝ × ℝ × ℝ | 0 < Δ₃ p.1 p.2.1 p.2.2} := by
    ext p; simp only [T1Set, mem_ofPred_eq, mem_inter_iff, mem_preimage]; tauto
  rw [h]
  exact (((measurable_fst measurableSet_Icc).inter
      ((measurable_fst.comp measurable_snd) measurableSet_Icc)).inter
      ((measurable_snd.comp measurable_snd) measurableSet_Icc)).inter
    (measurableSet_lt measurable_const continuous_Δ₃.measurable)

/-- **The slice.**  For `a ∈ [-1,1]` the `(b,c)`-slice of the real-rooted region
is exactly the region between the band edges over `b ∈ [-1, a²/3)`. -/
theorem slice_eq {a : ℝ} (ha : a ∈ Icc (-1 : ℝ) 1) :
    Prod.mk a ⁻¹' T1Set = regionBetween (cLo a) (cHi a) (Ico (-1) (a ^ 2 / 3)) := by
  obtain ⟨ha1, ha2⟩ := ha
  have hasq : a ^ 2 ≤ 1 := by nlinarith
  ext ⟨b, c⟩
  simp only [mem_preimage, T1Set, mem_ofPred_eq, regionBetween, mem_Ioo, mem_Ico, mem_Icc]
  constructor
  · rintro ⟨-, ⟨hb1, -⟩, -, hΔ⟩
    have hnn : 0 ≤ a ^ 2 - 3 * b := by
      by_contra hc
      rw [not_le] at hc
      exact absurd hΔ (not_lt.2 (Δ₃_neg_of_lt hc c).le)
    have hband := (Δ₃_pos_iff hnn c).1 hΔ
    have hlt : cLo a b < cHi a b := lt_trans hband.1 hband.2
    have hp : 0 < p32 (a ^ 2 - 3 * b) := by
      have := cHi_sub_cLo a b; linarith
    have hb2 : b < a ^ 2 / 3 := by
      rcases lt_or_eq_of_le hnn with h | h
      · linarith
      · exfalso; unfold p32 at hp; rw [← h] at hp; simp at hp
    exact ⟨⟨hb1, hb2⟩, hband⟩
  · rintro ⟨⟨hb1, hb2⟩, hband⟩
    have hnn : 0 ≤ a ^ 2 - 3 * b := by linarith
    refine ⟨⟨ha1, ha2⟩, ⟨hb1, by linarith⟩, ⟨?_, ?_⟩, (Δ₃_pos_iff hnn c).2 hband⟩
    · have := neg_one_le_cLo ha1 ha2 hb1 (by linarith)
      linarith [hband.1]
    · have := cHi_le_one ha1 ha2 hb1 (by linarith)
      linarith [hband.2]

theorem volume_slice {a : ℝ} (ha : a ∈ Icc (-1 : ℝ) 1) :
    volume (Prod.mk a ⁻¹' T1Set) = ENNReal.ofReal (8 / 405 * p52 (a ^ 2 + 3)) := by
  have hle : (-1 : ℝ) ≤ a ^ 2 / 3 := by nlinarith [sq_nonneg a]
  rw [slice_eq ha,
    show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
    volume_regionBetween_eq_integral
      ((continuous_cLo a).continuousOn.integrableOn_Icc.mono_set Ico_subset_Icc_self)
      ((continuous_cHi a).continuousOn.integrableOn_Icc.mono_set Ico_subset_Icc_self)
      measurableSet_Ico
      (fun b hb => cLo_le_cHi a b (by have := hb.2; linarith))]
  congr 1
  have hcongr : ∀ b : ℝ, (cHi a - cLo a) b = 4 / 27 * p32 (a ^ 2 - 3 * b) := by
    intro b; simpa using cHi_sub_cLo a b
  rw [setIntegral_congr_fun measurableSet_Ico (fun b _ => hcongr b),
    integral_Ico_eq_integral_Ioc, ← integral_of_le hle, integral_band_width]

/-- **Theorem 1, volume form.**  The real-rooted region of `[-1,1]³` has
Lebesgue measure `766/1215 + log 3 / 6`. -/
theorem volume_T1Set : volume T1Set = ENNReal.ofReal (766 / 1215 + Real.log 3 / 6) := by
  rw [show (volume : Measure (ℝ × ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
    Measure.prod_apply measurableSet_T1Set]
  have hfun : (fun a => (volume : Measure (ℝ × ℝ)) (Prod.mk a ⁻¹' T1Set))
      = (Icc (-1 : ℝ) 1).indicator
        (fun a => ENNReal.ofReal (8 / 405 * p52 (a ^ 2 + 3))) := by
    funext a
    by_cases ha : a ∈ Icc (-1 : ℝ) 1
    · rw [Set.indicator_of_mem ha, volume_slice ha]
    · rw [Set.indicator_of_notMem ha]
      have hempty : Prod.mk a ⁻¹' T1Set = ∅ := by
        ext ⟨b, c⟩
        simp only [mem_preimage, T1Set, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        exact fun h => absurd h ha
      rw [hempty, measure_empty]
  rw [hfun, lintegral_indicator measurableSet_Icc]
  have hcont : Continuous fun a : ℝ => 8 / 405 * p52 (a ^ 2 + 3) :=
    continuous_const.mul (continuous_p52.comp ((continuous_pow 2).add continuous_const))
  have hint : IntegrableOn (fun a : ℝ => 8 / 405 * p52 (a ^ 2 + 3)) (Icc (-1 : ℝ) 1) :=
    hcont.continuousOn.integrableOn_Icc
  have hnn : 0 ≤ᵐ[volume.restrict (Icc (-1 : ℝ) 1)]
      fun a : ℝ => 8 / 405 * p52 (a ^ 2 + 3) :=
    Filter.Eventually.of_forall fun a => by
      simp only [Pi.zero_apply]
      have : 0 ≤ p52 (a ^ 2 + 3) := by unfold p52; positivity
      linarith
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, ← integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    integral_p52_shift]

/-- **Theorem 1**, in exactly the shape of `reference/THEOREMS.md`:
the volume of `{Δ₃ > 0}` inside `[-1,1]³` is `8 × (383/4860 + log 3 / 48)`. -/
theorem theorem1 :
    volume {p : ℝ × ℝ × ℝ | p.1 ∈ Icc (-1 : ℝ) 1 ∧ p.2.1 ∈ Icc (-1 : ℝ) 1 ∧
      p.2.2 ∈ Icc (-1 : ℝ) 1 ∧ 0 < Δ₃ p.1 p.2.1 p.2.2}
      = ENNReal.ofReal ((383 / 4860 + Real.log 3 / 48) * 8) := by
  rw [show ((383 / 4860 + Real.log 3 / 48) * 8 : ℝ) = 766 / 1215 + Real.log 3 / 6 by ring]
  exact volume_T1Set

/-- The volume of the cube `[-1,1]³` is `8`. -/
theorem volume_cube3 :
    volume (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) = ENNReal.ofReal 8 := by
  rw [show (volume : Measure (ℝ × ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
    Measure.prod_prod,
    show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
    Measure.prod_prod, Real.volume_Icc]
  norm_num

/-- **Theorem 1, probability form.**  `P(three real roots) = 383/4860 + log 3 / 48`. -/
theorem theorem1_probability :
    (volume T1Set).toReal
      / (volume (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)).toReal
      = 383 / 4860 + Real.log 3 / 48 := by
  have hlog : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hnn : (0 : ℝ) ≤ 766 / 1215 + Real.log 3 / 6 := by linarith
  rw [volume_T1Set, volume_cube3, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 8),
    ENNReal.toReal_ofReal hnn]
  ring

end NonmonicCubic
