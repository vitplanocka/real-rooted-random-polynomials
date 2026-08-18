/-
# Theorem 4 — the proof

`P( a x³ + b x² + c x + d has three real roots ) = 719/2880 − ln 2 / 3` for
`(a,b,c,d)` i.i.d. uniform on `[0,1]`.

## Structure

1. **The cone decomposition on the positive orthant.**  `Δ₄` is homogeneous of
   degree 4, so `R = {Δ₄ > 0}` is a cone.  Inside `[0,1]⁴` every coordinate is
   `≥ 0`, so `maxⱼ |xⱼ| = maxⱼ xⱼ` and the cube splits into only **four** pieces
   (Theorem 3 needed eight), according to which coordinate is the largest.
   Slicing the `j`-th piece at `x_j = t` gives `t · (face x_j = 1)` by
   homogeneity, and `∫₀¹ t³ dt = 1/4`, so each piece contributes `F_j/4`.
2. **Face identifications.**  The face `a = 1` is the *monic* cubic on `[0,1]³`,
   which is literally `T2Set`, so `F_a = 1/2880` (Theorem 2).  Coefficient
   reversal `revMap : (a,b,c,d) ↦ (d,c,b,a)` preserves `Δ₄` and the cube, giving
   `F_d = F_a` and `F_c = F_b`.  Hence `vol₄ = (1/2)·(1/2880) + (1/2)·F_b`.
3. **The face `b = 1`** — the genuinely new computation; see `Face4B.lean`.

This file contains steps 1 and 2.
-/
import NonmonicCubic.Theorem4Statement

namespace NonmonicCubic

open Real Set MeasureTheory
open scoped Pointwise

/-! ## The positive orthant -/

/-- The closed positive orthant of `ℝ⁴`. -/
def nonnegSet : Set (ℝ × ℝ × ℝ × ℝ) :=
  {x | 0 ≤ x.1 ∧ 0 ≤ x.2.1 ∧ 0 ≤ x.2.2.1 ∧ 0 ≤ x.2.2.2}

theorem measurableSet_nonnegSet : MeasurableSet nonnegSet := by
  have h : nonnegSet = (({x : ℝ × ℝ × ℝ × ℝ | (0 : ℝ) ≤ x.1}
      ∩ {x : ℝ × ℝ × ℝ × ℝ | (0 : ℝ) ≤ x.2.1})
      ∩ {x : ℝ × ℝ × ℝ × ℝ | (0 : ℝ) ≤ x.2.2.1})
      ∩ {x : ℝ × ℝ × ℝ × ℝ | (0 : ℝ) ≤ x.2.2.2} := by
    ext x; simp only [nonnegSet, Set.mem_ofPred_eq, Set.mem_inter_iff]; tauto
  rw [h]
  exact (((measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_le measurable_const (measurable_fst.comp measurable_snd))).inter
      (measurableSet_le measurable_const
        ((measurable_fst.comp measurable_snd).comp measurable_snd))).inter
    (measurableSet_le measurable_const ((measurable_snd.comp measurable_snd).comp measurable_snd))

theorem nonnegSet_swap12 : swap12 ⁻¹' nonnegSet = nonnegSet := by
  ext x; simp only [Set.mem_preimage, nonnegSet, swap12, Set.mem_ofPred_eq]; tauto

theorem nonnegSet_revMap : revMap ⁻¹' nonnegSet = nonnegSet := by
  ext x; simp only [Set.mem_preimage, nonnegSet, revMap, Set.mem_ofPred_eq]; tauto

/-- On the positive orthant the sup-norm is the largest coordinate. -/
theorem coord_le_nrm₁ {x : ℝ × ℝ × ℝ × ℝ} : x.1 ≤ nrm x := le_trans (le_abs_self _) (abs_le_nrm₁ x)
theorem coord_le_nrm₂ {x : ℝ × ℝ × ℝ × ℝ} : x.2.1 ≤ nrm x :=
  le_trans (le_abs_self _) (abs_le_nrm₂ x)
theorem coord_le_nrm₃ {x : ℝ × ℝ × ℝ × ℝ} : x.2.2.1 ≤ nrm x :=
  le_trans (le_abs_self _) (abs_le_nrm₃ x)
theorem coord_le_nrm₄ {x : ℝ × ℝ × ℝ × ℝ} : x.2.2.2 ≤ nrm x :=
  le_trans (le_abs_self _) (abs_le_nrm₄ x)

/-! ## The four pieces -/

/-- The piece of `[0,1]⁴` where the **first** coordinate is the largest. -/
def conePieceP1 : Set (ℝ × ℝ × ℝ × ℝ) := nonnegSet ∩ conePiece1

def conePieceP2 : Set (ℝ × ℝ × ℝ × ℝ) := swap12 ⁻¹' conePieceP1

def conePieceP3 : Set (ℝ × ℝ × ℝ × ℝ) := revMap ⁻¹' conePieceP2

def conePieceP4 : Set (ℝ × ℝ × ℝ × ℝ) := revMap ⁻¹' conePieceP1

/-- The face `x₁ = 1` of a cone, over the **unit** cube `[0,1]³`. -/
def coneFaceP1 (R : Set (ℝ × ℝ × ℝ × ℝ)) : Set (ℝ × ℝ × ℝ) :=
  {y | y.1 ∈ Icc (0 : ℝ) 1 ∧ y.2.1 ∈ Icc (0 : ℝ) 1 ∧ y.2.2 ∈ Icc (0 : ℝ) 1 ∧ (1, y) ∈ R}

theorem measurableSet_conePieceP1 : MeasurableSet conePieceP1 :=
  measurableSet_nonnegSet.inter measurableSet_conePiece1

theorem measurableSet_conePieceP2 : MeasurableSet conePieceP2 :=
  measurableSet_conePieceP1.preimage measurable_swap12

theorem measurableSet_conePieceP3 : MeasurableSet conePieceP3 :=
  measurableSet_conePieceP2.preimage measurePreserving_revMap.measurable

theorem measurableSet_conePieceP4 : MeasurableSet conePieceP4 :=
  measurableSet_conePieceP1.preimage measurePreserving_revMap.measurable

/-- The clean description of the first positive piece. -/
theorem conePieceP1_eq :
    conePieceP1 = {x : ℝ × ℝ × ℝ × ℝ |
      x ∈ nonnegSet ∧ 0 < nrm x ∧ nrm x ≤ 1 ∧ x.1 = nrm x} := by
  rw [conePieceP1, conePiece1_eq]
  rfl

theorem conePieceP2_eq :
    conePieceP2 = {x : ℝ × ℝ × ℝ × ℝ |
      x ∈ nonnegSet ∧ 0 < nrm x ∧ nrm x ≤ 1 ∧ x.2.1 = nrm x} := by
  ext x
  have h1 : swap12 x ∈ nonnegSet ↔ x ∈ nonnegSet := by
    simp only [nonnegSet, swap12, Set.mem_ofPred_eq]; tauto
  rw [conePieceP2, Set.mem_preimage, conePieceP1_eq]
  simp only [Set.mem_ofPred_eq, nrm_swap12, h1]
  exact Iff.rfl

theorem conePieceP3_eq :
    conePieceP3 = {x : ℝ × ℝ × ℝ × ℝ |
      x ∈ nonnegSet ∧ 0 < nrm x ∧ nrm x ≤ 1 ∧ x.2.2.1 = nrm x} := by
  ext x
  have h1 : revMap x ∈ nonnegSet ↔ x ∈ nonnegSet := by
    simp only [nonnegSet, revMap, Set.mem_ofPred_eq]; tauto
  rw [conePieceP3, Set.mem_preimage, conePieceP2_eq]
  simp only [Set.mem_ofPred_eq, nrm_revMap, h1]
  exact Iff.rfl

theorem conePieceP4_eq :
    conePieceP4 = {x : ℝ × ℝ × ℝ × ℝ |
      x ∈ nonnegSet ∧ 0 < nrm x ∧ nrm x ≤ 1 ∧ x.2.2.2 = nrm x} := by
  ext x
  have h1 : revMap x ∈ nonnegSet ↔ x ∈ nonnegSet := by
    simp only [nonnegSet, revMap, Set.mem_ofPred_eq]; tauto
  rw [conePieceP4, Set.mem_preimage, conePieceP1_eq]
  simp only [Set.mem_ofPred_eq, nrm_revMap, h1]
  exact Iff.rfl

/-! ## The radial identity on the positive orthant -/

/-- Rescaling by `t > 0` turns "`0 ≤ z` and `|z| ≤ t`" into "`t⁻¹ z ∈ [0,1]`". -/
theorem scale_mem_iff {t z : ℝ} (ht0 : 0 < t) :
    ((0 : ℝ) ≤ t⁻¹ * z ∧ t⁻¹ * z ≤ 1) ↔ (0 ≤ z ∧ |z| ≤ t) := by
  have htne : t ≠ 0 := ne_of_gt ht0
  have hti : t * t⁻¹ = 1 := mul_inv_cancel₀ htne
  constructor
  · rintro ⟨h1, h2⟩
    have hz0 : 0 ≤ z := by
      have h := mul_nonneg ht0.le h1
      rwa [← mul_assoc, hti, one_mul] at h
    have hzt : z ≤ t := by
      have h := mul_le_mul_of_nonneg_left h2 ht0.le
      rwa [← mul_assoc, hti, one_mul, mul_one] at h
    exact ⟨hz0, abs_le.2 ⟨by linarith, hzt⟩⟩
  · rintro ⟨h1, h2⟩
    have hzt : z ≤ t := le_trans (le_abs_self z) h2
    refine ⟨mul_nonneg (inv_pos.2 ht0).le h1, ?_⟩
    have h := mul_le_mul_of_nonneg_left hzt (inv_pos.2 ht0).le
    rwa [inv_mul_cancel₀ htne] at h

theorem slice_conePieceP1 {R : Set (ℝ × ℝ × ℝ × ℝ)} (hR : IsCone R) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t ≤ 1) :
    Prod.mk t ⁻¹' (R ∩ conePieceP1) = t • coneFaceP1 R := by
  have htne : t ≠ 0 := ne_of_gt ht0
  have hRiff : ∀ y : ℝ × ℝ × ℝ, ((t, y) ∈ R ↔ ((1 : ℝ), t⁻¹ • y) ∈ R) := by
    intro y
    constructor
    · intro h
      have h2 := hR t⁻¹ (inv_pos.2 ht0) _ h
      rwa [Prod.smul_mk, smul_eq_mul, inv_mul_cancel₀ htne] at h2
    · intro h
      have h2 := hR t ht0 _ h
      rwa [Prod.smul_mk, smul_eq_mul, mul_one, smul_smul, mul_inv_cancel₀ htne,
        one_smul] at h2
  ext y
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ htne]
  constructor
  · rintro ⟨hRy, ⟨-, hn1, hn2, hn3⟩, -, -, ha1, ha2, ha3⟩
    exact ⟨(scale_mem_iff ht0).2 ⟨hn1, ha1⟩, (scale_mem_iff ht0).2 ⟨hn2, ha2⟩,
      (scale_mem_iff ht0).2 ⟨hn3, ha3⟩, (hRiff y).1 hRy⟩
  · rintro ⟨h1, h2, h3, hRy⟩
    obtain ⟨hn1, ha1⟩ := (scale_mem_iff ht0).1 h1
    obtain ⟨hn2, ha2⟩ := (scale_mem_iff ht0).1 h2
    obtain ⟨hn3, ha3⟩ := (scale_mem_iff ht0).1 h3
    exact ⟨(hRiff y).2 hRy, ⟨ht0.le, hn1, hn2, hn3⟩, ht0, ht1, ha1, ha2, ha3⟩

theorem volume_coneFaceP1_ne_top (R : Set (ℝ × ℝ × ℝ × ℝ)) :
    volume (coneFaceP1 R) ≠ ⊤ := by
  have hsub : coneFaceP1 R ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
    rintro y ⟨h1, h2, h3, -⟩
    exact ⟨h1, h2, h3⟩
  refine ne_top_of_le_ne_top ?_ (measure_mono hsub)
  rw [volume_cube_unit]
  exact ENNReal.one_ne_top

/-- **The radial identity, positive orthant, first face.** -/
theorem volume_conePieceP1 {R : Set (ℝ × ℝ × ℝ × ℝ)} (hR : MeasurableSet R)
    (hcone : IsCone R) :
    volume (R ∩ conePieceP1) = ENNReal.ofReal (1 / 4) * volume (coneFaceP1 R) := by
  rw [show (volume : Measure (ℝ × ℝ × ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
    Measure.prod_apply (hR.inter measurableSet_conePieceP1)]
  have hfun : (fun t : ℝ => (volume : Measure (ℝ × ℝ × ℝ)) (Prod.mk t ⁻¹' (R ∩ conePieceP1)))
      = (Set.Ioc (0 : ℝ) 1).indicator
        (fun t => ENNReal.ofReal (t ^ 3) * volume (coneFaceP1 R)) := by
    funext t
    by_cases ht : t ∈ Set.Ioc (0 : ℝ) 1
    · rw [Set.indicator_of_mem ht, slice_conePieceP1 hcone ht.1 ht.2,
        volume_smul_three ht.1.le]
    · rw [Set.indicator_of_notMem ht]
      have hempty : Prod.mk t ⁻¹' (R ∩ conePieceP1) = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro y ⟨-, -, h1, h2, -⟩
        exact ht ⟨h1, h2⟩
      rw [hempty, measure_empty]
  rw [hfun, lintegral_indicator measurableSet_Ioc,
    lintegral_mul_const' _ _ (volume_coneFaceP1_ne_top R), lintegral_pow_three, mul_comm]

/-! ## The two faces -/

/-- The face `a = 1`: the monic cubic on `[0,1]³` — literally Theorem 2's set. -/
theorem coneFaceP1_RCone : coneFaceP1 RCone = T2Set := by
  ext y
  simp only [coneFaceP1, T2Set, RCone, Set.mem_ofPred_eq, Δ₄_one]

/-- The face `b = 1`: the new three-dimensional region. -/
def FaceB0 : Set (ℝ × ℝ × ℝ) :=
  {p | p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2.1 ∈ Icc (0 : ℝ) 1 ∧ p.2.2 ∈ Icc (0 : ℝ) 1 ∧
    0 < Δ₄ p.1 1 p.2.1 p.2.2}

theorem coneFaceP1_swap12_RCone : coneFaceP1 (swap12 ⁻¹' RCone) = FaceB0 := by
  ext y
  simp only [coneFaceP1, FaceB0, RCone, swap12, Set.mem_preimage, Set.mem_ofPred_eq]

/-! ## The four-piece partition -/

theorem nrm_le_one_of_mem_T4Set {x : ℝ × ℝ × ℝ × ℝ} (h : x ∈ T4Set) : nrm x ≤ 1 := by
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩, ⟨d1, d2⟩, -⟩ := h
  unfold nrm
  refine max_le (max_le ?_ ?_) (max_le ?_ ?_) <;> rw [abs_le] <;> constructor <;> linarith

theorem nonnegSet_of_mem_T4Set {x : ℝ × ℝ × ℝ × ℝ} (h : x ∈ T4Set) : x ∈ nonnegSet :=
  ⟨h.1.1, h.2.1.1, h.2.2.1.1, h.2.2.2.1.1⟩

theorem mem_T4Set_of_nrm {x : ℝ × ℝ × ℝ × ℝ} (h : x ∈ RCone) (hnn : x ∈ nonnegSet)
    (hn : nrm x ≤ 1) : x ∈ T4Set :=
  ⟨⟨hnn.1, le_trans coord_le_nrm₁ hn⟩, ⟨hnn.2.1, le_trans coord_le_nrm₂ hn⟩,
    ⟨hnn.2.2.1, le_trans coord_le_nrm₃ hn⟩, ⟨hnn.2.2.2, le_trans coord_le_nrm₄ hn⟩, h⟩

theorem disjP_1_2 : Disjoint (Qp conePieceP1) (Qp conePieceP2) := by
  rw [Set.disjoint_left]
  rintro x ⟨⟨-, h1⟩, ht⟩ ⟨⟨-, h2⟩, -⟩
  rw [conePieceP1_eq] at h1; rw [conePieceP2_eq] at h2
  exact ht (tieSet_subset_tieCover (tie₁ (by rw [h1.2.2.2, h2.2.2.2])))

theorem disjP_1_3 : Disjoint (Qp conePieceP1) (Qp conePieceP3) := by
  rw [Set.disjoint_left]
  rintro x ⟨⟨-, h1⟩, ht⟩ ⟨⟨-, h2⟩, -⟩
  rw [conePieceP1_eq] at h1; rw [conePieceP3_eq] at h2
  exact ht (tieSet_subset_tieCover (tie₃ (by rw [h1.2.2.2, h2.2.2.2])))

theorem disjP_1_4 : Disjoint (Qp conePieceP1) (Qp conePieceP4) := by
  rw [Set.disjoint_left]
  rintro x ⟨⟨-, h1⟩, ht⟩ ⟨⟨-, h2⟩, -⟩
  rw [conePieceP1_eq] at h1; rw [conePieceP4_eq] at h2
  exact ht (tieSet_subset_tieCover (tie₅ (by rw [h1.2.2.2, h2.2.2.2])))

theorem disjP_2_3 : Disjoint (Qp conePieceP2) (Qp conePieceP3) := by
  rw [Set.disjoint_left]
  rintro x ⟨⟨-, h1⟩, ht⟩ ⟨⟨-, h2⟩, -⟩
  rw [conePieceP2_eq] at h1; rw [conePieceP3_eq] at h2
  exact ht (tieSet_subset_tieCover (tie₇ (by rw [h1.2.2.2, h2.2.2.2])))

theorem disjP_2_4 : Disjoint (Qp conePieceP2) (Qp conePieceP4) := by
  rw [Set.disjoint_left]
  rintro x ⟨⟨-, h1⟩, ht⟩ ⟨⟨-, h2⟩, -⟩
  rw [conePieceP2_eq] at h1; rw [conePieceP4_eq] at h2
  exact ht (tieSet_subset_tieCover (tie₉ (by rw [h1.2.2.2, h2.2.2.2])))

theorem disjP_3_4 : Disjoint (Qp conePieceP3) (Qp conePieceP4) := by
  rw [Set.disjoint_left]
  rintro x ⟨⟨-, h1⟩, ht⟩ ⟨⟨-, h2⟩, -⟩
  rw [conePieceP3_eq] at h1; rw [conePieceP4_eq] at h2
  exact ht (tieSet_subset_tieCover (tie₁₁ (by rw [h1.2.2.2, h2.2.2.2])))

theorem T4Set_diff_eq :
    T4Set \ tieCover =
      Qp conePieceP1 ∪ (Qp conePieceP2 ∪ (Qp conePieceP3 ∪ Qp conePieceP4)) := by
  ext x
  constructor
  · rintro ⟨hx, ht⟩
    have hR : x ∈ RCone := hx.2.2.2.2
    have hpos := nrm_pos_of_mem_RCone hR
    have hle := nrm_le_one_of_mem_T4Set hx
    have hnn := nonnegSet_of_mem_T4Set hx
    have hmem : ∀ P : Set (ℝ × ℝ × ℝ × ℝ), x ∈ P → x ∈ Qp P := fun P h => ⟨⟨hR, h⟩, ht⟩
    rcases nrm_eq_abs x with h | h | h | h
    · refine Or.inl (hmem _ ?_)
      rw [conePieceP1_eq]
      exact ⟨hnn, hpos, hle, by rw [h, abs_of_nonneg hnn.1]⟩
    · refine Or.inr (Or.inl (hmem _ ?_))
      rw [conePieceP2_eq]
      exact ⟨hnn, hpos, hle, by rw [h, abs_of_nonneg hnn.2.1]⟩
    · refine Or.inr (Or.inr (Or.inl (hmem _ ?_)))
      rw [conePieceP3_eq]
      exact ⟨hnn, hpos, hle, by rw [h, abs_of_nonneg hnn.2.2.1]⟩
    · refine Or.inr (Or.inr (Or.inr (hmem _ ?_)))
      rw [conePieceP4_eq]
      exact ⟨hnn, hpos, hle, by rw [h, abs_of_nonneg hnn.2.2.2]⟩
  · rintro (h | h | h | h) <;> obtain ⟨⟨hR, hP⟩, ht⟩ := h
    · rw [conePieceP1_eq] at hP; exact ⟨mem_T4Set_of_nrm hR hP.1 hP.2.2.1, ht⟩
    · rw [conePieceP2_eq] at hP; exact ⟨mem_T4Set_of_nrm hR hP.1 hP.2.2.1, ht⟩
    · rw [conePieceP3_eq] at hP; exact ⟨mem_T4Set_of_nrm hR hP.1 hP.2.2.1, ht⟩
    · rw [conePieceP4_eq] at hP; exact ⟨mem_T4Set_of_nrm hR hP.1 hP.2.2.1, ht⟩

theorem volume_T4Set_sum :
    volume T4Set = volume (RCone ∩ conePieceP1) + (volume (RCone ∩ conePieceP2)
      + (volume (RCone ∩ conePieceP3) + volume (RCone ∩ conePieceP4))) := by
  have hT : volume T4Set = volume (T4Set \ tieCover) :=
    (measure_sdiff_null volume_tieCover).symm
  rw [hT, T4Set_diff_eq]
  rw [measure_union
    (by simp only [Set.disjoint_union_right]; exact ⟨disjP_1_2, disjP_1_3, disjP_1_4⟩)
    ((measurableSet_Qp measurableSet_conePieceP2).union
      ((measurableSet_Qp measurableSet_conePieceP3).union
        (measurableSet_Qp measurableSet_conePieceP4)))]
  rw [measure_union
    (by simp only [Set.disjoint_union_right]; exact ⟨disjP_2_3, disjP_2_4⟩)
    ((measurableSet_Qp measurableSet_conePieceP3).union
      (measurableSet_Qp measurableSet_conePieceP4))]
  rw [measure_union disjP_3_4 (measurableSet_Qp measurableSet_conePieceP4)]
  simp only [volume_Qp]

theorem volume_conePieceP2_eq :
    volume (RCone ∩ conePieceP2) = ENNReal.ofReal (1 / 4) * volume FaceB0 := by
  have hm : MeasurableSet (swap12 ⁻¹' RCone) := measurableSet_RCone.preimage measurable_swap12
  have hpre : RCone ∩ conePieceP2 = swap12 ⁻¹' ((swap12 ⁻¹' RCone) ∩ conePieceP1) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, conePieceP2, swap12_involutive]
  rw [hpre, measurePreserving_swap12.measure_preimage
      (hm.inter measurableSet_conePieceP1).nullMeasurableSet,
    volume_conePieceP1 hm isCone_swap12_RCone, coneFaceP1_swap12_RCone]

theorem volume_conePieceP3_eq :
    volume (RCone ∩ conePieceP3) = volume (RCone ∩ conePieceP2) :=
  volume_piece_transport measurePreserving_revMap revMap_preimage_RCone measurableSet_conePieceP2

theorem volume_conePieceP4_eq :
    volume (RCone ∩ conePieceP4) = volume (RCone ∩ conePieceP1) :=
  volume_piece_transport measurePreserving_revMap revMap_preimage_RCone measurableSet_conePieceP1

/-- **The cone/face identity on the unit 4-cube.**

    vol₄(T4Set) = (1/2)·vol₃(T2Set) + (1/2)·vol₃(FaceB0). -/
theorem volume_T4Set_eq_faces :
    volume T4Set = ENNReal.ofReal (1 / 2) * volume T2Set
      + ENNReal.ofReal (1 / 2) * volume FaceB0 := by
  rw [volume_T4Set_sum, volume_conePieceP3_eq, volume_conePieceP4_eq,
    volume_conePieceP1 measurableSet_RCone isCone_RCone, coneFaceP1_RCone,
    volume_conePieceP2_eq]
  have h2 : ENNReal.ofReal (1 / 4 : ℝ) + ENNReal.ofReal (1 / 4 : ℝ)
      = ENNReal.ofReal (1 / 2 : ℝ) := by
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num
  rw [show ENNReal.ofReal (1 / 4) * volume T2Set
      + (ENNReal.ofReal (1 / 4) * volume FaceB0
        + (ENNReal.ofReal (1 / 4) * volume FaceB0 + ENNReal.ofReal (1 / 4) * volume T2Set))
      = (ENNReal.ofReal (1 / 4) + ENNReal.ofReal (1 / 4)) * volume T2Set
        + (ENNReal.ofReal (1 / 4) + ENNReal.ofReal (1 / 4)) * volume FaceB0 by ring, h2]

/-- **The reduction, with Theorem 2 substituted in.**
`vol₄(T4Set) = 1/5760 + (1/2)·vol₃(FaceB0)`. -/
theorem volume_T4Set_eq :
    volume T4Set = ENNReal.ofReal (1 / 5760) + ENNReal.ofReal (1 / 2) * volume FaceB0 := by
  rw [volume_T4Set_eq_faces, volume_T2Set, ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

end NonmonicCubic
