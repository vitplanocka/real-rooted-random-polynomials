/-
# The face `b = 1` of the unit 4-cube

    S := vol₃{ (a,c,d) ∈ [0,1]³ : a x³ + x² + c x + d has three real roots }
       = 479/960 − (2/3) log 2.

## The idea

For `a > 0` the substitution `y = a x` turns `a x³ + x² + c x + d` into the *monic*
`y³ + y² + (ac) y + (a²d)`; on discriminants this is the `ring` identity

    Δ₃ 1 (a c) (a² d) = a² · Δ₄ a 1 c d      (`Δ₃_rescale`).

So the whole face is Theorem 2's monic band problem in the variables `B = a c`,
`C = a² d`, and the machinery of `Basic.lean`/`Integrals.lean` applies verbatim.
Concretely, at fixed `a` the admissible `d` form the interval
`(cLo 1 (a c) / a², cHi 1 (a c) / a²)`, clipped below by the window floor `d = 0`
and — by `cHi_one_le_sq`, the `L1` lemma — *never* clipped above, since

    cHi 1 B ≤ B²  for 0 ≤ B ≤ 1/3   ⟺   (v−1)²(3v²+4v+2) ≥ 0,  v = √(1−3B),

whence `d < cHi 1 (a c)/a² ≤ (a c)²/a² = c² ≤ 1`.

The bottom clips exactly when `a c ≤ 1/4` (`cLo 1 B ≤ 0 ⟺ 4B ≤ 1`), so the
`c`-integral splits at `c = 1/(4a)` and all fractional powers collect into `p52`.
The resulting slice area is a rational function of `a` and `(1−3a)^{5/2}`; the
final `a`-integral is done with explicit antiderivatives built from
`u = √(1−3a)`, and produces `log 2` (the `log 3`s cancel between the two pieces).
-/
import NonmonicCubic.Theorem4Proof

namespace NonmonicCubic

open Real Set MeasureTheory intervalIntegral

/-! ## The rescaling to the monic case -/

/-- `y = a x` turns the face `b = 1` into the monic problem. Pure `ring`. -/
theorem Δ₃_rescale (a c d : ℝ) : Δ₃ 1 (a * c) (a ^ 2 * d) = a ^ 2 * Δ₄ a 1 c d := by
  unfold Δ₃ Δ₄; ring

/-! ## `L1` — the band never clips above -/

/-- **L1.**  `cHi 1 B ≤ B²` on `0 ≤ B ≤ 1/3`.  With `v = √(1−3B)` this is
`(v−1)²(3v²+4v+2) ≥ 0`, true for every real `v`. -/
theorem cHi_one_le_sq {B : ℝ} (h0 : 0 ≤ B) (h3 : 3 * B ≤ 1) : cHi 1 B ≤ B ^ 2 := by
  have hnn : (0 : ℝ) ≤ 1 - 3 * B := by linarith
  set v := Real.sqrt (1 - 3 * B) with hv
  have hv0 : 0 ≤ v := Real.sqrt_nonneg _
  have hv2 : v ^ 2 = 1 - 3 * B := Real.sq_sqrt hnn
  have hp : p32 (1 - 3 * B) = v ^ 3 := by rw [← hv2, p32_eq_sq_mul v hv0]
  unfold cHi
  rw [show (1 : ℝ) ^ 2 - 3 * B = 1 - 3 * B by ring, hp]
  nlinarith [mul_nonneg (sq_nonneg (v - 1)) (by nlinarith : (0 : ℝ) ≤ 3 * v ^ 2 + 4 * v + 2),
    sq_nonneg (v - 1), sq_nonneg v]

/-! ## The clipped `d`-band -/

/-- Top of the admissible `d`-interval on the face `b = 1`. -/
noncomputable def DHi (a c : ℝ) : ℝ := cHi 1 (a * c) / a ^ 2

/-- Bottom of the admissible `d`-interval, clipped at the window floor `d = 0`. -/
noncomputable def DLo0 (a c : ℝ) : ℝ := max (cLo 1 (a * c)) 0 / a ^ 2

/-- The `c`-range at fixed `a`: both `c ≤ 1` and `a c ≤ 1/3`. -/
noncomputable def cUp (a : ℝ) : ℝ := min 1 (1 / (3 * a))

theorem continuous_DHi (a : ℝ) : Continuous (DHi a) :=
  ((continuous_cHi 1).comp (continuous_const.mul continuous_id)).div_const _

theorem continuous_DLo0 (a : ℝ) : Continuous (DLo0 a) :=
  ((((continuous_cLo 1).comp (continuous_const.mul continuous_id)).max
    continuous_const)).div_const _

theorem cUp_le_one (a : ℝ) : cUp a ≤ 1 := min_le_left _ _

theorem cUp_pos {a : ℝ} (ha : 0 < a) : 0 < cUp a :=
  lt_min one_pos (by positivity)

theorem mul_cUp_le {a c : ℝ} (ha : 0 < a) (hc : c ≤ cUp a) : 3 * (a * c) ≤ 1 := by
  have h : c ≤ 1 / (3 * a) := le_trans hc (min_le_right _ _)
  have h3 : 0 < 3 * a := by linarith
  calc 3 * (a * c) = (3 * a) * c := by ring
    _ ≤ (3 * a) * (1 / (3 * a)) := by nlinarith
    _ = 1 := by field_simp

theorem DHi_le_one {a c : ℝ} (ha : 0 < a) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hcu : c ≤ cUp a) : DHi a c ≤ 1 := by
  have hB0 : 0 ≤ a * c := mul_nonneg ha.le hc0
  have hB3 : 3 * (a * c) ≤ 1 := mul_cUp_le ha hcu
  have h := cHi_one_le_sq hB0 hB3
  have ha2 : 0 < a ^ 2 := by positivity
  have hcc : c ^ 2 ≤ 1 := by nlinarith
  have hsq : (a * c) ^ 2 ≤ a ^ 2 := by nlinarith [sq_nonneg a]
  rw [DHi, div_le_one ha2]
  linarith

theorem DLo0_nonneg (a c : ℝ) : 0 ≤ DLo0 a c :=
  div_nonneg (le_max_right _ _) (sq_nonneg a)

/-! ## The slice of `FaceB0` at fixed `a` -/

theorem region_subset_sliceB0 {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    regionBetween (DLo0 a) (DHi a) (Ico 0 (cUp a)) ⊆ Prod.mk a ⁻¹' FaceB0 := by
  rintro ⟨c, d⟩ ⟨⟨hc0, hc2⟩, hd1, hd2⟩
  have ha2 : (0 : ℝ) < a ^ 2 := by positivity
  have hcu : c ≤ cUp a := hc2.le
  have hc1 : c ≤ 1 := le_trans hcu (cUp_le_one a)
  have hnn : (0 : ℝ) ≤ 1 ^ 2 - 3 * (a * c) := by
    have := mul_cUp_le ha hcu; linarith
  have hd0 : 0 ≤ d := le_trans (DLo0_nonneg a c) hd1.le
  have hdle : d ≤ 1 := le_trans hd2.le (DHi_le_one ha hc0 hc1 hcu)
  refine ⟨⟨ha.le, ha1⟩, ⟨hc0, hc1⟩, ⟨hd0, hdle⟩, ?_⟩
  have hlo : cLo 1 (a * c) < a ^ 2 * d := by
    have h1 : max (cLo 1 (a * c)) 0 / a ^ 2 < d := hd1
    rw [div_lt_iff₀ ha2] at h1
    calc cLo 1 (a * c) ≤ max (cLo 1 (a * c)) 0 := le_max_left _ _
      _ < d * a ^ 2 := h1
      _ = a ^ 2 * d := by ring
  have hhi : a ^ 2 * d < cHi 1 (a * c) := by
    have h2 : d < cHi 1 (a * c) / a ^ 2 := hd2
    rw [lt_div_iff₀ ha2] at h2
    linarith [h2]
  have hpos : 0 < Δ₃ 1 (a * c) (a ^ 2 * d) := (Δ₃_pos_iff hnn _).2 ⟨hlo, hhi⟩
  rw [Δ₃_rescale] at hpos
  nlinarith [hpos]

theorem sliceB0_sdiff_subset {a : ℝ} (ha : 0 < a) :
    (Prod.mk a ⁻¹' FaceB0) \ regionBetween (DLo0 a) (DHi a) (Ico 0 (cUp a))
      ⊆ {q : ℝ × ℝ | q.2 = 0} ∪ {q : ℝ × ℝ | q.1 = 1} := by
  rintro ⟨c, d⟩ ⟨⟨-, ⟨hc0, hc1⟩, ⟨hd0, -⟩, hΔ⟩, hout⟩
  by_contra hcon
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or] at hcon
  obtain ⟨hd, hc⟩ := hcon
  have ha2 : (0 : ℝ) < a ^ 2 := by positivity
  have hdpos : 0 < d := lt_of_le_of_ne hd0 (Ne.symm hd)
  have hc1' : c < 1 := lt_of_le_of_ne hc1 hc
  have hΔ3 : 0 < Δ₃ 1 (a * c) (a ^ 2 * d) := by rw [Δ₃_rescale]; positivity
  have hnn : (0 : ℝ) ≤ 1 ^ 2 - 3 * (a * c) := by
    by_contra hlt
    rw [not_le] at hlt
    exact absurd hΔ3 (not_lt.2 (Δ₃_neg_of_lt hlt _).le)
  obtain ⟨hlo, hhi⟩ := (Δ₃_pos_iff hnn _).1 hΔ3
  have hltc : cLo 1 (a * c) < cHi 1 (a * c) := lt_trans hlo hhi
  have hp : 0 < p32 (1 ^ 2 - 3 * (a * c)) := by
    have h1 := cHi_sub_cLo 1 (a * c)
    set X := p32 (1 ^ 2 - 3 * (a * c)) with hX
    linarith
  have hstrict : 3 * (a * c) < 1 := by
    rcases lt_or_eq_of_le hnn with h | h
    · linarith
    · exfalso; unfold p32 at hp; rw [← h] at hp; simp at hp
  refine hout ⟨⟨hc0, ?_⟩, ?_, ?_⟩
  · refine lt_min hc1' ?_
    rw [lt_div_iff₀ (by linarith : (0 : ℝ) < 3 * a)]
    nlinarith
  · simp only [DLo0]
    rw [div_lt_iff₀ ha2]
    exact max_lt (by nlinarith) (by nlinarith)
  · simp only [DHi]
    rw [lt_div_iff₀ ha2]
    nlinarith

theorem volume_snd_eq_zero' : (volume : Measure (ℝ × ℝ)) {q : ℝ × ℝ | q.2 = 0} = 0 :=
  volume_snd_eq_zero

theorem volume_fst_eq_one_zero : (volume : Measure (ℝ × ℝ)) {q : ℝ × ℝ | q.1 = 1} = 0 := by
  have h : {q : ℝ × ℝ | q.1 = 1} = ({1} : Set ℝ) ×ˢ (univ : Set ℝ) := by ext q; simp
  rw [h, show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
    Measure.prod_prod]
  simp

theorem volume_sliceB_eq {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    volume (Prod.mk a ⁻¹' FaceB0)
      = volume (regionBetween (DLo0 a) (DHi a) (Ico 0 (cUp a))) := by
  refine le_antisymm ?_ (measure_mono (region_subset_sliceB0 ha ha1))
  calc volume (Prod.mk a ⁻¹' FaceB0)
      ≤ volume (regionBetween (DLo0 a) (DHi a) (Ico 0 (cUp a))
          ∪ ({q : ℝ × ℝ | q.2 = 0} ∪ {q : ℝ × ℝ | q.1 = 1})) := by
        refine measure_mono fun q hq => ?_
        by_cases h : q ∈ regionBetween (DLo0 a) (DHi a) (Ico 0 (cUp a))
        · exact Or.inl h
        · exact Or.inr (sliceB0_sdiff_subset ha ⟨hq, h⟩)
    _ ≤ volume (regionBetween (DLo0 a) (DHi a) (Ico 0 (cUp a)))
          + volume ({q : ℝ × ℝ | q.2 = 0} ∪ {q : ℝ × ℝ | q.1 = 1}) := measure_union_le _ _
    _ = volume (regionBetween (DLo0 a) (DHi a) (Ico 0 (cUp a))) := by
        have : volume ({q : ℝ × ℝ | q.2 = 0} ∪ {q : ℝ × ℝ | q.1 = 1}) = 0 :=
          measure_union_null volume_snd_eq_zero' volume_fst_eq_one_zero
        rw [this, add_zero]

/-! ## The `c`-integral of the clipped band width -/

theorem one_sq_sub (B : ℝ) : (1 : ℝ) ^ 2 - 3 * B = 1 - 3 * B := by norm_num

theorem cHi_one (B : ℝ) : cHi 1 B = (9 * B - 2 + 2 * p32 (1 - 3 * B)) / 27 := by
  unfold cHi; rw [one_sq_sub]; ring

theorem cLo_one (B : ℝ) : cLo 1 B = (9 * B - 2 - 2 * p32 (1 - 3 * B)) / 27 := by
  unfold cLo; rw [one_sq_sub]; ring

theorem cHi_sub_cLo_one (B : ℝ) : cHi 1 B - cLo 1 B = 4 / 27 * p32 (1 - 3 * B) := by
  rw [cHi_one, cLo_one]; ring

/-- The integrand where the floor clips (`4 a c ≤ 1`): the band is `[0, DHi]`. -/
theorem integrand_clip {a c : ℝ} (ha : 0 < a) (hc0 : 0 ≤ c) (h4 : 4 * (a * c) ≤ 1) :
    (DHi a - DLo0 a) c = cHi 1 (a * c) / a ^ 2 := by
  have hb0 : 0 ≤ a * c := mul_nonneg ha.le hc0
  have h : cLo 1 (a * c) ≤ 0 := cLo_nonpos hb0 (by nlinarith)
  simp only [Pi.sub_apply, DHi, DLo0, max_eq_right h]
  simp

/-- The integrand where the floor does not clip (`1 ≤ 4 a c`): the full band width. -/
theorem integrand_full {a c : ℝ} (_ha : 0 < a) (h4 : 1 ≤ 4 * (a * c)) (h3 : 3 * (a * c) ≤ 1) :
    (DHi a - DLo0 a) c = 4 / 27 * p32 (1 - 3 * (a * c)) / a ^ 2 := by
  have h : 0 ≤ cLo 1 (a * c) := cLo_nonneg (by norm_num) (by nlinarith) (by nlinarith)
  simp only [Pi.sub_apply, DHi, DLo0, max_eq_left h]
  rw [div_sub_div_same, cHi_sub_cLo_one]

/-- Antiderivative of `c ↦ cHi 1 (a c)`. -/
noncomputable def Kc (a c : ℝ) : ℝ :=
  (9 * a * c ^ 2 / 2 - 2 * c) / 27 - 4 / (405 * a) * p52 (1 - 3 * (a * c))

/-- Antiderivative of `c ↦ (4/27) p32 (1 − 3 a c)`. -/
noncomputable def Wc (a c : ℝ) : ℝ := -(8 / (405 * a)) * p52 (1 - 3 * (a * c))

theorem continuous_shiftA (a : ℝ) : Continuous fun c : ℝ => 1 - 3 * (a * c) := by fun_prop

theorem continuous_Kc (a : ℝ) : Continuous (Kc a) := by
  unfold Kc
  exact (by fun_prop : Continuous fun c : ℝ => (9 * a * c ^ 2 / 2 - 2 * c) / 27).sub
    (continuous_const.mul (continuous_p52.comp (continuous_shiftA a)))

theorem continuous_Wc (a : ℝ) : Continuous (Wc a) := by
  unfold Wc
  exact continuous_const.mul (continuous_p52.comp (continuous_shiftA a))

theorem hasDerivAt_shiftA (a c : ℝ) : HasDerivAt (fun y : ℝ => 1 - 3 * (a * y)) (-(3 * a)) c := by
  simpa using (((hasDerivAt_id c).const_mul a).const_mul 3).const_sub 1

theorem hasDerivAt_Kc {a c : ℝ} (ha : 0 < a) (h : 0 < 1 - 3 * (a * c)) :
    HasDerivAt (Kc a) (cHi 1 (a * c)) c := by
  have h1 : HasDerivAt (fun y : ℝ => (9 * a * y ^ 2 / 2 - 2 * y) / 27)
      ((9 * a * (2 * c) / 2 - 2) / 27) c := by
    have := ((((hasDerivAt_id c).fun_pow 2).const_mul (9 * a)).div_const 2).sub
      ((hasDerivAt_id c).const_mul 2)
    simpa using this.div_const 27
  have h2 := ((hasDerivAt_p52 h).comp c (hasDerivAt_shiftA a c)).const_mul (4 / (405 * a))
  refine (h1.sub h2).congr_deriv ?_
  rw [cHi_one]
  field_simp
  ring

theorem hasDerivAt_Wc {a c : ℝ} (ha : 0 < a) (h : 0 < 1 - 3 * (a * c)) :
    HasDerivAt (Wc a) (4 / 27 * p32 (1 - 3 * (a * c))) c := by
  have h2 := ((hasDerivAt_p52 h).comp c (hasDerivAt_shiftA a c)).const_mul (-(8 / (405 * a)))
  refine h2.congr_deriv ?_
  field_simp
  ring

theorem integral_Kc {a l u : ℝ} (ha : 0 < a) (hlu : l ≤ u) (hu : 3 * (a * u) ≤ 1) :
    ∫ c in l..u, cHi 1 (a * c) = Kc a u - Kc a l := by
  refine integral_eq_sub_of_hasDerivAt_of_le hlu (continuous_Kc a).continuousOn
    (fun c hc => hasDerivAt_Kc ha ?_)
    (((continuous_cHi 1).comp (continuous_const.mul continuous_id)).intervalIntegrable _ _)
  have : c < u := hc.2
  nlinarith

theorem integral_Wc {a l u : ℝ} (ha : 0 < a) (hlu : l ≤ u) (hu : 3 * (a * u) ≤ 1) :
    ∫ c in l..u, 4 / 27 * p32 (1 - 3 * (a * c)) = Wc a u - Wc a l := by
  refine integral_eq_sub_of_hasDerivAt_of_le hlu (continuous_Wc a).continuousOn
    (fun c hc => hasDerivAt_Wc ha ?_)
    ((continuous_const.mul (continuous_p32.comp (continuous_shiftA a))).intervalIntegrable _ _)
  have : c < u := hc.2
  nlinarith

/-! ## The slice area in closed form -/

theorem p52_one : p52 (1 : ℝ) = 1 := by unfold p52; simp

theorem p52_quarter : p52 (1 / 4 : ℝ) = 1 / 32 := by
  rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, p52_eq_sq_mul (show (0:ℝ) ≤ 1 / 2 by norm_num)]
  norm_num

/-- The area of the `(c,d)`-slice of `FaceB0` at fixed `a`.  Three regimes:
the floor clips on the whole `c`-range (`a ≤ 1/4`), it clips on part of it
(`1/4 ≤ a ≤ 1/3`), and beyond `a = 1/3` the `c`-range itself is cut by
`a c ≤ 1/3` and all `a`-dependence collapses to `1/(480 a³)`. -/
noncomputable def sliceB0 (a : ℝ) : ℝ :=
  if a ≤ 1 / 4 then (a ^ 2 / 6 - 2 * a / 27 + 4 / 405 - 4 / 405 * p52 (1 - 3 * a)) / a ^ 3
  else if a ≤ 1 / 3 then (1 / 480 - 8 / 405 * p52 (1 - 3 * a)) / a ^ 3
  else 1 / (480 * a ^ 3)

theorem cUp_eq_one {a : ℝ} (ha : 0 < a) (h : a ≤ 1 / 3) : cUp a = 1 := by
  refine min_eq_left ?_
  rw [le_div_iff₀ (by linarith : (0 : ℝ) < 3 * a)]
  linarith

theorem cUp_eq_inv {a : ℝ} (ha : 1 / 3 < a) : cUp a = 1 / (3 * a) := by
  refine min_eq_right ?_
  rw [div_le_one (by linarith : (0 : ℝ) < 3 * a)]
  linarith

theorem integrable_slice (a : ℝ) (l u : ℝ) :
    IntervalIntegrable (DHi a - DLo0 a) volume l u :=
  ((continuous_DHi a).sub (continuous_DLo0 a)).intervalIntegrable _ _

theorem sliceB0_area {a : ℝ} (ha : 0 < a) (_ha1 : a ≤ 1) :
    ∫ c in Ico 0 (cUp a), (DHi a - DLo0 a) c = sliceB0 a := by
  have hane : a ≠ 0 := ne_of_gt ha
  have hcu : 0 < cUp a := cUp_pos ha
  rw [integral_Ico_eq_integral_Ioc, ← integral_of_le hcu.le]
  by_cases h4 : a ≤ 1 / 4
  · -- the floor clips on the whole range
    have hcU : cUp a = 1 := cUp_eq_one ha (by linarith)
    rw [hcU, sliceB0, if_pos h4]
    have hcongr : ∫ c in (0 : ℝ)..1, (DHi a - DLo0 a) c
        = ∫ c in (0 : ℝ)..1, cHi 1 (a * c) / a ^ 2 := by
      refine integral_congr fun c hc => ?_
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), mem_Icc] at hc
      exact integrand_clip ha hc.1 (by nlinarith [hc.2])
    rw [hcongr, intervalIntegral.integral_div, integral_Kc ha (by norm_num) (by linarith), Kc, Kc]
    rw [show (1 : ℝ) - 3 * (a * 0) = 1 by ring, show (1 : ℝ) - 3 * (a * 1) = 1 - 3 * a by ring,
      p52_one]
    field_simp
    ring
  · rw [not_le] at h4
    have hstar : 3 * (a * (1 / (4 * a))) = 3 / 4 := by field_simp
    have hs0 : 0 < 1 / (4 * a) := by positivity
    by_cases h3 : a ≤ 1 / 3
    · -- the floor clips only below `c = 1/(4a)`
      have hcU : cUp a = 1 := cUp_eq_one ha h3
      have hsl : 1 / (4 * a) ≤ 1 := by
        rw [div_le_one (by linarith : (0 : ℝ) < 4 * a)]; linarith
      rw [hcU, sliceB0, if_neg (not_le.2 h4), if_pos h3,
        ← integral_add_adjacent_intervals (b := 1 / (4 * a))
          (integrable_slice a _ _) (integrable_slice a _ _)]
      have hlow : ∫ c in (0 : ℝ)..(1 / (4 * a)), (DHi a - DLo0 a) c
          = ∫ c in (0 : ℝ)..(1 / (4 * a)), cHi 1 (a * c) / a ^ 2 := by
        refine integral_congr fun c hc => ?_
        rw [uIcc_of_le hs0.le, mem_Icc] at hc
        refine integrand_clip ha hc.1 ?_
        have : a * c ≤ a * (1 / (4 * a)) := by nlinarith [hc.2]
        rw [show a * (1 / (4 * a)) = 1 / 4 by field_simp] at this
        linarith
      have hhigh : ∫ c in (1 / (4 * a))..1, (DHi a - DLo0 a) c
          = ∫ c in (1 / (4 * a))..1, 4 / 27 * p32 (1 - 3 * (a * c)) / a ^ 2 := by
        refine integral_congr fun c hc => ?_
        rw [uIcc_of_le hsl, mem_Icc] at hc
        refine integrand_full ha ?_ (by nlinarith [hc.2])
        have : a * (1 / (4 * a)) ≤ a * c := by nlinarith [hc.1]
        rw [show a * (1 / (4 * a)) = 1 / 4 by field_simp] at this
        linarith
      rw [hlow, hhigh, intervalIntegral.integral_div, intervalIntegral.integral_div,
        integral_Kc ha hs0.le (by rw [hstar]; norm_num),
        integral_Wc ha hsl (by linarith), Kc, Kc, Wc, Wc, hstar]
      rw [show (1 : ℝ) - 3 * (a * 0) = 1 by ring, show (1 : ℝ) - 3 * (a * 1) = 1 - 3 * a by ring,
        show (1 : ℝ) - 3 / 4 = 1 / 4 by norm_num, p52_one, p52_quarter]
      field_simp
      ring
    · -- beyond `a = 1/3` the `c`-range itself is cut
      rw [not_le] at h3
      have hcU : cUp a = 1 / (3 * a) := cUp_eq_inv h3
      have hsl : 1 / (4 * a) ≤ 1 / (3 * a) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
      have hend : 3 * (a * (1 / (3 * a))) = 1 := by field_simp
      rw [hcU, sliceB0, if_neg (not_le.2 h4), if_neg (not_le.2 h3),
        ← integral_add_adjacent_intervals (b := 1 / (4 * a))
          (integrable_slice a _ _) (integrable_slice a _ _)]
      have hlow : ∫ c in (0 : ℝ)..(1 / (4 * a)), (DHi a - DLo0 a) c
          = ∫ c in (0 : ℝ)..(1 / (4 * a)), cHi 1 (a * c) / a ^ 2 := by
        refine integral_congr fun c hc => ?_
        rw [uIcc_of_le hs0.le, mem_Icc] at hc
        refine integrand_clip ha hc.1 ?_
        have : a * c ≤ a * (1 / (4 * a)) := by nlinarith [hc.2]
        rw [show a * (1 / (4 * a)) = 1 / 4 by field_simp] at this
        linarith
      have hhigh : ∫ c in (1 / (4 * a))..(1 / (3 * a)), (DHi a - DLo0 a) c
          = ∫ c in (1 / (4 * a))..(1 / (3 * a)), 4 / 27 * p32 (1 - 3 * (a * c)) / a ^ 2 := by
        refine integral_congr fun c hc => ?_
        rw [uIcc_of_le hsl, mem_Icc] at hc
        have h1 : a * (1 / (4 * a)) ≤ a * c := by nlinarith [hc.1]
        have h2 : a * c ≤ a * (1 / (3 * a)) := by nlinarith [hc.2]
        rw [show a * (1 / (4 * a)) = 1 / 4 by field_simp] at h1
        rw [show a * (1 / (3 * a)) = 1 / 3 by field_simp] at h2
        exact integrand_full ha (by linarith) (by linarith)
      rw [hlow, hhigh, intervalIntegral.integral_div, intervalIntegral.integral_div,
        integral_Kc ha hs0.le (by rw [hstar]; norm_num),
        integral_Wc ha hsl (by rw [hend]), Kc, Kc, Wc, Wc, hstar, hend]
      rw [show (1 : ℝ) - 3 * (a * 0) = 1 by ring, show (1 : ℝ) - 1 = 0 by norm_num,
        show (1 : ℝ) - 3 / 4 = 1 / 4 by norm_num, p52_one, p52_quarter, p52_zero]
      field_simp
      ring

/-! ## The outer `a`-integral

`u = √(1−3a)` turns each of the three regimes into a *rational* integrand in `u`,
so explicit antiderivatives exist; the `log 3` produced by the first two pieces
cancels and only `log 2` survives. -/

noncomputable def uu (a : ℝ) : ℝ := Real.sqrt (1 - 3 * a)

theorem uu_nonneg (a : ℝ) : 0 ≤ uu a := Real.sqrt_nonneg _

theorem uu_sq {a : ℝ} (h : a ≤ 1 / 3) : uu a ^ 2 = 1 - 3 * a := Real.sq_sqrt (by linarith)

theorem uu_pos {a : ℝ} (h : a < 1 / 3) : 0 < uu a := Real.sqrt_pos.2 (by linarith)

theorem uu_lt_one {a : ℝ} (h0 : 0 < a) (h : a ≤ 1 / 3) : uu a < 1 := by
  nlinarith [uu_sq h, uu_nonneg a]

theorem uu_le_half {a : ℝ} (h : 1 / 4 ≤ a) (h3 : a ≤ 1 / 3) : uu a ≤ 1 / 2 := by
  nlinarith [uu_sq h3, uu_nonneg a]

@[fun_prop]
theorem continuous_uu : Continuous uu := by
  unfold uu; fun_prop

theorem p52_uu {a : ℝ} (h : a ≤ 1 / 3) : p52 (1 - 3 * a) = uu a ^ 5 := by
  rw [← uu_sq h, p52_eq_sq_mul (uu_nonneg a)]

theorem hasDerivAt_uu {a : ℝ} (h : a < 1 / 3) :
    HasDerivAt uu (1 / (2 * uu a) * -3) a := by
  have hx : (1 : ℝ) - 3 * a ≠ 0 := by intro hc; linarith
  have hin : HasDerivAt (fun y : ℝ => 1 - 3 * y) (-3) a := by
    simpa using ((hasDerivAt_id a).const_mul 3).const_sub 1
  exact (Real.hasDerivAt_sqrt hx).comp a hin

/-! ### Piece 1: `0 ≤ a ≤ 1/4` -/

noncomputable def A1u (a : ℝ) : ℝ := (8 * uu a ^ 2 + 9 * uu a + 3) / (30 * (1 + uu a) ^ 3)

noncomputable def H1u (a : ℝ) : ℝ :=
  -(8 * uu a ^ 3 + 16 * uu a ^ 2 - uu a - 8) / (45 * (1 + uu a) ^ 2) + Real.log (1 + uu a) / 3

theorem continuous_A1u : Continuous A1u := by
  unfold A1u
  refine Continuous.div (by fun_prop) (by fun_prop) fun a => ?_
  have := uu_nonneg a
  positivity

theorem continuous_H1u : Continuous H1u := by
  unfold H1u
  have hc : Continuous fun a : ℝ => 1 + uu a := by fun_prop
  refine Continuous.add (Continuous.div (by fun_prop) (by fun_prop) fun a => ?_)
    ((hc.log fun a => ?_).div_const 3)
  · have := uu_nonneg a; positivity
  · have := uu_nonneg a; exact ne_of_gt (by linarith)

theorem hasDerivAt_H1u {a : ℝ} (h : a < 1 / 3) : HasDerivAt H1u (A1u a) a := by
  set u := uu a with hu
  have hu0 : 0 < u := uu_pos h
  have hu1 : (0 : ℝ) < 1 + u := by linarith
  have hd := hasDerivAt_uu h
  rw [← hu] at hd
  have hnum : HasDerivAt (fun x => -(8 * uu x ^ 3 + 16 * uu x ^ 2 - uu x - 8))
      (-(8 * (3 * u ^ 2) + 16 * (2 * u) - 1) * (1 / (2 * u) * -3)) a := by
    have := (((hd.fun_pow 3).const_mul 8).add ((hd.fun_pow 2).const_mul 16)).sub hd
    have h2 := (this.sub_const 8).neg
    refine h2.congr_deriv ?_
    ring
  have hden : HasDerivAt (fun x => 45 * (1 + uu x) ^ 2)
      (45 * (2 * (1 + u)) * (1 / (2 * u) * -3)) a := by
    have := ((hd.const_add 1).fun_pow 2).const_mul 45
    refine this.congr_deriv ?_
    ring
  have hlog : HasDerivAt (fun x => Real.log (1 + uu x) / 3)
      ((1 / (2 * u) * -3) / (1 + u) / 3) a :=
    (((hd.const_add 1).log (by linarith)).div_const 3)
  have hdiv := hnum.div hden (by positivity)
  have hres := hdiv.add hlog
  refine hres.congr_deriv ?_
  rw [A1u, ← hu]
  field_simp
  ring

theorem integral_A1u : ∫ a in (0 : ℝ)..(1 / 4), A1u a = 191 / 1620 + Real.log 3 / 3
    - 2 * Real.log 2 / 3 := by
  rw [integral_eq_sub_of_hasDerivAt_of_le (by norm_num) continuous_H1u.continuousOn
    (fun a ha => hasDerivAt_H1u (by linarith [ha.2])) (continuous_A1u.intervalIntegrable _ _)]
  have h4 : uu (1 / 4 : ℝ) = 1 / 2 := by
    unfold uu
    rw [show (1 : ℝ) - 3 * (1 / 4) = (1 / 2) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have h0 : uu (0 : ℝ) = 1 := by
    unfold uu; rw [show (1 : ℝ) - 3 * 0 = 1 by norm_num]; exact Real.sqrt_one
  rw [H1u, H1u, h4, h0]
  rw [show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num, show (1 : ℝ) + 1 = 2 by norm_num,
    show Real.log (3 / 2 : ℝ) = Real.log 3 - Real.log 2 by
      rw [Real.log_div (by norm_num) (by norm_num)]]
  norm_num
  ring

/-! ### Piece 2: `1/4 ≤ a ≤ 1/3` -/

noncomputable def A2u (a : ℝ) : ℝ := (1 / 480 - 8 / 405 * uu a ^ 5) / a ^ 3

noncomputable def H2u (a : ℝ) : ℝ :=
  -(-1152 * uu a ^ 3 + 896 * uu a + 27) / (25920 * a ^ 2) - 16 / 45 * uu a
    - Real.log (1 - uu a) / 3 + Real.log (1 + uu a) / 3

theorem hasDerivAt_H2u {a : ℝ} (h0 : 0 < a) (h : a < 1 / 3) : HasDerivAt H2u (A2u a) a := by
  have hu0 : 0 < uu a := uu_pos h
  have hu2 : uu a ^ 2 = 1 - 3 * a := uu_sq h.le
  have hu1 : uu a < 1 := uu_lt_one h0 h.le
  have hd := hasDerivAt_uu h
  have hnum : HasDerivAt (fun x => -(-1152 * uu x ^ 3 + 896 * uu x + 27))
      (-(-1152 * (3 * uu a ^ 2) + 896) * (1 / (2 * uu a) * -3)) a := by
    have h1 := (((hd.fun_pow 3).const_mul (-1152 : ℝ)).add (hd.const_mul (896 : ℝ))).add_const 27
    refine h1.neg.congr_deriv ?_
    ring
  have hden : HasDerivAt (fun x : ℝ => 25920 * x ^ 2) (25920 * (2 * a)) a := by
    simpa using ((hasDerivAt_id a).fun_pow 2).const_mul (25920 : ℝ)
  have hq := hnum.div hden (by positivity)
  have hlin : HasDerivAt (fun x => 16 / 45 * uu x) (16 / 45 * (1 / (2 * uu a) * -3)) a :=
    hd.const_mul _
  have hlog1 : HasDerivAt (fun x => Real.log (1 - uu x) / 3)
      (-(1 / (2 * uu a) * -3) / (1 - uu a) / 3) a :=
    ((hd.const_sub 1).log (by linarith)).div_const 3
  have hlog2 : HasDerivAt (fun x => Real.log (1 + uu x) / 3)
      ((1 / (2 * uu a) * -3) / (1 + uu a) / 3) a :=
    ((hd.const_add 1).log (by linarith)).div_const 3
  have hres := ((hq.sub hlin).sub hlog1).add hlog2
  refine hres.congr_deriv ?_
  rw [A2u]
  set u := uu a with hu
  clear_value u
  have ha' : a = (1 - u ^ 2) / 3 := by linarith
  rw [ha']
  have e1 : (1 : ℝ) - u ≠ 0 := by intro hc; nlinarith
  have e2 : (1 : ℝ) + u ≠ 0 := by intro hc; nlinarith
  have e3 : u ≠ 0 := ne_of_gt hu0
  have e4 : (1 : ℝ) - u ^ 2 ≠ 0 := by intro hc; nlinarith
  field_simp
  ring

theorem continuousOn_H2u : ContinuousOn H2u (Icc (1 / 4 : ℝ) (1 / 3)) := by
  refine ContinuousOn.add (ContinuousOn.sub (ContinuousOn.sub ?_ (by fun_prop)) ?_) ?_
  · refine ContinuousOn.div (by fun_prop) (by fun_prop) fun a ha => ?_
    have : (1 : ℝ) / 4 ≤ a := ha.1
    positivity
  · refine ContinuousOn.div_const (ContinuousOn.log (by fun_prop) fun a ha => ?_) 3
    have := uu_le_half ha.1 ha.2
    exact ne_of_gt (by linarith)
  · refine ContinuousOn.div_const (ContinuousOn.log (by fun_prop) fun a ha => ?_) 3
    have := uu_nonneg a
    exact ne_of_gt (by linarith)

theorem continuousOn_A2u : ContinuousOn A2u (Icc (1 / 4 : ℝ) (1 / 3)) := by
  refine ContinuousOn.div (by fun_prop) (by fun_prop) fun a ha => ?_
  have : (1 : ℝ) / 4 ≤ a := ha.1
  positivity

theorem integral_A2u :
    ∫ a in (1 / 4 : ℝ)..(1 / 3), A2u a = 9661 / 25920 - Real.log 3 / 3 := by
  rw [integral_eq_sub_of_hasDerivAt_of_le (by norm_num) continuousOn_H2u
    (fun a ha => hasDerivAt_H2u (by linarith [ha.1]) ha.2)
    (continuousOn_A2u.intervalIntegrable_of_Icc (by norm_num))]
  have h3 : uu (1 / 3 : ℝ) = 0 := by
    unfold uu; rw [show (1 : ℝ) - 3 * (1 / 3) = 0 by norm_num]; exact Real.sqrt_zero
  have h4 : uu (1 / 4 : ℝ) = 1 / 2 := by
    unfold uu
    rw [show (1 : ℝ) - 3 * (1 / 4) = (1 / 2) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [H2u, H2u, h3, h4]
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num,
    show (1 : ℝ) - 0 = 1 by norm_num, show (1 : ℝ) + 0 = 1 by norm_num, Real.log_one,
    show Real.log (1 / 2 : ℝ) = -Real.log 2 by
      rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.log_inv],
    show Real.log (3 / 2 : ℝ) = Real.log 3 - Real.log 2 by
      rw [Real.log_div (by norm_num) (by norm_num)]]
  norm_num
  ring

/-! ### Piece 3: `1/3 ≤ a ≤ 1` -/

noncomputable def A3u (a : ℝ) : ℝ := 1 / (480 * a ^ 3)

noncomputable def H3u (a : ℝ) : ℝ := -1 / (960 * a ^ 2)

theorem hasDerivAt_H3u {a : ℝ} (h0 : 0 < a) : HasDerivAt H3u (A3u a) a := by
  have hden : HasDerivAt (fun x : ℝ => 960 * x ^ 2) (960 * (2 * a)) a := by
    simpa using ((hasDerivAt_id a).fun_pow 2).const_mul (960 : ℝ)
  have h := (hasDerivAt_const a (-1 : ℝ)).div hden (by positivity)
  refine h.congr_deriv ?_
  rw [A3u]
  field_simp
  ring

theorem continuousOn_H3u : ContinuousOn H3u (Icc (1 / 3 : ℝ) 1) := by
  refine ContinuousOn.div (by fun_prop) (by fun_prop) fun a ha => ?_
  have : (1 : ℝ) / 3 ≤ a := ha.1
  positivity

theorem continuousOn_A3u : ContinuousOn A3u (Icc (1 / 3 : ℝ) 1) := by
  refine ContinuousOn.div (by fun_prop) (by fun_prop) fun a ha => ?_
  have : (1 : ℝ) / 3 ≤ a := ha.1
  positivity

theorem integral_A3u : ∫ a in (1 / 3 : ℝ)..1, A3u a = 1 / 120 := by
  rw [integral_eq_sub_of_hasDerivAt_of_le (by norm_num) continuousOn_H3u
    (fun a ha => hasDerivAt_H3u (by linarith [ha.1]))
    (continuousOn_A3u.intervalIntegrable_of_Icc (by norm_num))]
  rw [H3u, H3u]
  norm_num

/-! ### The three regimes of `sliceB0` in terms of `u` -/

theorem sliceB0_eq_A1u {a : ℝ} (h0 : 0 < a) (h : a ≤ 1 / 4) : sliceB0 a = A1u a := by
  have h3 : a ≤ 1 / 3 := by linarith
  have hu2 := uu_sq h3
  have hu0 : 0 < uu a := uu_pos (by linarith)
  have hu1 : uu a < 1 := uu_lt_one h0 h3
  rw [sliceB0, if_pos h, p52_uu h3, A1u]
  set u := uu a with hu
  clear_value u
  have ha' : a = (1 - u ^ 2) / 3 := by linarith
  rw [ha']
  have e1 : (1 : ℝ) - u ≠ 0 := by intro hc; nlinarith
  have e2 : (1 : ℝ) + u ≠ 0 := by intro hc; nlinarith
  have e3 : u ≠ 0 := ne_of_gt hu0
  have e4 : (1 : ℝ) - u ^ 2 ≠ 0 := by intro hc; nlinarith
  field_simp
  ring

theorem sliceB0_eq_A2u {a : ℝ} (h4 : ¬ a ≤ 1 / 4) (h : a ≤ 1 / 3) : sliceB0 a = A2u a := by
  rw [sliceB0, if_neg h4, if_pos h, p52_uu h, A2u]

theorem sliceB0_eq_A3u {a : ℝ} (h4 : ¬ a ≤ 1 / 4) (h : ¬ a ≤ 1 / 3) : sliceB0 a = A3u a := by
  rw [sliceB0, if_neg h4, if_neg h, A3u]

/-! ## Assembly: `vol₃(FaceB0) = 479/960 − (2/3) log 2` -/

theorem sliceB0_nonneg {a : ℝ} (h0 : 0 < a) : 0 ≤ sliceB0 a := by
  by_cases h4 : a ≤ 1 / 4
  · rw [sliceB0_eq_A1u h0 h4, A1u]
    have := uu_nonneg a
    positivity
  · by_cases h3 : a ≤ 1 / 3
    · rw [sliceB0_eq_A2u h4 h3, A2u]
      have hh : uu a ≤ 1 / 2 := uu_le_half (by linarith [not_le.1 h4]) h3
      have h0' : 0 ≤ uu a := uu_nonneg a
      have h5 : uu a ^ 5 ≤ 1 / 32 := by
        calc uu a ^ 5 ≤ (1 / 2 : ℝ) ^ 5 := by gcongr
          _ = 1 / 32 := by norm_num
      have : (0 : ℝ) ≤ 1 / 480 - 8 / 405 * uu a ^ 5 := by nlinarith
      positivity
    · rw [sliceB0_eq_A3u h4 h3, A3u]
      positivity

theorem intervalIntegrable_sliceB0_1 : IntervalIntegrable sliceB0 volume 0 (1 / 4) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  refine IntegrableOn.congr_fun
    (continuous_A1u.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (fun a ha => (sliceB0_eq_A1u ha.1 ha.2).symm) measurableSet_Ioc

theorem intervalIntegrable_sliceB0_2 : IntervalIntegrable sliceB0 volume (1 / 4) (1 / 3) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  refine IntegrableOn.congr_fun
    (continuousOn_A2u.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (fun a ha => (sliceB0_eq_A2u (not_le.2 ha.1) ha.2).symm) measurableSet_Ioc

theorem intervalIntegrable_sliceB0_3 : IntervalIntegrable sliceB0 volume (1 / 3) 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  refine IntegrableOn.congr_fun
    (continuousOn_A3u.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (fun a ha => (sliceB0_eq_A3u (not_le.2 (by linarith [ha.1])) (not_le.2 ha.1)).symm)
    measurableSet_Ioc

theorem integral_sliceB0 :
    ∫ a in (0 : ℝ)..1, sliceB0 a = 479 / 960 - 2 / 3 * Real.log 2 := by
  rw [← integral_add_adjacent_intervals intervalIntegrable_sliceB0_1
      (intervalIntegrable_sliceB0_2.trans intervalIntegrable_sliceB0_3),
    ← integral_add_adjacent_intervals intervalIntegrable_sliceB0_2 intervalIntegrable_sliceB0_3]
  have e1 : ∫ a in (0 : ℝ)..(1 / 4), sliceB0 a = ∫ a in (0 : ℝ)..(1 / 4), A1u a := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun a ha => ?_)
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1 / 4)] at ha
    exact sliceB0_eq_A1u ha.1 ha.2
  have e2 : ∫ a in (1 / 4 : ℝ)..(1 / 3), sliceB0 a = ∫ a in (1 / 4 : ℝ)..(1 / 3), A2u a := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun a ha => ?_)
    rw [Set.uIoc_of_le (by norm_num : (1/4:ℝ) ≤ 1 / 3)] at ha
    exact sliceB0_eq_A2u (not_le.2 ha.1) ha.2
  have e3 : ∫ a in (1 / 3 : ℝ)..1, sliceB0 a = ∫ a in (1 / 3 : ℝ)..1, A3u a := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun a ha => ?_)
    rw [Set.uIoc_of_le (by norm_num : (1/3:ℝ) ≤ 1)] at ha
    exact sliceB0_eq_A3u (not_le.2 (by linarith [ha.1])) (not_le.2 ha.1)
  rw [e1, e2, e3, integral_A1u, integral_A2u, integral_A3u]
  ring

theorem volume_slice_FaceB0 {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    volume (Prod.mk a ⁻¹' FaceB0) = ENNReal.ofReal (sliceB0 a) := by
  rw [volume_sliceB_eq ha ha1,
    show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
    volume_regionBetween_eq_integral
      ((continuous_DLo0 a).continuousOn.integrableOn_Icc.mono_set Ico_subset_Icc_self)
      ((continuous_DHi a).continuousOn.integrableOn_Icc.mono_set Ico_subset_Icc_self)
      measurableSet_Ico ?_, sliceB0_area ha ha1]
  intro c hc
  have hB0 : 0 ≤ a * c := mul_nonneg ha.le hc.1
  have hB3 : 3 * (a * c) ≤ 1 := mul_cUp_le ha hc.2.le
  have hnn : (0 : ℝ) ≤ 1 ^ 2 - 3 * (a * c) := by linarith
  have h1 : max (cLo 1 (a * c)) 0 ≤ cHi 1 (a * c) :=
    max_le (cLo_le_cHi 1 (a * c) hnn) (cHi_nonneg (by norm_num) hB0 (by linarith))
  have ha2 : (0 : ℝ) < a ^ 2 := by positivity
  have hdiv : max (cLo 1 (a * c)) 0 / a ^ 2 ≤ cHi 1 (a * c) / a ^ 2 := by gcongr
  simpa [DLo0, DHi] using hdiv

theorem volume_FaceB0 :
    volume FaceB0 = ENNReal.ofReal (479 / 960 - 2 / 3 * Real.log 2) := by
  have hmeas : MeasurableSet FaceB0 := by
    have h : FaceB0 = ((Prod.fst ⁻¹' Icc (0 : ℝ) 1)
        ∩ ((fun p : ℝ × ℝ × ℝ => p.2.1) ⁻¹' Icc (0 : ℝ) 1)
        ∩ ((fun p : ℝ × ℝ × ℝ => p.2.2) ⁻¹' Icc (0 : ℝ) 1))
        ∩ {p : ℝ × ℝ × ℝ | 0 < Δ₄ p.1 1 p.2.1 p.2.2} := by
      ext p; simp only [FaceB0, mem_ofPred_eq, mem_inter_iff, mem_preimage]; tauto
    rw [h]
    refine (((measurable_fst measurableSet_Icc).inter
      ((measurable_fst.comp measurable_snd) measurableSet_Icc)).inter
      ((measurable_snd.comp measurable_snd) measurableSet_Icc)).inter ?_
    refine measurableSet_lt measurable_const ?_
    exact (by unfold Δ₄; fun_prop : Continuous fun p : ℝ × ℝ × ℝ => Δ₄ p.1 1 p.2.1 p.2.2).measurable
  rw [show (volume : Measure (ℝ × ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
    Measure.prod_apply hmeas]
  have hfun : (fun a => (volume : Measure (ℝ × ℝ)) (Prod.mk a ⁻¹' FaceB0))
      =ᵐ[volume] (Ioc (0 : ℝ) 1).indicator (fun a => ENNReal.ofReal (sliceB0 a)) := by
    refine Filter.eventuallyEq_of_mem (compl_mem_ae_iff.2 (Real.volume_singleton (a := 0)))
      fun a ha => ?_
    have hane : a ≠ 0 := ha
    by_cases hmem : a ∈ Ioc (0 : ℝ) 1
    · rw [Set.indicator_of_mem hmem]
      exact volume_slice_FaceB0 hmem.1 hmem.2
    · rw [Set.indicator_of_notMem hmem]
      have hempty : Prod.mk a ⁻¹' FaceB0 = ∅ := by
        ext ⟨c, d⟩
        simp only [mem_preimage, FaceB0, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        intro h
        exact absurd (show a ∈ Ioc (0:ℝ) 1 from ⟨lt_of_le_of_ne h.1 (Ne.symm hane), h.2⟩) hmem
      rw [hempty, measure_empty]
  rw [lintegral_congr_ae hfun, lintegral_indicator measurableSet_Ioc]
  have hint : IntegrableOn sliceB0 (Ioc (0 : ℝ) 1) := by
    have h1 := intervalIntegrable_sliceB0_1
    have h2 := intervalIntegrable_sliceB0_2
    have h3 := intervalIntegrable_sliceB0_3
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at h1 h2 h3
    have h12 : IntegrableOn sliceB0 (Ioc (0:ℝ) (1/3)) := by
      rw [← Set.Ioc_union_Ioc_eq_Ioc (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num : (1:ℝ)/4 ≤ 1/3)]
      exact h1.union h2
    rw [← Set.Ioc_union_Ioc_eq_Ioc (by norm_num : (0:ℝ) ≤ 1/3) (by norm_num : (1:ℝ)/3 ≤ 1)]
    exact h12.union h3
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] sliceB0 := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall fun a ha => sliceB0_nonneg ha.1
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  rw [← integral_of_le (by norm_num : (0:ℝ) ≤ 1), integral_sliceB0]

end NonmonicCubic
