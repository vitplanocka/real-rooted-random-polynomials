/-
# Stage 4 — Theorem 3, the elementary route

## Which route, and a correction to the brief

`TASK.md` steers towards "`VERDICT.md`'s route 1 (no face decomposition, no
divergence theorem) … integrate `a` out first in closed form, then σ, then b …
every step is `intervalIntegral` of an explicit piecewise-elementary function".

**That is a misreading of the reference, and following it would not produce a
proof.**  Route 1 is a *numerical* route.  Only its innermost `a`-integral is in
closed form; the remaining double integral over `(b, σ)` is evaluated by
tanh–sinh / Gauss–Legendre quadrature with hand-placed panel breakpoints
(`reference/route1_closed_a.py`, and `VERDICT.md`'s table row "route 1 — the
leading-coefficient / V(t) route … `0.21801049620261477102`", i.e. 19 digits, not
a closed form).  `VERDICT.md` says so explicitly in "The stretch goal, and a
negative result worth recording": integrating in that order "leaves integrals of
algebraic functions of the roots of a cubic whose coefficients move with the
outer variable, which is not elementary in general", with PSLQ finding no
closed form for `V(t)` at `t = 1/2` or `1/3`.

The **only** closed-form derivation in the reference is route 2:
`P = (V(1) + S_b)/16`, obtained by cutting the 4-dimensional cone with the faces
of the cube.  So route 2 is what is formalized here.

## The cone step does *not* need the divergence theorem

`TASK.md` avoids route 2 because it "needs Stokes'/divergence-theorem machinery
on a region with a non-smooth (cusped) boundary".  That concern does not apply:
the face identity is a **change of variables**, not a boundary integral.

For a cone `R ⊆ ℝⁿ` (invariant under `x ↦ λx`, `λ > 0`), partition
`[-1,1]ⁿ \ {0}` by which coordinate attains `max_j |x_j|` and with which sign.
On the piece where `x_n = max_j |x_j| > 0`, the map
`(t, y) ∈ (0,1] × [-1,1]^{n-1} ↦ (t y, t)` is a bijection with Jacobian `t^{n-1}`,
so by homogeneity of `R`

    vol(R ∩ that piece) = ∫₀¹ t^{n-1} (∫_{[-1,1]^{n-1}} 1_R(y, 1) dy) dt
                        = (1/n) · vol_{n-1}{ y ∈ [-1,1]^{n-1} : (y,1) ∈ R }.

Summing the `2n` pieces (they overlap only in a null set of ties) gives
`vol(R ∩ [-1,1]ⁿ) = (1/n) Σ_faces S_face`.  For `n = 4`, with central symmetry
(`Δ₄_neg`) pairing opposite faces and coefficient reversal (`Δ₄_reverse`) giving
`S_a = S_d`, `S_b = S_c`, this is `vol₄ = S_a + S_b`.

That is `volume_T3Set_eq_faces` below, and it **is proved** — see
`volume_conePiece1`, the radial identity, which is Fubini plus the scaling law
`vol₃(t·E) = t³ vol₃(E)`.  No change-of-variables theorem in `ℝ⁴`, and above all
no Stokes, was needed.

## What is proved here

* `Δ₄_completeSquare` — the degree-4 analogue of `Basic.lean`'s key identity.
* `Δ₄_face_b_pos_iff`, `Δ₄_face_b_neg` — the exact `d`-band on the face `b = 1`,
  reproducing `VERDICT.md`'s `K₊`, `K₋`, `u = 27a²` **character for character**.
* `Kp_add_Km` — `K₊ + K₋ = 4s³`.
* `L1`, `L2_clips`, `L2_no_clip`, `L2_alphaM_lt_one` — the two clipping lemmas.
* `Fs_branches_agree` — `F` is continuous at `s = 2/3`, both branches `11264/18225`.
* `Fs_eq_face_integral` — **`F(s)` is the `a`-integral of the clipped band
  length**, both regimes, `0 < s < 2`, `s ≠ 1`.  (Proving it turned up that the
  statement needs `s ≠ 1`: at `s = 1` the integral genuinely diverges.)
* `integral_s_Fs` — **the closed form of the outer integral**,
  `∫₀² s F(s) ds = 727/270 − (5/8) log 3`, hence
  `S_b = (4/3)∫₀² s F(s) ds = 1454/405 − (5/6) log 3` (`volume_FaceB`).
  This is where Theorem 3's `log 3` actually comes
  from.  Proved by putting both branches of `F` in `a₀`-free, `α₋`-free form
  (`s_mul_Fs_le`, `s_mul_Fs_gt`), exhibiting explicit antiderivatives `H1`, `H2`,
  and applying the FTC — with `H2` continuous through the integrable `log`
  singularity at `s = 1` thanks to `Real.continuous_mul_log`.  The `log 5` that
  each half produces separately cancels in the sum, a useful internal check.
* `lintegral_faceRegion_swap` — **the Tonelli swap**: exchanging the order of
  integration over `faceRegion = {(a,s) : a ∈ (0,1], s ∈ (0,2), a₀ s ≤ a}`, so
  that `a` is integrated *first at fixed `s`* and `F(s)` can appear at all.
  This is `VERDICT.md`'s "this is the move".
* `post_swap_eval` — everything after the swap: the inner integral is
  `(2s/3)·F(s)` (`inner_lintegral_eq`, using `Fs_eq_face_integral`) and the outer
  one is `(2/3)∫₀² s F(s) ds` (using `integral_s_Fs`), giving
  `= ENNReal.ofReal ((2/3)∫₀² s F(s) ds)`.
* `volume_FaceB_eq_pre_swap` — the pre-swap identity: the `(a,c,d) ↦ (-a,-c,d)`
  symmetry (factor `2`), Fubini in `a`, the `(c,d)`-slice as a region between the
  clipped band edges (`volume_sliceB`, using `Δ₄_face_b_pos_iff` and `L1`), and
  the substitution `c = (1-s²)/(3a)` (`integral_c_eq_integral_s`).
* **`volume_FaceB` — `S_b = 1454/405 - (5/6) log 3`.**  Together with
  `volume_FaceA` (`= V(1)`, from the proved Theorem 1), both ingredients of
  Theorem 3.
* `volume_FaceA` — `S_a = V(1) = 766/1215 + log 3/6`, **derived from the fully
  proved Theorem 1** via `Δ₄_one`.
* `volume_conePiece1` — **the radial identity** (see above), and
  `volume_conePiece2` plus the six symmetry transports for the other pieces.
* `volume_T3Set_sum` — the eight pieces partition `[-1,1]⁴` off the null set
  `tieCover` of the twelve hyperplanes `x_i = ±x_j`.
* `theorem3_of_faces`, `volume_T3Set_eq_faces`, and finally **`theorem3` and
  `theorem3_probability`**.

## Status

**Nothing in this file is `sorry`d.**  Together with `DiscriminantRootCount.lean`
(which proves `Δ₄ > 0 ↔ three distinct real roots`), Theorem 3 is machine-checked
end to end as a statement about roots.
-/
import NonmonicCubic.DiscriminantRootCount

namespace NonmonicCubic

open Real Set MeasureTheory intervalIntegral
open scoped Pointwise

/-! ## The degree-4 completed square -/

/-- **The key identity for the general cubic**, the exact analogue of
`disc_completeSquare`.  Pure `ring`.  Setting `a = 1` recovers the `Δ₃` version. -/
theorem Δ₄_completeSquare (a b c d : ℝ) :
    -27 * a ^ 2 * Δ₄ a b c d
      = (27 * a ^ 2 * d - 9 * a * b * c + 2 * b ^ 3) ^ 2 - 4 * (b ^ 2 - 3 * a * c) ^ 3 := by
  unfold Δ₄; ring

/-! ## The `d`-band on the face `b = 1` -/

/-- `K₊ = (s−1)²(2s+1)` — the top of the `d`-band, scaled by `u = 27a²`. -/
def Kp (s : ℝ) : ℝ := (s - 1) ^ 2 * (2 * s + 1)

/-- `K₋ = (s+1)²(2s−1)` — the bottom of the `d`-band, scaled by `u = 27a²`. -/
def Km (s : ℝ) : ℝ := (s + 1) ^ 2 * (2 * s - 1)

/-- `K₊ + K₋ = 4s³`.  This is the identity that makes the awkward term
`−K₊/(2K₋) + 2s³/K₋` collapse to the constant `1/2`. -/
theorem Kp_add_Km (s : ℝ) : Kp s + Km s = 4 * s ^ 3 := by unfold Kp Km; ring

/-- **The band on the face `b = 1`.**  With `s = √(1−3ac)` and `u = 27a²`, the
admissible `d` are exactly `−K₋/u < d·… `, stated here in the cleared form
`−K₋ < 27a²d < K₊`, matching `VERDICT.md`'s `[−K₋/u, K₊/u]`. -/
theorem Δ₄_face_b_pos_iff {a c s d : ℝ} (ha : a ≠ 0) (hs : 0 ≤ s)
    (hsq : s ^ 2 = 1 - 3 * a * c) :
    0 < Δ₄ a 1 c d ↔ -Km s < 27 * a ^ 2 * d ∧ 27 * a ^ 2 * d < Kp s := by
  have ha2 : 0 < a ^ 2 := by positivity
  have hkey := Δ₄_completeSquare a 1 c d
  have hcube : (1 - 3 * a * c) ^ 3 = (s ^ 3) ^ 2 := by rw [← hsq]; ring
  have hexp : -27 * a ^ 2 * Δ₄ a 1 c d
      = (27 * a ^ 2 * d + 3 * s ^ 2 - 1) ^ 2 - (2 * s ^ 3) ^ 2 := by
    rw [hkey]
    have h9 : 9 * a * 1 * c = 3 - 3 * s ^ 2 := by rw [hsq]; ring
    rw [show (27 * a ^ 2 * d - 9 * a * 1 * c + 2 * (1 : ℝ) ^ 3)
        = 27 * a ^ 2 * d + 3 * s ^ 2 - 1 by rw [h9]; ring,
      show (1 : ℝ) ^ 2 - 3 * a * c = s ^ 2 by rw [hsq]; ring]
    ring
  have hKp : Kp s = 1 - 3 * s ^ 2 + 2 * s ^ 3 := by unfold Kp; ring
  have hKm : -Km s = 1 - 3 * s ^ 2 - 2 * s ^ 3 := by unfold Km; ring
  constructor
  · intro hpos
    have h : (27 * a ^ 2 * d + 3 * s ^ 2 - 1) ^ 2 < (2 * s ^ 3) ^ 2 := by nlinarith
    have habs := abs_lt_of_sq_lt_sq' h (by positivity)
    rw [hKp, hKm]
    constructor <;> linarith [habs.1, habs.2]
  · rintro ⟨h1, h2⟩
    rw [hKp] at h2
    rw [hKm] at h1
    nlinarith

/-- Above the parabola `b² = 3ac` (here `1 = 3ac`) the discriminant is negative:
one real root. -/
theorem Δ₄_face_b_neg {a c d : ℝ} (ha : a ≠ 0) (h : 1 - 3 * a * c < 0) :
    Δ₄ a 1 c d < 0 := by
  have ha2 : 0 < a ^ 2 := by positivity
  have hkey := Δ₄_completeSquare a 1 c d
  have hsq : (0 : ℝ) ≤ (27 * a ^ 2 * d - 9 * a * 1 * c + 2 * 1 ^ 3) ^ 2 := sq_nonneg _
  have hcube : ((1 : ℝ) ^ 2 - 3 * a * c) ^ 3 < 0 := by
    refine (Odd.pow_neg_iff (by decide)).2 ?_
    linarith
  nlinarith

/-! ## The two clipping lemmas `L1`, `L2` -/

/-- `a₀ = |s²−1|/3`, the smallest `a` compatible with `|c| ≤ 1` at this `s`. -/
noncomputable def a0 (s : ℝ) : ℝ := |s ^ 2 - 1| / 3

/-- `α₋ = √(K₋/27)`, the `a` below which the *bottom* of the band leaves `[-1,1]`. -/
noncomputable def alphaM (s : ℝ) : ℝ := Real.sqrt (Km s / 27)

theorem a0_sq (s : ℝ) : a0 s ^ 2 = (s ^ 2 - 1) ^ 2 / 9 := by
  unfold a0; rw [div_pow, sq_abs]; norm_num

/-- **L1 — the band never clips above.**  `α₊ ≤ a₀`, i.e. `K₊/27 ≤ a₀²`, which
after clearing reduces to `(s−1)²(3s²+4s+2) ≥ 0`; the quadratic `3s²+4s+2` has
negative discriminant, so this holds for **every** real `s`.  (`VERDICT.md`
states it as `2s+1 < 3(s+1)²`, the same inequality after dividing by `(s−1)²`.) -/
theorem L1 (s : ℝ) : Kp s / 27 ≤ a0 s ^ 2 := by
  rw [a0_sq]
  unfold Kp
  nlinarith [sq_nonneg (s - 1), sq_nonneg (3 * s + 2), sq_nonneg s,
    mul_nonneg (sq_nonneg (s - 1)) (sq_nonneg (3 * s + 2))]

/-- **L2, clipping half.**  For `2/3 < s < 2` the bottom of the band *does* clip:
`α₋ > a₀`, which reduces to `(3s−2)(s−2) < 0`. -/
theorem L2_clips {s : ℝ} (h1 : 2 / 3 < s) (h2 : s < 2) : a0 s ^ 2 < Km s / 27 := by
  rw [a0_sq]
  unfold Km
  nlinarith [sq_nonneg (s + 1), mul_pos (by linarith : (0:ℝ) < 3 * s - 2)
    (by linarith : (0:ℝ) < 2 - s), sq_nonneg s]

/-- **L2, no-clipping half.**  For `0 < s ≤ 2/3` the bottom does not clip. -/
theorem L2_no_clip {s : ℝ} (h1 : 0 < s) (h2 : s ≤ 2 / 3) : Km s / 27 ≤ a0 s ^ 2 := by
  rw [a0_sq]
  unfold Km
  nlinarith [sq_nonneg (s + 1), mul_nonneg (by linarith : (0:ℝ) ≤ 2 - 3 * s)
    (by linarith : (0:ℝ) ≤ 2 - s), sq_nonneg s]

/-- **L2, the upper endpoint.**  `α₋ < 1 ↔ s < 2`, i.e. `(s+1)²(2s−1) < 27`,
with equality exactly at `s = 2`. -/
theorem L2_alphaM_lt_one {s : ℝ} (hs : 0 ≤ s) : Km s < 27 ↔ s < 2 := by
  unfold Km
  constructor
  · intro h; nlinarith [sq_nonneg (s - 2), sq_nonneg (s + 1)]
  · intro h; nlinarith [sq_nonneg (s - 2), sq_nonneg (s + 1)]

/-! ## `F(s)` -/

/-- `F(s) = ∫_{a₀}^1 (clipped band length)/a da`, in the closed form of
`reference/VERDICT.md`:

    F(s) = (2s³/27)(1/a₀² − 1)                      for s ≤ 2/3
    F(s) = K₊/(54a₀²) + 1/2 + log(α₋/a₀) − 2s³/27   for 2/3 < s < 2
-/
noncomputable def Fs (s : ℝ) : ℝ :=
  if s ≤ 2 / 3 then 2 * s ^ 3 / 27 * (1 / a0 s ^ 2 - 1)
  else Kp s / (54 * a0 s ^ 2) + 1 / 2 + Real.log (alphaM s / a0 s) - 2 * s ^ 3 / 27

/-- **PROVED.**  `F` is continuous at the branch point `s = 2/3`: both formulas
give `11264/18225`, exactly as `reference/VERDICT.md` records.  At `s = 2/3` one
has `α₋ = a₀ = 5/27`, so the `log` term vanishes. -/
theorem Fs_branches_agree :
    2 * (2 / 3 : ℝ) ^ 3 / 27 * (1 / a0 (2 / 3) ^ 2 - 1) = 11264 / 18225 ∧
    Kp (2 / 3) / (54 * a0 (2 / 3) ^ 2) + 1 / 2
      + Real.log (alphaM (2 / 3) / a0 (2 / 3)) - 2 * (2 / 3 : ℝ) ^ 3 / 27
      = 11264 / 18225 := by
  have ha0 : a0 (2 / 3 : ℝ) = 5 / 27 := by
    unfold a0
    rw [show ((2 : ℝ) / 3) ^ 2 - 1 = -(5 / 9) by norm_num, abs_neg,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 5 / 9)]
    norm_num
  have halpha : alphaM (2 / 3 : ℝ) = 5 / 27 := by
    unfold alphaM Km
    rw [show ((2 : ℝ) / 3 + 1) ^ 2 * (2 * (2 / 3) - 1) / 27 = (5 / 27) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  refine ⟨by rw [ha0]; norm_num, ?_⟩
  rw [ha0, halpha]
  norm_num [Kp]

/-! ## The faces of the 4-cube -/

/-- `S_a`: the face `a = 1`, i.e. the monic cubic — this is Theorem 1's set. -/
def FaceA : Set (ℝ × ℝ × ℝ) :=
  {q | q.1 ∈ Icc (-1 : ℝ) 1 ∧ q.2.1 ∈ Icc (-1 : ℝ) 1 ∧ q.2.2 ∈ Icc (-1 : ℝ) 1 ∧
    0 < Δ₄ 1 q.1 q.2.1 q.2.2}

/-- `S_b`: the face `b = 1`, the genuinely new 3-dimensional problem. -/
def FaceB : Set (ℝ × ℝ × ℝ) :=
  {q | q.1 ∈ Icc (-1 : ℝ) 1 ∧ q.2.1 ∈ Icc (-1 : ℝ) 1 ∧ q.2.2 ∈ Icc (-1 : ℝ) 1 ∧
    0 < Δ₄ q.1 1 q.2.1 q.2.2}

/-- **PROVED.**  The `a = 1` face is literally Theorem 1's region. -/
theorem FaceA_eq_T1Set : FaceA = T1Set := by
  ext q
  simp only [FaceA, T1Set, mem_ofPred_eq, Δ₄_one]

/-- **PROVED, from Theorem 1.**  `S_a = V(1) = 766/1215 + log 3 / 6`. -/
theorem volume_FaceA : volume FaceA = ENNReal.ofReal (766 / 1215 + Real.log 3 / 6) := by
  rw [FaceA_eq_T1Set]; exact volume_T1Set

/-! ## The cone/face identity -/

/-! ## The cone/face identity

`{Δ₄ > 0}` is a cone (`Δ₄_smul`).  For **any** measurable cone `R ⊆ ℝ⁴`, cutting
`[-1,1]⁴` into the eight pieces "coordinate `i` attains `max_j |x_j|`, with sign
`±`" and rescaling each piece onto its face gives

    vol₄(R ∩ [-1,1]⁴) = (1/4) · Σ_{8 faces} vol₃(face).

**No divergence theorem is involved** — contrary to `TASK.md`'s reading of
`reference/VERDICT.md`.  On the piece where `x₁` is the largest coordinate and
positive, slicing off `x₁ = t` and using homogeneity of `R` gives

    vol₄(R ∩ piece) = ∫₀¹ vol₃( t · face ) dt = ∫₀¹ t³ dt · vol₃(face) = vol₃(face)/4,

which is Fubini plus the scaling law `vol₃(t·E) = t³ vol₃(E)` — no boundary
integral, so the cusps of `{Δ₄ = 0}` are irrelevant.  That is
`volume_conePiece1` below. -/

instance instIsAddLeftInvariant_volume_prod2 :
    (volume : Measure (ℝ × ℝ)).IsAddLeftInvariant :=
  (inferInstance : ((volume : Measure ℝ).prod volume).IsAddLeftInvariant)

instance instIsAddLeftInvariant_volume_prod3 :
    (volume : Measure (ℝ × ℝ × ℝ)).IsAddLeftInvariant :=
  (inferInstance : ((volume : Measure ℝ).prod volume).IsAddLeftInvariant)

noncomputable instance instIsAddHaarMeasure_volume_prod3 :
    (volume : Measure (ℝ × ℝ × ℝ)).IsAddHaarMeasure := ⟨⟩

instance instIsAddLeftInvariant_volume_prod4 :
    (volume : Measure (ℝ × ℝ × ℝ × ℝ)).IsAddLeftInvariant :=
  (inferInstance : ((volume : Measure ℝ).prod volume).IsAddLeftInvariant)

noncomputable instance instIsAddHaarMeasure_volume_prod4 :
    (volume : Measure (ℝ × ℝ × ℝ × ℝ)).IsAddHaarMeasure := ⟨⟩

/-- `vol₃(t · E) = t³ vol₃(E)`. -/
theorem volume_smul_three {t : ℝ} (ht : 0 ≤ t) (E : Set (ℝ × ℝ × ℝ)) :
    volume (t • E) = ENNReal.ofReal (t ^ 3) * volume E := by
  rw [Measure.addHaar_smul_of_nonneg volume ht E]
  norm_num

/-- A set is a *cone* if it is invariant under positive scaling. -/
def IsCone (R : Set (ℝ × ℝ × ℝ × ℝ)) : Prop :=
  ∀ l : ℝ, 0 < l → ∀ x, x ∈ R → l • x ∈ R

/-- The piece of `[-1,1]⁴` where the first coordinate attains `max_j |x_j|`,
with positive sign. -/
def conePiece1 : Set (ℝ × ℝ × ℝ × ℝ) :=
  {x | 0 < x.1 ∧ x.1 ≤ 1 ∧ |x.2.1| ≤ x.1 ∧ |x.2.2.1| ≤ x.1 ∧ |x.2.2.2| ≤ x.1}

/-- The face `x₁ = 1` of a cone. -/
def coneFace1 (R : Set (ℝ × ℝ × ℝ × ℝ)) : Set (ℝ × ℝ × ℝ) :=
  {y | |y.1| ≤ 1 ∧ |y.2.1| ≤ 1 ∧ |y.2.2| ≤ 1 ∧ (1, y) ∈ R}

theorem measurableSet_conePiece1 : MeasurableSet conePiece1 := by
  have h1 : Measurable fun x : ℝ × ℝ × ℝ × ℝ => x.1 := measurable_fst
  have h2 : Measurable fun x : ℝ × ℝ × ℝ × ℝ => |x.2.1| :=
    (measurable_fst.comp measurable_snd).abs
  have h3 : Measurable fun x : ℝ × ℝ × ℝ × ℝ => |x.2.2.1| :=
    ((measurable_fst.comp measurable_snd).comp measurable_snd).abs
  have h4 : Measurable fun x : ℝ × ℝ × ℝ × ℝ => |x.2.2.2| :=
    ((measurable_snd.comp measurable_snd).comp measurable_snd).abs
  have h : conePiece1 = ((({x : ℝ × ℝ × ℝ × ℝ | (0 : ℝ) < x.1}
      ∩ {x : ℝ × ℝ × ℝ × ℝ | x.1 ≤ (1 : ℝ)})
      ∩ {x : ℝ × ℝ × ℝ × ℝ | |x.2.1| ≤ x.1})
      ∩ {x : ℝ × ℝ × ℝ × ℝ | |x.2.2.1| ≤ x.1})
      ∩ {x : ℝ × ℝ × ℝ × ℝ | |x.2.2.2| ≤ x.1} := by
    ext x; simp only [conePiece1, Set.mem_ofPred_eq, Set.mem_inter_iff]; tauto
  rw [h]
  exact ((((measurableSet_lt measurable_const h1).inter
    (measurableSet_le h1 measurable_const)).inter
    (measurableSet_le h2 h1)).inter (measurableSet_le h3 h1)).inter (measurableSet_le h4 h1)

/-- The `t`-slice of `R ∩ conePiece1` is `t · (face)`, by homogeneity. -/
theorem slice_conePiece1 {R : Set (ℝ × ℝ × ℝ × ℝ)} (hR : IsCone R) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t ≤ 1) :
    Prod.mk t ⁻¹' (R ∩ conePiece1) = t • coneFace1 R := by
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
  have habs : ∀ z : ℝ, (|t⁻¹ * z| ≤ 1 ↔ |z| ≤ t) := by
    intro z
    rw [abs_mul, abs_of_pos (inv_pos.2 ht0), inv_mul_eq_div, div_le_one ht0]
  ext y
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ htne]
  simp only [Set.mem_preimage, Set.mem_inter_iff, conePiece1, coneFace1, Set.mem_ofPred_eq,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul, habs, hRiff]
  tauto

theorem volume_coneFace1_ne_top (R : Set (ℝ × ℝ × ℝ × ℝ)) :
    volume (coneFace1 R) ≠ ⊤ := by
  have hsub : coneFace1 R
      ⊆ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1 := by
    rintro y ⟨h1, h2, h3, -⟩
    exact ⟨abs_le.1 h1, abs_le.1 h2, abs_le.1 h3⟩
  refine ne_top_of_le_ne_top ?_ (measure_mono hsub)
  rw [volume_cube3]
  exact ENNReal.ofReal_ne_top

theorem lintegral_pow_three : ∫⁻ t in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ 3)
    = ENNReal.ofReal (1 / 4) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((continuous_pow 3).continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
    (by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
      simp only [Pi.zero_apply]
      exact pow_nonneg ht.1.le 3)]
  congr 1
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_pow]
  norm_num

/-- **PROVED — the radial identity, one face.**  For any measurable cone `R`, the
piece of `[-1,1]⁴` on which the first coordinate attains `max_j |x_j|` positively
has volume `(1/4)` times that of the face `x₁ = 1`.

This is the whole content of the "cone" step, and it is Fubini plus the scaling
law `vol₃(t·E) = t³ vol₃(E)`: slice at `x₁ = t`, use homogeneity of `R` to see the
slice as `t · face`, and integrate `∫₀¹ t³ dt = 1/4`.  **No boundary integral, so
no Stokes and no smoothness of `∂R` is needed.** -/
theorem volume_conePiece1 {R : Set (ℝ × ℝ × ℝ × ℝ)} (hR : MeasurableSet R)
    (hcone : IsCone R) :
    volume (R ∩ conePiece1) = ENNReal.ofReal (1 / 4) * volume (coneFace1 R) := by
  rw [show (volume : Measure (ℝ × ℝ × ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
    Measure.prod_apply (hR.inter measurableSet_conePiece1)]
  have hfun : (fun t : ℝ => (volume : Measure (ℝ × ℝ × ℝ)) (Prod.mk t ⁻¹' (R ∩ conePiece1)))
      = (Set.Ioc (0 : ℝ) 1).indicator
        (fun t => ENNReal.ofReal (t ^ 3) * volume (coneFace1 R)) := by
    funext t
    by_cases ht : t ∈ Set.Ioc (0 : ℝ) 1
    · rw [Set.indicator_of_mem ht, slice_conePiece1 hcone ht.1 ht.2,
        volume_smul_three ht.1.le]
    · rw [Set.indicator_of_notMem ht]
      have hempty : Prod.mk t ⁻¹' (R ∩ conePiece1) = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro y ⟨-, h1, h2, -, -, -⟩
        exact ht ⟨h1, h2⟩
      rw [hempty, measure_empty]
  rw [hfun, lintegral_indicator measurableSet_Ioc,
    lintegral_mul_const' _ _ (volume_coneFace1_ne_top R), lintegral_pow_three, mul_comm]

/-! ### The cone `{Δ₄ > 0}` and its two faces -/

/-- The real-rooted set, as a cone in `ℝ⁴`. -/
def RCone : Set (ℝ × ℝ × ℝ × ℝ) := {p | 0 < Δ₄ p.1 p.2.1 p.2.2.1 p.2.2.2}

theorem measurableSet_RCone : MeasurableSet RCone :=
  measurableSet_lt measurable_const continuous_Δ₄.measurable

/-- `{Δ₄ > 0}` is a cone — this is `Δ₄_smul`, homogeneity of degree 4. -/
theorem isCone_RCone : IsCone RCone := by
  intro l hl x hx
  have hd : Δ₄ (l • x).1 (l • x).2.1 (l • x).2.2.1 (l • x).2.2.2
      = l ^ 4 * Δ₄ x.1 x.2.1 x.2.2.1 x.2.2.2 := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    exact Δ₄_smul _ _ _ _ _
  change 0 < Δ₄ (l • x).1 (l • x).2.1 (l • x).2.2.1 (l • x).2.2.2
  rw [hd]
  exact mul_pos (by positivity) hx

theorem coneFace1_RCone : coneFace1 RCone = FaceA := by
  ext y
  simp only [coneFace1, FaceA, RCone, Set.mem_ofPred_eq, Set.mem_Icc, abs_le]

/-- Swap the first two coordinates of `ℝ⁴`. -/
def swap12 : ℝ × ℝ × ℝ × ℝ → ℝ × ℝ × ℝ × ℝ := fun x => (x.2.1, x.1, x.2.2)

theorem swap12_involutive (x : ℝ × ℝ × ℝ × ℝ) : swap12 (swap12 x) = x := rfl

theorem measurePreserving_swap12 : MeasurePreserving swap12 volume volume := by
  have h1 : MeasurePreserving
      (MeasurableEquiv.prodAssoc (α := ℝ) (β := ℝ) (γ := ℝ × ℝ)).symm volume volume :=
    (MeasureTheory.volume_preserving_prodAssoc (α₁ := ℝ) (β₁ := ℝ) (γ₁ := ℝ × ℝ)).symm _
  have h2 : MeasurePreserving
      (Prod.map (Prod.swap : ℝ × ℝ → ℝ × ℝ) (id : ℝ × ℝ → ℝ × ℝ)) volume volume :=
    (Measure.measurePreserving_swap).prod (MeasurePreserving.id _)
  have h3 : MeasurePreserving
      (MeasurableEquiv.prodAssoc (α := ℝ) (β := ℝ) (γ := ℝ × ℝ)) volume volume :=
    MeasureTheory.volume_preserving_prodAssoc
  have h := h3.comp (h2.comp h1)
  have heq : ((MeasurableEquiv.prodAssoc (α := ℝ) (β := ℝ) (γ := ℝ × ℝ)) ∘
      (Prod.map (Prod.swap : ℝ × ℝ → ℝ × ℝ) (id : ℝ × ℝ → ℝ × ℝ)) ∘
      (MeasurableEquiv.prodAssoc (α := ℝ) (β := ℝ) (γ := ℝ × ℝ)).symm) = swap12 := by
    funext x; rfl
  rwa [heq] at h

theorem measurable_swap12 : Measurable swap12 := measurePreserving_swap12.measurable

/-- The piece of `[-1,1]⁴` where the **second** coordinate attains `max_j |x_j|`,
with positive sign. -/
def conePiece2 : Set (ℝ × ℝ × ℝ × ℝ) := swap12 ⁻¹' conePiece1

theorem isCone_swap12_RCone : IsCone (swap12 ⁻¹' RCone) := by
  intro l hl x hx
  have hs : swap12 (l • x) = l • swap12 x := rfl
  rw [Set.mem_preimage, hs]
  exact isCone_RCone l hl _ hx

theorem coneFace1_swap12_RCone : coneFace1 (swap12 ⁻¹' RCone) = FaceB := by
  ext y
  simp only [coneFace1, FaceB, RCone, swap12, Set.mem_preimage, Set.mem_ofPred_eq,
    Set.mem_Icc, abs_le]

/-- **PROVED — the radial identity for the second face**, obtained from
`volume_conePiece1` by the measure-preserving swap of coordinates 1 and 2. -/
theorem volume_conePiece2 :
    volume (RCone ∩ conePiece2) = ENNReal.ofReal (1 / 4) * volume FaceB := by
  have hm : MeasurableSet (swap12 ⁻¹' RCone) := measurableSet_RCone.preimage measurable_swap12
  have hpre : RCone ∩ conePiece2 = swap12 ⁻¹' ((swap12 ⁻¹' RCone) ∩ conePiece1) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, conePiece2, swap12_involutive]
  rw [hpre, measurePreserving_swap12.measure_preimage
      (hm.inter measurableSet_conePiece1).nullMeasurableSet,
    volume_conePiece1 hm isCone_swap12_RCone, coneFace1_swap12_RCone]

/-! ### The other six pieces, by the two `ring`-provable symmetries of `Δ₄` -/

/-- Central symmetry `x ↦ -x`.  Preserves `Δ₄` (`Δ₄_neg`). -/
def negMap : ℝ × ℝ × ℝ × ℝ → ℝ × ℝ × ℝ × ℝ := fun x => (-x.1, -x.2.1, -x.2.2.1, -x.2.2.2)

theorem measurePreserving_negMap : MeasurePreserving negMap volume volume :=
  (Measure.measurePreserving_neg (volume : Measure ℝ)).prod
    ((Measure.measurePreserving_neg (volume : Measure ℝ)).prod
      ((Measure.measurePreserving_neg (volume : Measure ℝ)).prod
        (Measure.measurePreserving_neg (volume : Measure ℝ))))

theorem negMap_involutive (x : ℝ × ℝ × ℝ × ℝ) : negMap (negMap x) = x := by
  simp only [negMap, neg_neg]

/-- Coefficient reversal `(a,b,c,d) ↦ (d,c,b,a)`, i.e. `x ↦ 1/x` on the roots.
Preserves `Δ₄` (`Δ₄_reverse`). -/
def revMap : ℝ × ℝ × ℝ × ℝ → ℝ × ℝ × ℝ × ℝ := fun x => (x.2.2.2, x.2.2.1, x.2.1, x.1)

theorem measurePreserving_revMap : MeasurePreserving revMap volume volume := by
  have h1 : MeasurePreserving
      (MeasurableEquiv.prodAssoc (α := ℝ) (β := ℝ) (γ := ℝ × ℝ)).symm volume volume :=
    (MeasureTheory.volume_preserving_prodAssoc (α₁ := ℝ) (β₁ := ℝ) (γ₁ := ℝ × ℝ)).symm _
  have h2 : MeasurePreserving
      (Prod.map (Prod.swap : ℝ × ℝ → ℝ × ℝ) (Prod.swap : ℝ × ℝ → ℝ × ℝ)) volume volume :=
    (Measure.measurePreserving_swap).prod (Measure.measurePreserving_swap)
  have h3 : MeasurePreserving (Prod.swap : (ℝ × ℝ) × (ℝ × ℝ) → (ℝ × ℝ) × (ℝ × ℝ))
      volume volume := Measure.measurePreserving_swap
  have h4 : MeasurePreserving
      (MeasurableEquiv.prodAssoc (α := ℝ) (β := ℝ) (γ := ℝ × ℝ)) volume volume :=
    MeasureTheory.volume_preserving_prodAssoc
  have h := h4.comp (h3.comp (h2.comp h1))
  have heq : ((MeasurableEquiv.prodAssoc (α := ℝ) (β := ℝ) (γ := ℝ × ℝ)) ∘
      (Prod.swap : (ℝ × ℝ) × (ℝ × ℝ) → (ℝ × ℝ) × (ℝ × ℝ)) ∘
      (Prod.map (Prod.swap : ℝ × ℝ → ℝ × ℝ) (Prod.swap : ℝ × ℝ → ℝ × ℝ)) ∘
      (MeasurableEquiv.prodAssoc (α := ℝ) (β := ℝ) (γ := ℝ × ℝ)).symm) = revMap := by
    funext x; rfl
  rwa [heq] at h

theorem revMap_involutive (x : ℝ × ℝ × ℝ × ℝ) : revMap (revMap x) = x := rfl

theorem negMap_preimage_RCone : negMap ⁻¹' RCone = RCone := by
  ext x
  simp only [Set.mem_preimage, RCone, negMap, Set.mem_ofPred_eq, Δ₄_neg]

theorem revMap_preimage_RCone : revMap ⁻¹' RCone = RCone := by
  ext x
  simp only [Set.mem_preimage, RCone, revMap, Set.mem_ofPred_eq, Δ₄_reverse]

/-- The remaining six pieces of `[-1,1]⁴`. -/
def conePiece3 : Set (ℝ × ℝ × ℝ × ℝ) := revMap ⁻¹' conePiece2

def conePiece4 : Set (ℝ × ℝ × ℝ × ℝ) := revMap ⁻¹' conePiece1

def conePiece1N : Set (ℝ × ℝ × ℝ × ℝ) := negMap ⁻¹' conePiece1

def conePiece2N : Set (ℝ × ℝ × ℝ × ℝ) := negMap ⁻¹' conePiece2

def conePiece3N : Set (ℝ × ℝ × ℝ × ℝ) := negMap ⁻¹' conePiece3

def conePiece4N : Set (ℝ × ℝ × ℝ × ℝ) := negMap ⁻¹' conePiece4

theorem measurableSet_conePiece2 : MeasurableSet conePiece2 :=
  measurableSet_conePiece1.preimage measurable_swap12

theorem measurableSet_conePiece3 : MeasurableSet conePiece3 :=
  measurableSet_conePiece2.preimage measurePreserving_revMap.measurable

theorem measurableSet_conePiece4 : MeasurableSet conePiece4 :=
  measurableSet_conePiece1.preimage measurePreserving_revMap.measurable

/-- Transport of a piece's volume along a measure-preserving involution that
fixes the cone. -/
theorem volume_piece_transport {f : ℝ × ℝ × ℝ × ℝ → ℝ × ℝ × ℝ × ℝ}
    (hf : MeasurePreserving f volume volume)
    (hR : f ⁻¹' RCone = RCone) {P : Set (ℝ × ℝ × ℝ × ℝ)} (hP : MeasurableSet P) :
    volume (RCone ∩ f ⁻¹' P) = volume (RCone ∩ P) := by
  have hpre : RCone ∩ f ⁻¹' P = f ⁻¹' (RCone ∩ P) := by
    rw [Set.preimage_inter, hR]
  rw [hpre, hf.measure_preimage
    ((measurableSet_RCone.inter hP)).nullMeasurableSet]

theorem volume_conePiece3 :
    volume (RCone ∩ conePiece3) = volume (RCone ∩ conePiece2) :=
  volume_piece_transport measurePreserving_revMap revMap_preimage_RCone measurableSet_conePiece2

theorem volume_conePiece4 :
    volume (RCone ∩ conePiece4) = volume (RCone ∩ conePiece1) :=
  volume_piece_transport measurePreserving_revMap revMap_preimage_RCone measurableSet_conePiece1

theorem volume_conePiece1N :
    volume (RCone ∩ conePiece1N) = volume (RCone ∩ conePiece1) :=
  volume_piece_transport measurePreserving_negMap negMap_preimage_RCone measurableSet_conePiece1

theorem volume_conePiece2N :
    volume (RCone ∩ conePiece2N) = volume (RCone ∩ conePiece2) :=
  volume_piece_transport measurePreserving_negMap negMap_preimage_RCone measurableSet_conePiece2

theorem volume_conePiece3N :
    volume (RCone ∩ conePiece3N) = volume (RCone ∩ conePiece2) := by
  rw [conePiece3N,
    volume_piece_transport measurePreserving_negMap negMap_preimage_RCone
      measurableSet_conePiece3, volume_conePiece3]

theorem volume_conePiece4N :
    volume (RCone ∩ conePiece4N) = volume (RCone ∩ conePiece1) := by
  rw [conePiece4N,
    volume_piece_transport measurePreserving_negMap negMap_preimage_RCone
      measurableSet_conePiece4, volume_conePiece4]

/-! ### The eight-piece partition

Everything here is bookkeeping.  The organising observation is that each piece
has a description with no inequalities between *different* coordinates: writing
`nrm x = max_j |x_j|` for the sup norm,

    conePiece1 = { x | 0 < nrm x ∧ nrm x ≤ 1 ∧ x.1 = nrm x }

and likewise for the other seven, with `x.1` replaced by the appropriate signed
coordinate.  Two distinct pieces then force two signed coordinates to be equal,
which either contradicts `0 < nrm x` (same coordinate, opposite signs) or lands
in the null set `tieSet` of the twelve hyperplanes `x_i = ±x_j`. -/

/-- The sup norm on `ℝ⁴`. -/
noncomputable def nrm (x : ℝ × ℝ × ℝ × ℝ) : ℝ :=
  max (max |x.1| |x.2.1|) (max |x.2.2.1| |x.2.2.2|)

theorem abs_le_nrm₁ (x : ℝ × ℝ × ℝ × ℝ) : |x.1| ≤ nrm x := le_max_of_le_left (le_max_left _ _)
theorem abs_le_nrm₂ (x : ℝ × ℝ × ℝ × ℝ) : |x.2.1| ≤ nrm x := le_max_of_le_left (le_max_right _ _)
theorem abs_le_nrm₃ (x : ℝ × ℝ × ℝ × ℝ) : |x.2.2.1| ≤ nrm x :=
  le_max_of_le_right (le_max_left _ _)
theorem abs_le_nrm₄ (x : ℝ × ℝ × ℝ × ℝ) : |x.2.2.2| ≤ nrm x :=
  le_max_of_le_right (le_max_right _ _)

theorem nrm_nonneg (x : ℝ × ℝ × ℝ × ℝ) : 0 ≤ nrm x :=
  le_trans (abs_nonneg _) (abs_le_nrm₁ x)

theorem nrm_eq_abs (x : ℝ × ℝ × ℝ × ℝ) :
    nrm x = |x.1| ∨ nrm x = |x.2.1| ∨ nrm x = |x.2.2.1| ∨ nrm x = |x.2.2.2| := by
  unfold nrm
  rcases max_cases (max |x.1| |x.2.1|) (max |x.2.2.1| |x.2.2.2|) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
  · rcases max_cases |x.1| |x.2.1| with ⟨h2, -⟩ | ⟨h2, -⟩ <;> rw [h2] <;> tauto
  · rcases max_cases |x.2.2.1| |x.2.2.2| with ⟨h2, -⟩ | ⟨h2, -⟩ <;> rw [h2] <;> tauto

theorem nrm_swap12 (x : ℝ × ℝ × ℝ × ℝ) : nrm (swap12 x) = nrm x := by
  unfold nrm swap12
  rw [max_comm |x.1| |x.2.1|]

theorem nrm_negMap (x : ℝ × ℝ × ℝ × ℝ) : nrm (negMap x) = nrm x := by
  unfold nrm negMap
  simp only [abs_neg]

theorem nrm_revMap (x : ℝ × ℝ × ℝ × ℝ) : nrm (revMap x) = nrm x := by
  unfold nrm revMap
  simp only
  rw [max_comm |x.2.2.2| |x.2.2.1|, max_comm |x.2.1| |x.1|,
    max_comm (max |x.2.2.1| |x.2.2.2|) (max |x.1| |x.2.1|)]

/-- The clean description of the first piece. -/
theorem conePiece1_eq :
    conePiece1 = {x : ℝ × ℝ × ℝ × ℝ | 0 < nrm x ∧ nrm x ≤ 1 ∧ x.1 = nrm x} := by
  ext x
  simp only [conePiece1, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    have hn : nrm x = x.1 := by
      unfold nrm
      rw [abs_of_pos h1, max_eq_left h3, max_eq_left (max_le h4 h5)]
    exact ⟨by linarith, by linarith, hn.symm⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨by linarith, by linarith, ?_, ?_, ?_⟩
    · rw [h3]; exact abs_le_nrm₂ x
    · rw [h3]; exact abs_le_nrm₃ x
    · rw [h3]; exact abs_le_nrm₄ x

theorem conePiece2_eq :
    conePiece2 = {x : ℝ × ℝ × ℝ × ℝ | 0 < nrm x ∧ nrm x ≤ 1 ∧ x.2.1 = nrm x} := by
  ext x
  rw [conePiece2, Set.mem_preimage, conePiece1_eq]
  simp only [Set.mem_ofPred_eq, nrm_swap12]
  exact Iff.rfl

theorem conePiece3_eq :
    conePiece3 = {x : ℝ × ℝ × ℝ × ℝ | 0 < nrm x ∧ nrm x ≤ 1 ∧ x.2.2.1 = nrm x} := by
  ext x
  rw [conePiece3, Set.mem_preimage, conePiece2_eq]
  simp only [Set.mem_ofPred_eq, nrm_revMap]
  exact Iff.rfl

theorem conePiece4_eq :
    conePiece4 = {x : ℝ × ℝ × ℝ × ℝ | 0 < nrm x ∧ nrm x ≤ 1 ∧ x.2.2.2 = nrm x} := by
  ext x
  rw [conePiece4, Set.mem_preimage, conePiece1_eq]
  simp only [Set.mem_ofPred_eq, nrm_revMap]
  exact Iff.rfl

theorem conePiece1N_eq :
    conePiece1N = {x : ℝ × ℝ × ℝ × ℝ | 0 < nrm x ∧ nrm x ≤ 1 ∧ -x.1 = nrm x} := by
  ext x
  rw [conePiece1N, Set.mem_preimage, conePiece1_eq]
  simp only [Set.mem_ofPred_eq, nrm_negMap]
  exact Iff.rfl

theorem conePiece2N_eq :
    conePiece2N = {x : ℝ × ℝ × ℝ × ℝ | 0 < nrm x ∧ nrm x ≤ 1 ∧ -x.2.1 = nrm x} := by
  ext x
  rw [conePiece2N, Set.mem_preimage, conePiece2_eq]
  simp only [Set.mem_ofPred_eq, nrm_negMap]
  exact Iff.rfl

theorem conePiece3N_eq :
    conePiece3N = {x : ℝ × ℝ × ℝ × ℝ | 0 < nrm x ∧ nrm x ≤ 1 ∧ -x.2.2.1 = nrm x} := by
  ext x
  rw [conePiece3N, Set.mem_preimage, conePiece3_eq]
  simp only [Set.mem_ofPred_eq, nrm_negMap]
  exact Iff.rfl

theorem conePiece4N_eq :
    conePiece4N = {x : ℝ × ℝ × ℝ × ℝ | 0 < nrm x ∧ nrm x ≤ 1 ∧ -x.2.2.2 = nrm x} := by
  ext x
  rw [conePiece4N, Set.mem_preimage, conePiece4_eq]
  simp only [Set.mem_ofPred_eq, nrm_negMap]
  exact Iff.rfl

/-- The twelve hyperplanes on which two coordinates tie in absolute value.  This
is the only place where two of the eight pieces can meet, and it is null. -/
def tieSet : Set (ℝ × ℝ × ℝ × ℝ) :=
  {x | x.1 = x.2.1 ∨ x.1 = -x.2.1 ∨ x.1 = x.2.2.1 ∨ x.1 = -x.2.2.1 ∨ x.1 = x.2.2.2 ∨
    x.1 = -x.2.2.2 ∨ x.2.1 = x.2.2.1 ∨ x.2.1 = -x.2.2.1 ∨ x.2.1 = x.2.2.2 ∨
    x.2.1 = -x.2.2.2 ∨ x.2.2.1 = x.2.2.2 ∨ x.2.2.1 = -x.2.2.2}

theorem tie₁ {x : ℝ × ℝ × ℝ × ℝ} (h : x.1 = x.2.1) : x ∈ tieSet := by
  simp only [tieSet, Set.mem_ofPred_eq]; tauto
theorem tie₂ {x : ℝ × ℝ × ℝ × ℝ} (h : x.1 = -x.2.1) : x ∈ tieSet := by
  simp only [tieSet, Set.mem_ofPred_eq]; tauto
theorem tie₃ {x : ℝ × ℝ × ℝ × ℝ} (h : x.1 = x.2.2.1) : x ∈ tieSet := by
  simp only [tieSet, Set.mem_ofPred_eq]; tauto
theorem tie₄ {x : ℝ × ℝ × ℝ × ℝ} (h : x.1 = -x.2.2.1) : x ∈ tieSet := by
  simp only [tieSet, Set.mem_ofPred_eq]; tauto
theorem tie₅ {x : ℝ × ℝ × ℝ × ℝ} (h : x.1 = x.2.2.2) : x ∈ tieSet := by
  simp only [tieSet, Set.mem_ofPred_eq]; tauto
theorem tie₆ {x : ℝ × ℝ × ℝ × ℝ} (h : x.1 = -x.2.2.2) : x ∈ tieSet := by
  simp only [tieSet, Set.mem_ofPred_eq]; tauto
theorem tie₇ {x : ℝ × ℝ × ℝ × ℝ} (h : x.2.1 = x.2.2.1) : x ∈ tieSet := by
  simp only [tieSet, Set.mem_ofPred_eq]; tauto
theorem tie₈ {x : ℝ × ℝ × ℝ × ℝ} (h : x.2.1 = -x.2.2.1) : x ∈ tieSet := by
  simp only [tieSet, Set.mem_ofPred_eq]; tauto
theorem tie₉ {x : ℝ × ℝ × ℝ × ℝ} (h : x.2.1 = x.2.2.2) : x ∈ tieSet := by
  simp only [tieSet, Set.mem_ofPred_eq]; tauto
theorem tie₁₀ {x : ℝ × ℝ × ℝ × ℝ} (h : x.2.1 = -x.2.2.2) : x ∈ tieSet := by
  simp only [tieSet, Set.mem_ofPred_eq]; tauto
theorem tie₁₁ {x : ℝ × ℝ × ℝ × ℝ} (h : x.2.2.1 = x.2.2.2) : x ∈ tieSet := by
  simp only [tieSet, Set.mem_ofPred_eq]; tauto
theorem tie₁₂ {x : ℝ × ℝ × ℝ × ℝ} (h : x.2.2.1 = -x.2.2.2) : x ∈ tieSet := by
  simp only [tieSet, Set.mem_ofPred_eq]; tauto

/-- A hyperplane through the origin in `ℝ⁴`. -/
def hyper (a b c d : ℝ) : Set (ℝ × ℝ × ℝ × ℝ) :=
  {x | a * x.1 + b * x.2.1 + c * x.2.2.1 + d * x.2.2.2 = 0}

noncomputable def linFunc (a b c d : ℝ) : (ℝ × ℝ × ℝ × ℝ) →ₗ[ℝ] ℝ where
  toFun x := a * x.1 + b * x.2.1 + c * x.2.2.1 + d * x.2.2.2
  map_add' u v := by simp only [Prod.fst_add, Prod.snd_add]; ring
  map_smul' r u := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]; ring

theorem volume_hyper {a b c d : ℝ} (h : ¬(a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0)) :
    volume (hyper a b c d) = 0 := by
  have hne : linFunc a b c d ≠ 0 := by
    intro hz
    refine h ⟨?_, ?_, ?_, ?_⟩
    · simpa [linFunc] using congrArg (fun f : (ℝ × ℝ × ℝ × ℝ) →ₗ[ℝ] ℝ => f (1, 0, 0, 0)) hz
    · simpa [linFunc] using congrArg (fun f : (ℝ × ℝ × ℝ × ℝ) →ₗ[ℝ] ℝ => f (0, 1, 0, 0)) hz
    · simpa [linFunc] using congrArg (fun f : (ℝ × ℝ × ℝ × ℝ) →ₗ[ℝ] ℝ => f (0, 0, 1, 0)) hz
    · simpa [linFunc] using congrArg (fun f : (ℝ × ℝ × ℝ × ℝ) →ₗ[ℝ] ℝ => f (0, 0, 0, 1)) hz
  have hset : hyper a b c d = (LinearMap.ker (linFunc a b c d) : Set (ℝ × ℝ × ℝ × ℝ)) := by
    ext x; simp [hyper, LinearMap.mem_ker, linFunc]
  rw [hset]
  exact Measure.addHaar_submodule _ _ (fun hk => hne (LinearMap.ker_eq_top.1 hk))

/-- The twelve hyperplanes, as a right-nested union. -/
def tieCover : Set (ℝ × ℝ × ℝ × ℝ) :=
  hyper 1 (-1) 0 0 ∪ (hyper 1 1 0 0 ∪ (hyper 1 0 (-1) 0 ∪ (hyper 1 0 1 0 ∪ (hyper 1 0 0 (-1) ∪
    (hyper 1 0 0 1 ∪ (hyper 0 1 (-1) 0 ∪ (hyper 0 1 1 0 ∪ (hyper 0 1 0 (-1) ∪ (hyper 0 1 0 1 ∪
    (hyper 0 0 1 (-1) ∪ (hyper 0 0 1 1)))))))))))

theorem volume_tieCover : volume tieCover = 0 := by
  unfold tieCover
  repeat' refine measure_union_null ?_ ?_
  all_goals exact volume_hyper (by norm_num)

theorem tieSet_subset_tieCover : tieSet ⊆ tieCover := by
  intro x hx
  simp only [tieCover, hyper, Set.mem_union, Set.mem_ofPred_eq, one_mul, zero_mul,
    add_zero, zero_add, neg_mul, add_eq_zero_iff_eq_neg, neg_neg]
  exact hx

theorem volume_tieSet : volume tieSet = 0 :=
  measure_mono_null tieSet_subset_tieCover volume_tieCover


theorem measurableSet_hyper (a b c d : ℝ) : MeasurableSet (hyper a b c d) := by
  have hc : Continuous fun x : ℝ × ℝ × ℝ × ℝ =>
      a * x.1 + b * x.2.1 + c * x.2.2.1 + d * x.2.2.2 := by fun_prop
  exact measurableSet_eq_fun hc.measurable measurable_const

theorem measurableSet_tieCover : MeasurableSet tieCover := by
  unfold tieCover
  repeat' refine MeasurableSet.union ?_ ?_
  all_goals exact measurableSet_hyper _ _ _ _

theorem measurableSet_conePiece1N : MeasurableSet conePiece1N :=
  measurableSet_conePiece1.preimage measurePreserving_negMap.measurable
theorem measurableSet_conePiece2N : MeasurableSet conePiece2N :=
  measurableSet_conePiece2.preimage measurePreserving_negMap.measurable
theorem measurableSet_conePiece3N : MeasurableSet conePiece3N :=
  measurableSet_conePiece3.preimage measurePreserving_negMap.measurable
theorem measurableSet_conePiece4N : MeasurableSet conePiece4N :=
  measurableSet_conePiece4.preimage measurePreserving_negMap.measurable

/-- A piece of the partition, with the tie hyperplanes removed so the eight are
genuinely (not merely almost-everywhere) disjoint. -/
def Qp (P : Set (ℝ × ℝ × ℝ × ℝ)) : Set (ℝ × ℝ × ℝ × ℝ) := (RCone ∩ P) \ tieCover

theorem measurableSet_Qp {P : Set (ℝ × ℝ × ℝ × ℝ)} (hP : MeasurableSet P) :
    MeasurableSet (Qp P) := (measurableSet_RCone.inter hP).diff measurableSet_tieCover

theorem volume_Qp {P : Set (ℝ × ℝ × ℝ × ℝ)} : volume (Qp P) = volume (RCone ∩ P) :=
  measure_sdiff_null volume_tieCover

theorem nrm_pos_of_mem_RCone {x : ℝ × ℝ × ℝ × ℝ} (h : x ∈ RCone) : 0 < nrm x := by
  rcases (nrm_nonneg x).lt_or_eq with h1 | h1
  · exact h1
  · exfalso
    have e1 : x.1 = 0 := by
      have h2 := abs_le_nrm₁ x; rw [← h1] at h2
      exact abs_eq_zero.1 (le_antisymm h2 (abs_nonneg _))
    have e2 : x.2.1 = 0 := by
      have h2 := abs_le_nrm₂ x; rw [← h1] at h2
      exact abs_eq_zero.1 (le_antisymm h2 (abs_nonneg _))
    have e3 : x.2.2.1 = 0 := by
      have h2 := abs_le_nrm₃ x; rw [← h1] at h2
      exact abs_eq_zero.1 (le_antisymm h2 (abs_nonneg _))
    have e4 : x.2.2.2 = 0 := by
      have h2 := abs_le_nrm₄ x; rw [← h1] at h2
      exact abs_eq_zero.1 (le_antisymm h2 (abs_nonneg _))
    have hz : Δ₄ x.1 x.2.1 x.2.2.1 x.2.2.2 = 0 := by rw [e1, e2, e3, e4]; unfold Δ₄; ring
    have := h
    rw [RCone, Set.mem_ofPred_eq, hz] at this
    exact lt_irrefl 0 this

theorem nrm_le_one_of_mem_T3Set {x : ℝ × ℝ × ℝ × ℝ} (h : x ∈ T3Set) : nrm x ≤ 1 := by
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩, ⟨d1, d2⟩, -⟩ := h
  unfold nrm
  refine max_le (max_le ?_ ?_) (max_le ?_ ?_) <;> rw [abs_le] <;> constructor <;> linarith

theorem mem_T3Set_of_nrm {x : ℝ × ℝ × ℝ × ℝ} (h : x ∈ RCone) (hn : nrm x ≤ 1) :
    x ∈ T3Set := by
  refine ⟨abs_le.1 (le_trans (abs_le_nrm₁ x) hn), abs_le.1 (le_trans (abs_le_nrm₂ x) hn),
    abs_le.1 (le_trans (abs_le_nrm₃ x) hn), abs_le.1 (le_trans (abs_le_nrm₄ x) hn), h⟩

theorem disj_1_2 : Disjoint (Qp conePiece1) (Qp conePiece2) := by
  rw [Set.disjoint_left]
  rintro x ⟨⟨-, h1⟩, ht⟩ ⟨⟨-, h2⟩, -⟩
  rw [conePiece1_eq] at h1
  rw [conePiece2_eq] at h2
  exact ht (tieSet_subset_tieCover (tie₁ (by linarith [h1.2.2, h2.2.2])))

theorem disj_1_3 : Disjoint (Qp conePiece1) (Qp conePiece3) := by
  rw [Set.disjoint_left]
  rintro x ⟨⟨-, h1⟩, ht⟩ ⟨⟨-, h2⟩, -⟩
  rw [conePiece1_eq] at h1
  rw [conePiece3_eq] at h2
  exact ht (tieSet_subset_tieCover (tie₃ (by linarith [h1.2.2, h2.2.2])))

theorem disj_1_4 : Disjoint (Qp conePiece1) (Qp conePiece4) := by
  rw [Set.disjoint_left]
  rintro x ⟨⟨-, h1⟩, ht⟩ ⟨⟨-, h2⟩, -⟩
  rw [conePiece1_eq] at h1
  rw [conePiece4_eq] at h2
  exact ht (tieSet_subset_tieCover (tie₅ (by linarith [h1.2.2, h2.2.2])))

theorem disj_1_5 : Disjoint (Qp conePiece1) (Qp conePiece1N) := by
  rw [Set.disjoint_left]
  rintro x ⟨⟨-, h1⟩, ht⟩ ⟨⟨-, h2⟩, -⟩
  rw [conePiece1_eq] at h1
  rw [conePiece1N_eq] at h2
  exact absurd h1.1 (not_lt.2 (by linarith [h1.2.2, h2.2.2]))

theorem disj_1_6 : Disjoint (Qp conePiece1) (Qp conePiece2N) := by
  rw [Set.disjoint_left]
  rintro x ⟨⟨-, h1⟩, ht⟩ ⟨⟨-, h2⟩, -⟩
  rw [conePiece1_eq] at h1
  rw [conePiece2N_eq] at h2
  exact ht (tieSet_subset_tieCover (tie₂ (by linarith [h1.2.2, h2.2.2])))

theorem disj_1_7 : Disjoint (Qp conePiece1) (Qp conePiece3N) := by
  rw [Set.disjoint_left]
  rintro x ⟨⟨-, h1⟩, ht⟩ ⟨⟨-, h2⟩, -⟩
  rw [conePiece1_eq] at h1
  rw [conePiece3N_eq] at h2
  exact ht (tieSet_subset_tieCover (tie₄ (by linarith [h1.2.2, h2.2.2])))

theorem disj_1_8 : Disjoint (Qp conePiece1) (Qp conePiece4N) := by
  rw [Set.disjoint_left]
  rintro x ⟨⟨-, h1⟩, ht⟩ ⟨⟨-, h2⟩, -⟩
  rw [conePiece1_eq] at h1
  rw [conePiece4N_eq] at h2
  exact ht (tieSet_subset_tieCover (tie₆ (by linarith [h1.2.2, h2.2.2])))

theorem disj_2_3 : Disjoint (Qp conePiece2) (Qp conePiece3) := by
  rw [Set.disjoint_left]
  rintro x ⟨⟨-, h1⟩, ht⟩ ⟨⟨-, h2⟩, -⟩
  rw [conePiece2_eq] at h1
  rw [conePiece3_eq] at h2
  exact ht (tieSet_subset_tieCover (tie₇ (by linarith [h1.2.2, h2.2.2])))

theorem disj_2_4 : Disjoint (Qp conePiece2) (Qp conePiece4) := by
  rw [Set.disjoint_left]
  rintro x ⟨⟨-, h1⟩, ht⟩ ⟨⟨-, h2⟩, -⟩
  rw [conePiece2_eq] at h1
  rw [conePiece4_eq] at h2
  exact ht (tieSet_subset_tieCover (tie₉ (by linarith [h1.2.2, h2.2.2])))

theorem disj_2_5 : Disjoint (Qp conePiece2) (Qp conePiece1N) := by
  rw [Set.disjoint_left]
  rintro x ⟨⟨-, h1⟩, ht⟩ ⟨⟨-, h2⟩, -⟩
  rw [conePiece2_eq] at h1
  rw [conePiece1N_eq] at h2
  exact ht (tieSet_subset_tieCover (tie₂ (by linarith [h1.2.2, h2.2.2])))

theorem disj_2_6 : Disjoint (Qp conePiece2) (Qp conePiece2N) := by
  rw [Set.disjoint_left]
  rintro x ⟨⟨-, h1⟩, ht⟩ ⟨⟨-, h2⟩, -⟩
  rw [conePiece2_eq] at h1
  rw [conePiece2N_eq] at h2
  exact absurd h1.1 (not_lt.2 (by linarith [h1.2.2, h2.2.2]))

theorem disj_2_7 : Disjoint (Qp conePiece2) (Qp conePiece3N) := by
  rw [Set.disjoint_left]
  rintro x ⟨⟨-, h1⟩, ht⟩ ⟨⟨-, h2⟩, -⟩
  rw [conePiece2_eq] at h1
  rw [conePiece3N_eq] at h2
  exact ht (tieSet_subset_tieCover (tie₈ (by linarith [h1.2.2, h2.2.2])))

theorem disj_2_8 : Disjoint (Qp conePiece2) (Qp conePiece4N) := by
  rw [Set.disjoint_left]
  rintro x ⟨⟨-, h1⟩, ht⟩ ⟨⟨-, h2⟩, -⟩
  rw [conePiece2_eq] at h1
  rw [conePiece4N_eq] at h2
  exact ht (tieSet_subset_tieCover (tie₁₀ (by linarith [h1.2.2, h2.2.2])))

theorem disj_3_4 : Disjoint (Qp conePiece3) (Qp conePiece4) := by
  rw [Set.disjoint_left]
  rintro x ⟨⟨-, h1⟩, ht⟩ ⟨⟨-, h2⟩, -⟩
  rw [conePiece3_eq] at h1
  rw [conePiece4_eq] at h2
  exact ht (tieSet_subset_tieCover (tie₁₁ (by linarith [h1.2.2, h2.2.2])))

theorem disj_3_5 : Disjoint (Qp conePiece3) (Qp conePiece1N) := by
  rw [Set.disjoint_left]
  rintro x ⟨⟨-, h1⟩, ht⟩ ⟨⟨-, h2⟩, -⟩
  rw [conePiece3_eq] at h1
  rw [conePiece1N_eq] at h2
  exact ht (tieSet_subset_tieCover (tie₄ (by linarith [h1.2.2, h2.2.2])))

theorem disj_3_6 : Disjoint (Qp conePiece3) (Qp conePiece2N) := by
  rw [Set.disjoint_left]
  rintro x ⟨⟨-, h1⟩, ht⟩ ⟨⟨-, h2⟩, -⟩
  rw [conePiece3_eq] at h1
  rw [conePiece2N_eq] at h2
  exact ht (tieSet_subset_tieCover (tie₈ (by linarith [h1.2.2, h2.2.2])))

theorem disj_3_7 : Disjoint (Qp conePiece3) (Qp conePiece3N) := by
  rw [Set.disjoint_left]
  rintro x ⟨⟨-, h1⟩, ht⟩ ⟨⟨-, h2⟩, -⟩
  rw [conePiece3_eq] at h1
  rw [conePiece3N_eq] at h2
  exact absurd h1.1 (not_lt.2 (by linarith [h1.2.2, h2.2.2]))

theorem disj_3_8 : Disjoint (Qp conePiece3) (Qp conePiece4N) := by
  rw [Set.disjoint_left]
  rintro x ⟨⟨-, h1⟩, ht⟩ ⟨⟨-, h2⟩, -⟩
  rw [conePiece3_eq] at h1
  rw [conePiece4N_eq] at h2
  exact ht (tieSet_subset_tieCover (tie₁₂ (by linarith [h1.2.2, h2.2.2])))

theorem disj_4_5 : Disjoint (Qp conePiece4) (Qp conePiece1N) := by
  rw [Set.disjoint_left]
  rintro x ⟨⟨-, h1⟩, ht⟩ ⟨⟨-, h2⟩, -⟩
  rw [conePiece4_eq] at h1
  rw [conePiece1N_eq] at h2
  exact ht (tieSet_subset_tieCover (tie₆ (by linarith [h1.2.2, h2.2.2])))

theorem disj_4_6 : Disjoint (Qp conePiece4) (Qp conePiece2N) := by
  rw [Set.disjoint_left]
  rintro x ⟨⟨-, h1⟩, ht⟩ ⟨⟨-, h2⟩, -⟩
  rw [conePiece4_eq] at h1
  rw [conePiece2N_eq] at h2
  exact ht (tieSet_subset_tieCover (tie₁₀ (by linarith [h1.2.2, h2.2.2])))

theorem disj_4_7 : Disjoint (Qp conePiece4) (Qp conePiece3N) := by
  rw [Set.disjoint_left]
  rintro x ⟨⟨-, h1⟩, ht⟩ ⟨⟨-, h2⟩, -⟩
  rw [conePiece4_eq] at h1
  rw [conePiece3N_eq] at h2
  exact ht (tieSet_subset_tieCover (tie₁₂ (by linarith [h1.2.2, h2.2.2])))

theorem disj_4_8 : Disjoint (Qp conePiece4) (Qp conePiece4N) := by
  rw [Set.disjoint_left]
  rintro x ⟨⟨-, h1⟩, ht⟩ ⟨⟨-, h2⟩, -⟩
  rw [conePiece4_eq] at h1
  rw [conePiece4N_eq] at h2
  exact absurd h1.1 (not_lt.2 (by linarith [h1.2.2, h2.2.2]))

theorem disj_5_6 : Disjoint (Qp conePiece1N) (Qp conePiece2N) := by
  rw [Set.disjoint_left]
  rintro x ⟨⟨-, h1⟩, ht⟩ ⟨⟨-, h2⟩, -⟩
  rw [conePiece1N_eq] at h1
  rw [conePiece2N_eq] at h2
  exact ht (tieSet_subset_tieCover (tie₁ (by linarith [h1.2.2, h2.2.2])))

theorem disj_5_7 : Disjoint (Qp conePiece1N) (Qp conePiece3N) := by
  rw [Set.disjoint_left]
  rintro x ⟨⟨-, h1⟩, ht⟩ ⟨⟨-, h2⟩, -⟩
  rw [conePiece1N_eq] at h1
  rw [conePiece3N_eq] at h2
  exact ht (tieSet_subset_tieCover (tie₃ (by linarith [h1.2.2, h2.2.2])))

theorem disj_5_8 : Disjoint (Qp conePiece1N) (Qp conePiece4N) := by
  rw [Set.disjoint_left]
  rintro x ⟨⟨-, h1⟩, ht⟩ ⟨⟨-, h2⟩, -⟩
  rw [conePiece1N_eq] at h1
  rw [conePiece4N_eq] at h2
  exact ht (tieSet_subset_tieCover (tie₅ (by linarith [h1.2.2, h2.2.2])))

theorem disj_6_7 : Disjoint (Qp conePiece2N) (Qp conePiece3N) := by
  rw [Set.disjoint_left]
  rintro x ⟨⟨-, h1⟩, ht⟩ ⟨⟨-, h2⟩, -⟩
  rw [conePiece2N_eq] at h1
  rw [conePiece3N_eq] at h2
  exact ht (tieSet_subset_tieCover (tie₇ (by linarith [h1.2.2, h2.2.2])))

theorem disj_6_8 : Disjoint (Qp conePiece2N) (Qp conePiece4N) := by
  rw [Set.disjoint_left]
  rintro x ⟨⟨-, h1⟩, ht⟩ ⟨⟨-, h2⟩, -⟩
  rw [conePiece2N_eq] at h1
  rw [conePiece4N_eq] at h2
  exact ht (tieSet_subset_tieCover (tie₉ (by linarith [h1.2.2, h2.2.2])))

theorem disj_7_8 : Disjoint (Qp conePiece3N) (Qp conePiece4N) := by
  rw [Set.disjoint_left]
  rintro x ⟨⟨-, h1⟩, ht⟩ ⟨⟨-, h2⟩, -⟩
  rw [conePiece3N_eq] at h1
  rw [conePiece4N_eq] at h2
  exact ht (tieSet_subset_tieCover (tie₁₁ (by linarith [h1.2.2, h2.2.2])))


/-- **The covering.**  Off the tie hyperplanes the eight pieces partition the
real-rooted region: every point's largest coordinate picks out exactly one. -/
theorem T3Set_diff_eq :
    T3Set \ tieCover =
      Qp conePiece1 ∪ (Qp conePiece2 ∪ (Qp conePiece3 ∪ (Qp conePiece4 ∪ (Qp conePiece1N ∪ (Qp
        conePiece2N ∪ (Qp conePiece3N ∪ (Qp conePiece4N))))))) := by
  ext x
  constructor
  · rintro ⟨hx, ht⟩
    have hR : x ∈ RCone := hx.2.2.2.2
    have hpos := nrm_pos_of_mem_RCone hR
    have hle := nrm_le_one_of_mem_T3Set hx
    have hmem : ∀ P : Set (ℝ × ℝ × ℝ × ℝ), x ∈ P → x ∈ Qp P := fun P h => ⟨⟨hR, h⟩, ht⟩
    rcases nrm_eq_abs x with h | h | h | h
    · rcases abs_choice x.1 with e | e
      · refine Or.inl (hmem _ ?_)
        rw [conePiece1_eq]
        exact ⟨hpos, hle, by rw [h, e]⟩
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hmem _ ?_)))))
        rw [conePiece1N_eq]
        exact ⟨hpos, hle, by rw [h, e]⟩
    · rcases abs_choice x.2.1 with e | e
      · refine Or.inr (Or.inl (hmem _ ?_))
        rw [conePiece2_eq]
        exact ⟨hpos, hle, by rw [h, e]⟩
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hmem _ ?_))))))
        rw [conePiece2N_eq]
        exact ⟨hpos, hle, by rw [h, e]⟩
    · rcases abs_choice x.2.2.1 with e | e
      · refine Or.inr (Or.inr (Or.inl (hmem _ ?_)))
        rw [conePiece3_eq]
        exact ⟨hpos, hle, by rw [h, e]⟩
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hmem _ ?_)))))))
        rw [conePiece3N_eq]
        exact ⟨hpos, hle, by rw [h, e]⟩
    · rcases abs_choice x.2.2.2 with e | e
      · refine Or.inr (Or.inr (Or.inr (Or.inl (hmem _ ?_))))
        rw [conePiece4_eq]
        exact ⟨hpos, hle, by rw [h, e]⟩
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hmem _ ?_)))))))
        rw [conePiece4N_eq]
        exact ⟨hpos, hle, by rw [h, e]⟩
  · rintro (h | h | h | h | h | h | h | h) <;> obtain ⟨⟨hR, hP⟩, ht⟩ := h
    · rw [conePiece1_eq] at hP
      exact ⟨mem_T3Set_of_nrm hR hP.2.1, ht⟩
    · rw [conePiece2_eq] at hP
      exact ⟨mem_T3Set_of_nrm hR hP.2.1, ht⟩
    · rw [conePiece3_eq] at hP
      exact ⟨mem_T3Set_of_nrm hR hP.2.1, ht⟩
    · rw [conePiece4_eq] at hP
      exact ⟨mem_T3Set_of_nrm hR hP.2.1, ht⟩
    · rw [conePiece1N_eq] at hP
      exact ⟨mem_T3Set_of_nrm hR hP.2.1, ht⟩
    · rw [conePiece2N_eq] at hP
      exact ⟨mem_T3Set_of_nrm hR hP.2.1, ht⟩
    · rw [conePiece3N_eq] at hP
      exact ⟨mem_T3Set_of_nrm hR hP.2.1, ht⟩
    · rw [conePiece4N_eq] at hP
      exact ⟨mem_T3Set_of_nrm hR hP.2.1, ht⟩

/-- **PROVED — the eight-piece partition.** -/
theorem volume_T3Set_sum :
    volume T3Set = volume (RCone ∩ conePiece1) + (volume (RCone ∩ conePiece2)
      + (volume (RCone ∩ conePiece3) + (volume (RCone ∩ conePiece4)
      + (volume (RCone ∩ conePiece1N) + (volume (RCone ∩ conePiece2N)
      + (volume (RCone ∩ conePiece3N) + volume (RCone ∩ conePiece4N))))))) := by
  have hT : volume T3Set = volume (T3Set \ tieCover) :=
    (measure_sdiff_null volume_tieCover).symm
  rw [hT, T3Set_diff_eq]
  rw [measure_union
    (by simp only [Set.disjoint_union_right]; exact ⟨disj_1_2, disj_1_3, disj_1_4, disj_1_5,
      disj_1_6, disj_1_7, disj_1_8⟩)
    ((measurableSet_Qp measurableSet_conePiece2).union ((measurableSet_Qp
      measurableSet_conePiece3).union ((measurableSet_Qp measurableSet_conePiece4).union
      ((measurableSet_Qp measurableSet_conePiece1N).union ((measurableSet_Qp
      measurableSet_conePiece2N).union ((measurableSet_Qp measurableSet_conePiece3N).union
      (measurableSet_Qp measurableSet_conePiece4N)))))))]
  rw [measure_union
    (by simp only [Set.disjoint_union_right]; exact ⟨disj_2_3, disj_2_4, disj_2_5, disj_2_6,
      disj_2_7, disj_2_8⟩)
    ((measurableSet_Qp measurableSet_conePiece3).union ((measurableSet_Qp
      measurableSet_conePiece4).union ((measurableSet_Qp measurableSet_conePiece1N).union
      ((measurableSet_Qp measurableSet_conePiece2N).union ((measurableSet_Qp
      measurableSet_conePiece3N).union (measurableSet_Qp measurableSet_conePiece4N))))))]
  rw [measure_union
    (by simp only [Set.disjoint_union_right]; exact ⟨disj_3_4, disj_3_5, disj_3_6, disj_3_7,
      disj_3_8⟩)
    ((measurableSet_Qp measurableSet_conePiece4).union ((measurableSet_Qp
      measurableSet_conePiece1N).union ((measurableSet_Qp measurableSet_conePiece2N).union
      ((measurableSet_Qp measurableSet_conePiece3N).union (measurableSet_Qp
      measurableSet_conePiece4N)))))]
  rw [measure_union
    (by simp only [Set.disjoint_union_right]; exact ⟨disj_4_5, disj_4_6, disj_4_7, disj_4_8⟩)
    ((measurableSet_Qp measurableSet_conePiece1N).union ((measurableSet_Qp
      measurableSet_conePiece2N).union ((measurableSet_Qp measurableSet_conePiece3N).union
      (measurableSet_Qp measurableSet_conePiece4N))))]
  rw [measure_union
    (by simp only [Set.disjoint_union_right]; exact ⟨disj_5_6, disj_5_7, disj_5_8⟩)
    ((measurableSet_Qp measurableSet_conePiece2N).union ((measurableSet_Qp
      measurableSet_conePiece3N).union (measurableSet_Qp measurableSet_conePiece4N)))]
  rw [measure_union
    (by simp only [Set.disjoint_union_right]; exact ⟨disj_6_7, disj_6_8⟩)
    ((measurableSet_Qp measurableSet_conePiece3N).union (measurableSet_Qp
      measurableSet_conePiece4N))]
  rw [measure_union
    disj_7_8
    (measurableSet_Qp measurableSet_conePiece4N)]
  simp only [volume_Qp]

/-! ### What is left -/

/-- **PROVED — the eight-piece partition.**

    vol₄(T3Set) = 4 · vol₄(R ∩ conePiece1) + 4 · vol₄(R ∩ conePiece2).

`volume_T3Set_sum` splits the region into the eight pieces (covering by
`T3Set_diff_eq`, disjointness off the null `tieCover`), and the six symmetry
transports collapse them to two. -/
theorem volume_T3Set_eq_pieces :
    volume T3Set
      = 4 * volume (RCone ∩ conePiece1) + 4 * volume (RCone ∩ conePiece2) := by
  rw [volume_T3Set_sum, volume_conePiece3, volume_conePiece4, volume_conePiece1N,
    volume_conePiece2N, volume_conePiece3N, volume_conePiece4N]
  ring

/-- **PROVED from `volume_T3Set_eq_pieces`** — the cone/face identity
`vol₄ = S_a + S_b`. -/
theorem volume_T3Set_eq_faces : volume T3Set = volume FaceA + volume FaceB := by
  have h4 : (4 : ENNReal) * ENNReal.ofReal (1 / 4) = 1 := by
    rw [show ENNReal.ofReal (1 / 4 : ℝ) = (4 : ENNReal)⁻¹ by
      rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num,
        ENNReal.ofReal_inv_of_pos (by norm_num)]
      norm_num]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  rw [volume_T3Set_eq_pieces, volume_conePiece1 measurableSet_RCone isCone_RCone,
    coneFace1_RCone, volume_conePiece2, ← mul_assoc, ← mul_assoc, h4, one_mul, one_mul]


/-- **PROVED.**  `F(s)` really is the `a`-integral of the clipped band length:

    F s = ∫_{a₀ s}^{1} (K₊/(27a²) + min (K₋/(27a²)) 1) / a  da,   0 < s < 2, s ≠ 1.

The two branches of `Fs` come from the two clipping regimes settled by `L2`:

* `s ≤ 2/3` (`L2_no_clip`): `K₋/27 ≤ a₀²`, so `min (K₋/(27a²)) 1 = K₋/(27a²)`
  throughout `[a₀,1]`, the integrand collapses to `(K₊+K₋)/(27a³) = 4s³/(27a³)`
  by `Kp_add_Km`, and one antiderivative `-2s³/(27a²)` finishes it.
* `2/3 < s < 2` (`L2_clips`, `L2_alphaM_lt_one`): `a₀ < α₋ < 1`, the integral
  splits at `α₋`; below it the `min` is `1` and the antiderivative picks up the
  `log`, above it we are back in the previous case.  The cross terms
  `-K₊/(54α₋²) + 2s³/(27α₋²)` collapse to the constant `1/2` via `α₋² = K₋/27`
  and `K₊ + K₋ = 4s³` — this is `VERDICT.md`'s "the awkward term
  `−K₊/(2K₋) + 2s³/K₋` collapses to the constant `1/2`".

**The hypothesis `s ≠ 1` is necessary, and was missing from the earlier
statement of this lemma in this file.**  At `s = 1` we have `a₀ = 0`, the
integrand behaves like `1/a` near `0`, and the integral genuinely diverges; both
sides then degenerate to unrelated Lean junk values (`Fs 1 = 23/54` via `0/0 = 0`
and `log 0 = 0`, while the divergent `intervalIntegral` is `0`).  So the old
statement was false at that single point.  Excluding it is harmless: `{1}` is
Lebesgue-null in the outer `s`-integral that `volume_FaceB` needs, and `F` really
does blow up there (logarithmically, hence integrably). -/
theorem Fs_eq_face_integral {s : ℝ} (h0 : 0 < s) (h2 : s < 2) (hs1 : s ≠ 1) :
    Fs s = ∫ a in (a0 s)..1, (Kp s / (27 * a ^ 2) + min (Km s / (27 * a ^ 2)) 1) / a := by
  -- `0 < a₀ s < 1`
  have hsqne : s ^ 2 - 1 ≠ 0 := by
    intro h
    have hfac : (s - 1) * (s + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.1 hfac with h' | h'
    · exact hs1 (by linarith)
    · linarith
  have hA0 : 0 < a0 s := by
    unfold a0; exact div_pos (abs_pos.2 hsqne) (by norm_num)
  have hA1 : a0 s < 1 := by
    unfold a0
    rw [div_lt_one (by norm_num), abs_lt]
    constructor <;> nlinarith
  have hAne : a0 s ≠ 0 := ne_of_gt hA0
  -- the raw integrand is continuous away from `a = 0`, hence interval integrable
  have hint : ∀ u v : ℝ, 0 < u → u ≤ v →
      IntervalIntegrable
        (fun a : ℝ => (Kp s / (27 * a ^ 2) + min (Km s / (27 * a ^ 2)) 1) / a) volume u v := by
    intro u v hu huv
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le huv]
    have hxne : ∀ x ∈ Set.Icc u v, x ≠ 0 := fun x hx => ne_of_gt (lt_of_lt_of_le hu hx.1)
    have hden : ∀ x ∈ Set.Icc u v, (27 : ℝ) * x ^ 2 ≠ 0 :=
      fun x hx => mul_ne_zero (by norm_num) (pow_ne_zero 2 (hxne x hx))
    have hquot : ContinuousOn (fun a : ℝ => Km s / (27 * a ^ 2)) (Set.Icc u v) :=
      continuousOn_const.div ((continuous_const.mul (continuous_pow 2)).continuousOn) hden
    have hone : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc u v) := continuousOn_const
    have hmin : ContinuousOn (fun a : ℝ => min (Km s / (27 * a ^ 2)) 1) (Set.Icc u v) := by
      exact hquot.inf hone
    refine ContinuousOn.div ?_ (continuousOn_id' _) hxne
    exact (continuousOn_const.div ((continuous_const.mul (continuous_pow 2)).continuousOn)
      hden).add hmin
  by_cases hcase : s ≤ 2 / 3
  · -- ## Branch 1: the bottom of the band never clips
    unfold Fs
    rw [if_pos hcase]
    have hnoclip : Km s / 27 ≤ a0 s ^ 2 := L2_no_clip h0 hcase
    have hcongr : Set.EqOn
        (fun a : ℝ => (Kp s / (27 * a ^ 2) + min (Km s / (27 * a ^ 2)) 1) / a)
        (fun a : ℝ => 4 * s ^ 3 / (27 * a ^ 3)) (Set.uIcc (a0 s) 1) := by
      intro a ha
      rw [Set.uIcc_of_le hA1.le, Set.mem_Icc] at ha
      have hap : 0 < a := lt_of_lt_of_le hA0 ha.1
      have hle : Km s / (27 * a ^ 2) ≤ 1 := by
        rw [div_le_one (by nlinarith [pow_pos hap 2])]
        nlinarith [hnoclip, mul_nonneg (sub_nonneg.2 ha.1) (by linarith : (0 : ℝ) ≤ a + a0 s)]
      simp only
      have hK : Km s = 4 * s ^ 3 - Kp s := by linarith [Kp_add_Km s]
      rw [min_eq_left hle, hK]
      field_simp
      ring
    rw [integral_congr hcongr]
    have hderiv : ∀ x ∈ Set.uIcc (a0 s) 1,
        HasDerivAt (fun y : ℝ => -(2 * s ^ 3) / (27 * y ^ 2)) (4 * s ^ 3 / (27 * x ^ 3)) x := by
      intro x hx
      rw [Set.uIcc_of_le hA1.le, Set.mem_Icc] at hx
      have hxp : 0 < x := lt_of_lt_of_le hA0 hx.1
      have hd : HasDerivAt (fun y : ℝ => 27 * y ^ 2) (27 * (2 * x)) x := by
        simpa using ((hasDerivAt_id x).fun_pow 2).const_mul (27 : ℝ)
      have hne : (27 : ℝ) * x ^ 2 ≠ 0 :=
        mul_ne_zero (by norm_num) (pow_ne_zero 2 (ne_of_gt hxp))
      refine ((hasDerivAt_const x (-(2 * s ^ 3))).div hd hne).congr_deriv ?_
      field_simp
      ring
    have hi : IntervalIntegrable (fun a : ℝ => 4 * s ^ 3 / (27 * a ^ 3)) volume (a0 s) 1 := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hA1.le]
      exact continuousOn_const.div ((continuous_const.mul (continuous_pow 3)).continuousOn)
        (fun x hx => mul_ne_zero (by norm_num)
          (pow_ne_zero 3 (ne_of_gt (lt_of_lt_of_le hA0 hx.1))))
    rw [integral_eq_sub_of_hasDerivAt hderiv hi]
    field_simp
    ring
  · -- ## Branch 2: the bottom clips on `[a₀, α₋]`
    unfold Fs
    rw [if_neg hcase]
    rw [not_le] at hcase
    have hclip : a0 s ^ 2 < Km s / 27 := L2_clips hcase h2
    have hKmpos : 0 < Km s := by nlinarith [pow_pos hA0 2]
    have hKmne : Km s ≠ 0 := ne_of_gt hKmpos
    have hMsq : alphaM s ^ 2 = Km s / 27 := by
      unfold alphaM; exact Real.sq_sqrt (by linarith)
    have hM0 : 0 < alphaM s := by
      unfold alphaM; exact Real.sqrt_pos.2 (by linarith)
    have hMne : alphaM s ≠ 0 := ne_of_gt hM0
    have hAM : a0 s < alphaM s := by nlinarith [hMsq, hA0, hM0]
    have hM1 : alphaM s < 1 := by
      have hk := (L2_alphaM_lt_one h0.le).2 h2
      nlinarith [hMsq, hM0]
    rw [← integral_add_adjacent_intervals (b := alphaM s)
      (hint (a0 s) (alphaM s) hA0 hAM.le) (hint (alphaM s) 1 hM0 hM1.le)]
    -- lower piece: `min = 1`, the `log` appears
    have hc1 : Set.EqOn
        (fun a : ℝ => (Kp s / (27 * a ^ 2) + min (Km s / (27 * a ^ 2)) 1) / a)
        (fun a : ℝ => Kp s / (27 * a ^ 3) + 1 / a) (Set.uIcc (a0 s) (alphaM s)) := by
      intro a ha
      rw [Set.uIcc_of_le hAM.le, Set.mem_Icc] at ha
      have hap : 0 < a := lt_of_lt_of_le hA0 ha.1
      have hden : (0 : ℝ) < 27 * a ^ 2 := by nlinarith [pow_pos hap 2]
      have hge : 1 ≤ Km s / (27 * a ^ 2) := by
        rw [le_div_iff₀ hden]
        nlinarith [hMsq, mul_nonneg (sub_nonneg.2 ha.2) (by linarith : (0 : ℝ) ≤ alphaM s + a)]
      simp only
      rw [min_eq_right hge]
      field_simp
    -- upper piece: no clipping, as in branch 1
    have hc2 : Set.EqOn
        (fun a : ℝ => (Kp s / (27 * a ^ 2) + min (Km s / (27 * a ^ 2)) 1) / a)
        (fun a : ℝ => 4 * s ^ 3 / (27 * a ^ 3)) (Set.uIcc (alphaM s) 1) := by
      intro a ha
      rw [Set.uIcc_of_le hM1.le, Set.mem_Icc] at ha
      have hap : 0 < a := lt_of_lt_of_le hM0 ha.1
      have hle : Km s / (27 * a ^ 2) ≤ 1 := by
        rw [div_le_one (by nlinarith [pow_pos hap 2])]
        nlinarith [hMsq, mul_nonneg (sub_nonneg.2 ha.1) (by linarith : (0 : ℝ) ≤ a + alphaM s)]
      simp only
      have hK : Km s = 4 * s ^ 3 - Kp s := by linarith [Kp_add_Km s]
      rw [min_eq_left hle, hK]
      field_simp
      ring
    rw [integral_congr hc1, integral_congr hc2]
    have hd1 : ∀ x ∈ Set.uIcc (a0 s) (alphaM s),
        HasDerivAt (fun y : ℝ => -(Kp s) / (54 * y ^ 2) + Real.log y)
          (Kp s / (27 * x ^ 3) + 1 / x) x := by
      intro x hx
      rw [Set.uIcc_of_le hAM.le, Set.mem_Icc] at hx
      have hxp : 0 < x := lt_of_lt_of_le hA0 hx.1
      have hxne : x ≠ 0 := ne_of_gt hxp
      have hd : HasDerivAt (fun y : ℝ => 54 * y ^ 2) (54 * (2 * x)) x := by
        simpa using ((hasDerivAt_id x).fun_pow 2).const_mul (54 : ℝ)
      have hne : (54 : ℝ) * x ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hxne)
      refine (((hasDerivAt_const x (-(Kp s))).div hd hne).add
        (Real.hasDerivAt_log hxne)).congr_deriv ?_
      field_simp
      ring
    have hi1 : IntervalIntegrable (fun a : ℝ => Kp s / (27 * a ^ 3) + 1 / a) volume
        (a0 s) (alphaM s) := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hAM.le]
      have hxne : ∀ x ∈ Set.Icc (a0 s) (alphaM s), x ≠ 0 :=
        fun x hx => ne_of_gt (lt_of_lt_of_le hA0 hx.1)
      exact (continuousOn_const.div ((continuous_const.mul (continuous_pow 3)).continuousOn)
        (fun x hx => mul_ne_zero (by norm_num) (pow_ne_zero 3 (hxne x hx)))).add
        (continuousOn_const.div (continuousOn_id' _) hxne)
    have hd2 : ∀ x ∈ Set.uIcc (alphaM s) 1,
        HasDerivAt (fun y : ℝ => -(2 * s ^ 3) / (27 * y ^ 2)) (4 * s ^ 3 / (27 * x ^ 3)) x := by
      intro x hx
      rw [Set.uIcc_of_le hM1.le, Set.mem_Icc] at hx
      have hxp : 0 < x := lt_of_lt_of_le hM0 hx.1
      have hd : HasDerivAt (fun y : ℝ => 27 * y ^ 2) (27 * (2 * x)) x := by
        simpa using ((hasDerivAt_id x).fun_pow 2).const_mul (27 : ℝ)
      have hne : (27 : ℝ) * x ^ 2 ≠ 0 :=
        mul_ne_zero (by norm_num) (pow_ne_zero 2 (ne_of_gt hxp))
      refine ((hasDerivAt_const x (-(2 * s ^ 3))).div hd hne).congr_deriv ?_
      field_simp
      ring
    have hi2 : IntervalIntegrable (fun a : ℝ => 4 * s ^ 3 / (27 * a ^ 3)) volume
        (alphaM s) 1 := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hM1.le]
      exact continuousOn_const.div ((continuous_const.mul (continuous_pow 3)).continuousOn)
        (fun x hx => mul_ne_zero (by norm_num)
          (pow_ne_zero 3 (ne_of_gt (lt_of_lt_of_le hM0 hx.1))))
    rw [integral_eq_sub_of_hasDerivAt hd1 hi1, integral_eq_sub_of_hasDerivAt hd2 hi2,
      Real.log_div hMne hAne, hMsq]
    field_simp
    linear_combination (1458 * a0 s ^ 2) * Kp_add_Km s

/-! ### The outer `s`-integral `∫₀² s F(s) ds`

This is the calculus half of `S_b`.  Both branches of `Fs` are put in a form with
no `a₀` and no `α₋` left (`s_mul_Fs_le`, `s_mul_Fs_gt`), each gets an explicit
elementary antiderivative (`H1`, `H2`), and the FTC does the rest.  The `log 5`
that each half produces separately cancels in the sum — a useful internal check.
-/

theorem a0_of_lt_one {s : ℝ} (h0 : 0 ≤ s) (h1 : s < 1) : a0 s = (1 - s ^ 2) / 3 := by
  unfold a0
  rw [abs_of_nonpos (by nlinarith)]
  ring

theorem a0_of_one_lt {s : ℝ} (h1 : 1 < s) : a0 s = (s ^ 2 - 1) / 3 := by
  unfold a0
  rw [abs_of_nonneg (by nlinarith)]

/-- Lower branch integrand: no `a₀` left, and no `log`. -/
theorem s_mul_Fs_le {s : ℝ} (h0 : 0 ≤ s) (h : s ≤ 2 / 3) :
    s * Fs s = 2 * s ^ 4 / (3 * (s ^ 2 - 1) ^ 2) - 2 * s ^ 4 / 27 := by
  have hs1 : s < 1 := by linarith
  have hne : (1 : ℝ) - s ^ 2 ≠ 0 := by nlinarith
  have hne' : s ^ 2 - 1 ≠ 0 := by intro h; exact hne (by linarith)
  have hne2 : (s ^ 2 - 1) ^ 2 ≠ 0 := pow_ne_zero 2 hne'
  unfold Fs
  rw [if_pos h, a0_of_lt_one h0 hs1]
  field_simp
  ring

/-- The upper branch integrand, with `a₀` and `α₋` eliminated.  Only one `log`
singularity survives, at `s = 1`, and it is integrable. -/
noncomputable def G (s : ℝ) : ℝ :=
  s * (2 * s + 1) / (6 * (s + 1) ^ 2) + s / 2 + s / 2 * Real.log (2 * s - 1)
    - Real.log (s - 1) * s - s / 2 * Real.log 3 - 2 * s ^ 4 / 27

theorem log_27 : Real.log 27 = 3 * Real.log 3 := by
  rw [show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow]
  norm_num

theorem s_mul_Fs_gt {s : ℝ} (h1 : 2 / 3 < s) (hne : s ≠ 1) :
    s * Fs s = G s := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.2 hne
  have hsp : (0 : ℝ) < s + 1 := by linarith
  have h2s : (0 : ℝ) < 2 * s - 1 := by linarith
  have hKm : Km s = (s + 1) ^ 2 * (2 * s - 1) := rfl
  have hKmpos : 0 < Km s := by rw [hKm]; positivity
  have hsq : s ^ 2 - 1 ≠ 0 := by
    intro h
    exact hs1 (by nlinarith)
  have hA0 : 0 < a0 s := by
    unfold a0; exact div_pos (abs_pos.2 hsq) (by norm_num)
  have hM0 : 0 < alphaM s := by
    unfold alphaM; exact Real.sqrt_pos.2 (by linarith)
  have hlogA : Real.log (a0 s) = Real.log (s - 1) + Real.log (s + 1) - Real.log 3 := by
    unfold a0
    rw [Real.log_div (by simpa using hsq) (by norm_num), Real.log_abs,
      show s ^ 2 - 1 = (s - 1) * (s + 1) by ring, Real.log_mul hs1 (ne_of_gt hsp)]
  have hlogM : Real.log (alphaM s)
      = Real.log (s + 1) + Real.log (2 * s - 1) / 2 - 3 * Real.log 3 / 2 := by
    unfold alphaM
    rw [Real.log_sqrt (by positivity), Real.log_div (ne_of_gt hKmpos) (by norm_num), hKm,
      Real.log_mul (by positivity) (ne_of_gt h2s), Real.log_pow, log_27]
    push_cast
    ring
  unfold Fs G
  rw [if_neg (by linarith : ¬ s ≤ 2 / 3), Real.log_div (ne_of_gt hM0) (ne_of_gt hA0),
    hlogM, hlogA, a0_sq]
  have hKp : Kp s = (s - 1) ^ 2 * (2 * s + 1) := rfl
  rw [hKp]
  field_simp
  ring

/-! #### The two antiderivatives -/

/-- Antiderivative of `s F(s)` on `[0, 2/3]`. -/
noncomputable def H1 (s : ℝ) : ℝ :=
  2 / 3 * s - s / (3 * (s ^ 2 - 1)) + 1 / 2 * Real.log (1 - s) - 1 / 2 * Real.log (1 + s)
    - 2 * s ^ 5 / 135

theorem hasDerivAt_H1 {s : ℝ} (h0 : 0 ≤ s) (h1 : s < 1) :
    HasDerivAt H1 (2 * s ^ 4 / (3 * (s ^ 2 - 1) ^ 2) - 2 * s ^ 4 / 27) s := by
  have hlt : (3 : ℝ) * (s ^ 2 - 1) < 0 := by nlinarith
  have hden : (3 : ℝ) * (s ^ 2 - 1) ≠ 0 := ne_of_lt hlt
  have hne' : s ^ 2 - 1 ≠ 0 := by intro h; rw [h] at hlt; norm_num at hlt
  have hne2 : (s ^ 2 - 1) ^ 2 ≠ 0 := pow_ne_zero 2 hne'
  have hu : (1 : ℝ) - s ≠ 0 := by intro h; nlinarith
  have hv : (1 : ℝ) + s ≠ 0 := by intro h; nlinarith
  have hA : HasDerivAt (fun y : ℝ => 2 / 3 * y) (2 / 3 : ℝ) s := by
    simpa using (hasDerivAt_id s).const_mul (2 / 3 : ℝ)
  have hq : HasDerivAt (fun y : ℝ => 3 * (y ^ 2 - 1)) (3 * (2 * s)) s := by
    simpa using (((hasDerivAt_id s).fun_pow 2).sub_const (1 : ℝ)).const_mul (3 : ℝ)
  have hB : HasDerivAt (fun y : ℝ => y / (3 * (y ^ 2 - 1)))
      ((1 * (3 * (s ^ 2 - 1)) - s * (3 * (2 * s))) / (3 * (s ^ 2 - 1)) ^ 2) s :=
    (hasDerivAt_id s).div hq hden
  have hu' : HasDerivAt (fun y : ℝ => 1 - y) (-1 : ℝ) s := by
    simpa using (hasDerivAt_id s).const_sub (1 : ℝ)
  have hC : HasDerivAt (fun y : ℝ => Real.log (1 - y)) (-1 / (1 - s)) s := hu'.log hu
  have hv' : HasDerivAt (fun y : ℝ => 1 + y) (1 : ℝ) s := by
    simpa using (hasDerivAt_id s).const_add (1 : ℝ)
  have hD : HasDerivAt (fun y : ℝ => Real.log (1 + y)) (1 / (1 + s)) s := hv'.log hv
  have hE : HasDerivAt (fun y : ℝ => 2 * y ^ 5 / 135) (2 * (5 * s ^ 4) / 135) s := by
    simpa using (((hasDerivAt_id s).fun_pow 5).const_mul (2 : ℝ)).div_const 135
  refine ((((hA.sub hB).add (hC.const_mul (1 / 2 : ℝ))).sub
    (hD.const_mul (1 / 2 : ℝ))).sub hE).congr_deriv ?_
  field_simp
  ring

/-- Antiderivative of `s F(s)` on `[2/3, 2]`.  The last `log` term is written as
`((s+1)/2) * ((s-1) log (s-1))` so that `Real.continuous_mul_log` gives its
continuity at the singular point `s = 1` for free. -/
noncomputable def H2 (s : ℝ) : ℝ :=
  3 / 8 * s ^ 2 + 17 / 24 * s - 1 / (6 * (s + 1)) - 2 * s ^ 5 / 135
    - 1 / 2 * Real.log (s + 1) + (s ^ 2 / 4 - 1 / 16) * Real.log (2 * s - 1)
    - (s + 1) / 2 * ((s - 1) * Real.log (s - 1)) - s ^ 2 / 4 * Real.log 3

theorem hasDerivAt_H2 {s : ℝ} (hsp : (0 : ℝ) < s + 1) (h2s : (0 : ℝ) < 2 * s - 1)
    (hs1 : s - 1 ≠ 0) : HasDerivAt H2 (G s) s := by
  have h6 : (6 : ℝ) * (s + 1) ≠ 0 := by positivity
  have hA : HasDerivAt (fun y : ℝ => 3 / 8 * y ^ 2) (3 / 8 * (2 * s)) s := by
    simpa using ((hasDerivAt_id s).fun_pow 2).const_mul (3 / 8 : ℝ)
  have hB : HasDerivAt (fun y : ℝ => 17 / 24 * y) (17 / 24 : ℝ) s := by
    simpa using (hasDerivAt_id s).const_mul (17 / 24 : ℝ)
  have hq : HasDerivAt (fun y : ℝ => 6 * (y + 1)) (6 * 1 : ℝ) s := by
    simpa using ((hasDerivAt_id s).add_const (1 : ℝ)).const_mul (6 : ℝ)
  have hC : HasDerivAt (fun y : ℝ => 1 / (6 * (y + 1)))
      ((0 * (6 * (s + 1)) - 1 * (6 * 1)) / (6 * (s + 1)) ^ 2) s :=
    (hasDerivAt_const s (1 : ℝ)).div hq h6
  have hD : HasDerivAt (fun y : ℝ => 2 * y ^ 5 / 135) (2 * (5 * s ^ 4) / 135) s := by
    simpa using (((hasDerivAt_id s).fun_pow 5).const_mul (2 : ℝ)).div_const 135
  have hp : HasDerivAt (fun y : ℝ => y + 1) (1 : ℝ) s := by
    simpa using (hasDerivAt_id s).add_const (1 : ℝ)
  have hE : HasDerivAt (fun y : ℝ => Real.log (y + 1)) (1 / (s + 1)) s := hp.log (ne_of_gt hsp)
  have ht : HasDerivAt (fun y : ℝ => 2 * y - 1) (2 : ℝ) s := by
    simpa using ((hasDerivAt_id s).const_mul (2 : ℝ)).sub_const (1 : ℝ)
  have hF : HasDerivAt (fun y : ℝ => Real.log (2 * y - 1)) (2 / (2 * s - 1)) s :=
    ht.log (ne_of_gt h2s)
  have hG : HasDerivAt (fun y : ℝ => y ^ 2 / 4 - 1 / 16) (2 * s / 4) s := by
    simpa using (((hasDerivAt_id s).fun_pow 2).div_const 4).sub_const (1 / 16 : ℝ)
  have hm : HasDerivAt (fun y : ℝ => y - 1) (1 : ℝ) s := by
    simpa using (hasDerivAt_id s).sub_const (1 : ℝ)
  have hlm : HasDerivAt (fun y : ℝ => Real.log (y - 1)) (1 / (s - 1)) s := hm.log hs1
  have hW : HasDerivAt (fun y : ℝ => (y - 1) * Real.log (y - 1))
      (1 * Real.log (s - 1) + (s - 1) * (1 / (s - 1))) s := hm.mul hlm
  have hV : HasDerivAt (fun y : ℝ => (y + 1) / 2) (1 / 2 : ℝ) s := by
    simpa using ((hasDerivAt_id s).add_const (1 : ℝ)).div_const 2
  have hI : HasDerivAt (fun y : ℝ => y ^ 2 / 4 * Real.log 3) (2 * s / 4 * Real.log 3) s := by
    simpa using (((hasDerivAt_id s).fun_pow 2).div_const 4).mul_const (Real.log 3)
  refine ((((((hA.add hB).sub hC).sub hD).sub (hE.const_mul (1 / 2 : ℝ))).add
    (hG.mul hF)).sub (hV.mul hW) |>.sub hI).congr_deriv ?_
  unfold G
  field_simp
  ring

/-! #### Continuity and integrability -/

/-- `H2` is continuous across the singular point `s = 1`: the only term that
could fail is `((s+1)/2) * ((s-1) log (s-1))`, and `Real.continuous_mul_log`
says `x ↦ x log x` is continuous at `0`. -/
theorem continuousOn_H2 : ContinuousOn H2 (Set.Icc (2 / 3 : ℝ) 2) := by
  have hml : Continuous fun y : ℝ => (y + 1) / 2 * ((y - 1) * Real.log (y - 1)) :=
    ((continuous_id.add continuous_const).div_const 2).mul
      (Real.continuous_mul_log.comp (continuous_id.sub continuous_const))
  intro x hx
  have hx1 : (2 : ℝ) / 3 ≤ x := hx.1
  have hp : x + 1 ≠ 0 := by intro h; linarith
  have hq : 2 * x - 1 ≠ 0 := by intro h; linarith
  have h6 : (6 : ℝ) * (x + 1) ≠ 0 := by intro h; linarith
  refine ContinuousAt.continuousWithinAt ?_
  have hrest : ContinuousAt (fun y : ℝ => 3 / 8 * y ^ 2 + 17 / 24 * y - 1 / (6 * (y + 1))
      - 2 * y ^ 5 / 135 - 1 / 2 * Real.log (y + 1)
      + (y ^ 2 / 4 - 1 / 16) * Real.log (2 * y - 1)) x := by
    fun_prop (disch := assumption)
  have hlast : ContinuousAt (fun y : ℝ => y ^ 2 / 4 * Real.log 3) x := by fun_prop
  exact (hrest.sub hml.continuousAt).sub hlast

theorem intervalIntegrable_G {u v : ℝ} (hu : 2 / 3 ≤ u) (hv : v ≤ 2) (huv : u ≤ v) :
    IntervalIntegrable G volume u v := by
  have hsub : Set.uIcc u v ⊆ Set.Icc (2 / 3 : ℝ) 2 := by
    rw [Set.uIcc_of_le huv]; exact Set.Icc_subset_Icc hu hv
  have hlog : IntervalIntegrable (fun x : ℝ => Real.log (x - 1)) volume u v := by
    simpa using (intervalIntegrable_log' (a := u - 1) (b := v - 1)).comp_sub_right 1
  have hD : IntervalIntegrable (fun x : ℝ => Real.log (x - 1) * x) volume u v :=
    hlog.mul_continuousOn (continuousOn_id' _)
  have hABC : IntervalIntegrable
      (fun s : ℝ => s * (2 * s + 1) / (6 * (s + 1) ^ 2) + s / 2
        + s / 2 * Real.log (2 * s - 1)) volume u v := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hx1 : (2 : ℝ) / 3 ≤ x := (hsub hx).1
    have hxp : x + 1 ≠ 0 := by intro h; linarith
    have hq : 2 * x - 1 ≠ 0 := by intro h; linarith
    have hp : (6 : ℝ) * (x + 1) ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hxp)
    exact ContinuousAt.continuousWithinAt (by fun_prop (disch := assumption))
  have hE : IntervalIntegrable (fun s : ℝ => s / 2 * Real.log 3) volume u v :=
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  have hF : IntervalIntegrable (fun s : ℝ => 2 * s ^ 4 / 27) volume u v :=
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  unfold G
  exact ((hABC.sub hD).sub hE).sub hF

/-! #### The integral -/

theorem integral_low :
    ∫ s in (0 : ℝ)..(2 / 3), s * Fs s = H1 (2 / 3) - H1 0 := by
  have hEq : Set.EqOn (fun s : ℝ => 2 * s ^ 4 / (3 * (s ^ 2 - 1) ^ 2) - 2 * s ^ 4 / 27)
      (fun s : ℝ => s * Fs s) (Set.uIcc (0 : ℝ) (2 / 3)) := by
    intro s hs
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2 / 3), Set.mem_Icc] at hs
    exact (s_mul_Fs_le hs.1 hs.2).symm
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) (2 / 3),
      HasDerivAt H1 (2 * x ^ 4 / (3 * (x ^ 2 - 1) ^ 2) - 2 * x ^ 4 / 27) x := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2 / 3), Set.mem_Icc] at hx
    exact hasDerivAt_H1 hx.1 (by linarith [hx.2])
  have hint : IntervalIntegrable
      (fun s : ℝ => 2 * s ^ 4 / (3 * (s ^ 2 - 1) ^ 2) - 2 * s ^ 4 / 27) volume 0 (2 / 3) := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2 / 3), Set.mem_Icc] at hx
    have hlt : (3 : ℝ) * (x ^ 2 - 1) ^ 2 ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero 2 (by intro h; nlinarith [hx.1, hx.2]))
    exact ContinuousAt.continuousWithinAt (by fun_prop (disch := assumption))
  rw [← integral_congr hEq, integral_eq_sub_of_hasDerivAt hderiv hint]

theorem integral_high :
    ∫ s in (2 / 3 : ℝ)..2, s * Fs s = H2 2 - H2 (2 / 3) := by
  -- replace the integrand by `G`, which differs only at `s = 1`
  have hae : ∫ s in (2 / 3 : ℝ)..2, s * Fs s = ∫ s in (2 / 3 : ℝ)..2, G s := by
    refine integral_congr_ae ?_
    have hne : ∀ᵐ x : ℝ, x ≠ 1 := by
      rw [MeasureTheory.ae_iff]; simp
    filter_upwards [hne] with x hx hmem
    rw [Set.uIoc_of_le (by norm_num : (2 / 3 : ℝ) ≤ 2), Set.mem_Ioc] at hmem
    exact s_mul_Fs_gt hmem.1 hx
  have hderivL : ∀ x ∈ Set.Ioo (2 / 3 : ℝ) 1,
      HasDerivWithinAt H2 (G x) (Set.Ioi x) x := fun x hx =>
    (hasDerivAt_H2 (by linarith [hx.1]) (by linarith [hx.1])
      (by intro h; linarith [hx.2, sub_eq_zero.1 h])).hasDerivWithinAt
  have hderivR : ∀ x ∈ Set.Ioo (1 : ℝ) 2,
      HasDerivWithinAt H2 (G x) (Set.Ioi x) x := fun x hx =>
    (hasDerivAt_H2 (by linarith [hx.1]) (by linarith [hx.1])
      (by intro h; linarith [hx.1, sub_eq_zero.1 h])).hasDerivWithinAt
  have hL : ∫ s in (2 / 3 : ℝ)..1, G s = H2 1 - H2 (2 / 3) :=
    integral_eq_sub_of_hasDeriv_right_of_le (by norm_num)
      (continuousOn_H2.mono (Set.Icc_subset_Icc le_rfl (by norm_num))) hderivL
      (intervalIntegrable_G le_rfl (by norm_num) (by norm_num))
  have hR : ∫ s in (1 : ℝ)..2, G s = H2 2 - H2 1 :=
    integral_eq_sub_of_hasDeriv_right_of_le (by norm_num)
      (continuousOn_H2.mono (Set.Icc_subset_Icc (by norm_num) le_rfl)) hderivR
      (intervalIntegrable_G (by norm_num) le_rfl (by norm_num))
  have hi1 : IntervalIntegrable G volume (2 / 3) 1 :=
    intervalIntegrable_G le_rfl (by norm_num) (by norm_num)
  have hi2 : IntervalIntegrable G volume 1 2 :=
    intervalIntegrable_G (by norm_num) le_rfl (by norm_num)
  rw [hae, ← integral_add_adjacent_intervals hi1 hi2, hL, hR]
  ring

theorem intervalIntegrable_s_mul_Fs_low :
    IntervalIntegrable (fun s : ℝ => s * Fs s) volume 0 (2 / 3) := by
  have hint : IntervalIntegrable
      (fun s : ℝ => 2 * s ^ 4 / (3 * (s ^ 2 - 1) ^ 2) - 2 * s ^ 4 / 27) volume 0 (2 / 3) := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2 / 3), Set.mem_Icc] at hx
    have hlt : (3 : ℝ) * (x ^ 2 - 1) ^ 2 ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero 2 (by intro h; nlinarith [hx.1, hx.2]))
    exact ContinuousAt.continuousWithinAt (by fun_prop (disch := assumption))
  refine (intervalIntegrable_congr ?_).mp hint
  intro s hs
  rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 2 / 3), Set.mem_Ioc] at hs
  exact (s_mul_Fs_le hs.1.le hs.2).symm

theorem intervalIntegrable_s_mul_Fs_high :
    IntervalIntegrable (fun s : ℝ => s * Fs s) volume (2 / 3) 2 := by
  refine (intervalIntegrable_G le_rfl le_rfl (by norm_num)).congr_ae ?_
  have hne : ∀ᵐ x : ℝ, x ≠ 1 := by rw [MeasureTheory.ae_iff]; simp
  have : ∀ᵐ x ∂(volume.restrict (Set.uIoc (2 / 3 : ℝ) 2)), x ≠ 1 :=
    MeasureTheory.ae_restrict_of_ae hne
  filter_upwards [this, MeasureTheory.ae_restrict_mem measurableSet_uIoc] with x hx hmem
  rw [Set.uIoc_of_le (by norm_num : (2 / 3 : ℝ) ≤ 2), Set.mem_Ioc] at hmem
  exact (s_mul_Fs_gt hmem.1 hx).symm

/-- **PROVED.**  The outer `s`-integral in closed form.  The `log 5` produced by
each half separately cancels in the sum. -/
theorem integral_s_Fs : ∫ s in (0 : ℝ)..2, s * Fs s = 727 / 270 - 5 / 8 * Real.log 3 := by
  have hsplit : (∫ s in (0 : ℝ)..(2 / 3), s * Fs s) + (∫ s in (2 / 3 : ℝ)..2, s * Fs s)
      = ∫ s in (0 : ℝ)..2, s * Fs s :=
    integral_add_adjacent_intervals intervalIntegrable_s_mul_Fs_low
      intervalIntegrable_s_mul_Fs_high
  have hlog5 : Real.log (5 / 3 : ℝ) = Real.log 5 - Real.log 3 :=
    Real.log_div (by norm_num) (by norm_num)
  have hlog3 : Real.log (1 / 3 : ℝ) = -Real.log 3 := by
    rw [one_div, Real.log_inv]
  have e1 : H1 0 = 0 := by unfold H1; norm_num
  have e2 : H1 (2 / 3) = 27638 / 32805 - 1 / 2 * Real.log 5 := by
    unfold H1
    rw [show (1 : ℝ) - 2 / 3 = 1 / 3 by norm_num, show (1 : ℝ) + 2 / 3 = 5 / 3 by norm_num,
      hlog3, hlog5]
    ring
  have e3 : H2 2 = 1289 / 540 - 9 / 16 * Real.log 3 := by
    unfold H2
    rw [show (2 : ℝ) + 1 = 3 by norm_num, show 2 * (2 : ℝ) - 1 = 3 by norm_num,
      show (2 : ℝ) - 1 = 1 by norm_num, Real.log_one]
    ring
  have e4 : H2 (2 / 3) = 70457 / 131220 + 1 / 16 * Real.log 3 - 1 / 2 * Real.log 5 := by
    unfold H2
    rw [show (2 / 3 : ℝ) + 1 = 5 / 3 by norm_num,
      show 2 * (2 / 3 : ℝ) - 1 = 1 / 3 by norm_num,
      show (2 / 3 : ℝ) - 1 = -(1 / 3) by norm_num, Real.log_neg_eq_log, hlog3, hlog5]
    ring
  rw [← hsplit, integral_low, integral_high, e1, e2, e3, e4]
  ring

/-! #### The Tonelli swap

`VERDICT.md`'s decisive move is "integrating over `a` **first**, at fixed `s`".
In the natural `(a, c) ↦ (a, s)` parametrisation the integral comes out with `a`
outermost, so that move is an exchange of the order of integration over the
non-rectangular region

    faceRegion = { (a,s) : a ∈ (0,1], s ∈ (0,2), a₀ s ≤ a }.

Its horizontal slices (fixed `a`) are `faceSliceS a = {s ∈ (0,2) : a₀ s ≤ a}` —
which is where the `√(1±3a)` limits of `reference/route1_closed_a.py` come from —
and its vertical slices (fixed `s`) are `[a₀ s, 1]`, the domain of `F`.

This is done in `ENNReal` (Tonelli), so it needs measurability only, no
integrability side conditions. -/

theorem continuous_a0 : Continuous a0 := by
  unfold a0
  exact (((continuous_pow 2).sub continuous_const).abs).div_const 3

theorem a0_nonneg (s : ℝ) : 0 ≤ a0 s := by
  unfold a0; positivity

theorem a0_lt_one {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 2) : a0 s < 1 := by
  obtain ⟨h0, h2⟩ := hs
  unfold a0
  rw [div_lt_one (by norm_num), abs_lt]
  constructor <;> nlinarith

/-- The `(a,s)` domain of the face-`b` computation. -/
def faceRegion : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Set.Ioc (0 : ℝ) 1 ∧ p.2 ∈ Set.Ioo (0 : ℝ) 2 ∧ a0 p.2 ≤ p.1}

/-- Horizontal slice: the admissible `s` at fixed `a`. -/
def faceSliceS (a : ℝ) : Set ℝ := {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 2 ∧ a0 t ≤ a}

/-- Vertical slice: the admissible `a` at fixed `s`. -/
def faceSliceA (s : ℝ) : Set ℝ := {b : ℝ | b ∈ Set.Ioc (0 : ℝ) 1 ∧ a0 s ≤ b}

theorem measurableSet_faceSliceA (s : ℝ) : MeasurableSet (faceSliceA s) := by
  have h : faceSliceA s = Set.Ioc (0 : ℝ) 1 ∩ Set.Ici (a0 s) := by
    ext b; simp only [faceSliceA, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Ici]
  rw [h]; exact measurableSet_Ioc.inter measurableSet_Ici

theorem measurableSet_faceSliceS (a : ℝ) : MeasurableSet (faceSliceS a) := by
  have h : faceSliceS a = Set.Ioo (0 : ℝ) 2 ∩ (a0 ⁻¹' Set.Iic a) := by
    ext t; simp only [faceSliceS, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_Iic]
  rw [h]
  exact measurableSet_Ioo.inter (continuous_a0.measurable measurableSet_Iic)

theorem measurableSet_faceRegion : MeasurableSet faceRegion := by
  have h : faceRegion = ((Prod.fst ⁻¹' Set.Ioc (0 : ℝ) 1)
      ∩ (Prod.snd ⁻¹' Set.Ioo (0 : ℝ) 2)) ∩ {p : ℝ × ℝ | a0 p.2 ≤ p.1} := by
    ext p
    simp only [faceRegion, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
    tauto
  rw [h]
  exact ((measurable_fst measurableSet_Ioc).inter (measurable_snd measurableSet_Ioo)).inter
    (measurableSet_le (continuous_a0.measurable.comp measurable_snd) measurable_fst)

/-- Vertical slice: at fixed `s ∈ (0,2)` the admissible `a` are `[a₀ s, 1]`, up
to the single point `a = 0` (which only occurs at `s = 1`, where `a₀ = 0`). -/
theorem faceSliceA_ae (s : ℝ) : faceSliceA s =ᵐ[volume] Set.Icc (a0 s) 1 := by
  have hsub : faceSliceA s ⊆ Set.Icc (a0 s) 1 := by
    rintro a ⟨⟨-, h2⟩, h3⟩
    exact Set.mem_Icc.2 ⟨h3, h2⟩
  rw [MeasureTheory.ae_eq_set]
  refine ⟨by rw [Set.sdiff_eq_empty.2 hsub, measure_empty], ?_⟩
  refine measure_mono_null ?_ (measure_singleton (0 : ℝ))
  rintro a ⟨ha1, ha2⟩
  rw [Set.mem_Icc] at ha1
  rw [Set.mem_singleton_iff]
  by_contra hne
  exact ha2 ⟨⟨lt_of_le_of_ne (le_trans (a0_nonneg s) ha1.1) (Ne.symm hne), ha1.2⟩, ha1.1⟩

/-- **PROVED — the Tonelli swap.**  Exchanging the order of integration over
`faceRegion`: outer `a`, inner `s` becomes outer `s`, inner `a ∈ [a₀ s, 1]`.
This is the step that lets `F(s) = ∫_{a₀ s}^1 …` appear at all. -/
theorem lintegral_faceRegion_swap {f : ℝ → ℝ → ENNReal}
    (hf : Measurable (Function.uncurry f)) :
    ∫⁻ a in Set.Ioc (0 : ℝ) 1, ∫⁻ s in faceSliceS a, f a s
      = ∫⁻ s in Set.Ioo (0 : ℝ) 2, ∫⁻ a in Set.Icc (a0 s) 1, f a s := by
  classical
  set F : ℝ → ℝ → ENNReal :=
    fun a s => faceRegion.indicator (Function.uncurry f) (a, s) with hFdef
  have hFapp : ∀ a s : ℝ, F a s = faceRegion.indicator (Function.uncurry f) (a, s) :=
    fun _ _ => rfl
  have hFm : Measurable (Function.uncurry F) := by
    have huc : Function.uncurry F = faceRegion.indicator (Function.uncurry f) := by
      funext p
      simp only [hFdef, Function.uncurry]
    rw [huc]
    exact hf.indicator measurableSet_faceRegion
  -- rows
  have hrow : ∀ a : ℝ, ∫⁻ s, F a s
      = (Set.Ioc (0 : ℝ) 1).indicator (fun a => ∫⁻ s in faceSliceS a, f a s) a := by
    intro a
    by_cases ha : a ∈ Set.Ioc (0 : ℝ) 1
    · rw [Set.indicator_of_mem ha, ← lintegral_indicator (measurableSet_faceSliceS a)]
      refine lintegral_congr fun s => ?_
      by_cases hs : s ∈ faceSliceS a
      · have hin : ((a, s) : ℝ × ℝ) ∈ faceRegion := ⟨ha, hs.1, hs.2⟩
        rw [Set.indicator_of_mem hs, hFapp, Set.indicator_of_mem hin]
        rfl
      · rw [Set.indicator_of_notMem hs, hFapp,
          Set.indicator_of_notMem
            (fun hmem : ((a, s) : ℝ × ℝ) ∈ faceRegion => hs ⟨hmem.2.1, hmem.2.2⟩)]
    · rw [Set.indicator_of_notMem ha]
      have hz : (fun s => F a s) = fun _ => (0 : ENNReal) := by
        funext s
        rw [hFapp, Set.indicator_of_notMem
          (fun hmem : ((a, s) : ℝ × ℝ) ∈ faceRegion => ha hmem.1)]
      rw [hz]
      simp
  -- columns
  have hcol : ∀ s : ℝ, ∫⁻ a, F a s
      = (Set.Ioo (0 : ℝ) 2).indicator (fun s => ∫⁻ a in Set.Icc (a0 s) 1, f a s) s := by
    intro s
    by_cases hs : s ∈ Set.Ioo (0 : ℝ) 2
    · rw [Set.indicator_of_mem hs]
      have hV : ∫⁻ a, F a s = ∫⁻ a in faceSliceA s, f a s := by
        rw [← lintegral_indicator (measurableSet_faceSliceA s)]
        refine lintegral_congr fun a => ?_
        by_cases ha : a ∈ faceSliceA s
        · have hin : ((a, s) : ℝ × ℝ) ∈ faceRegion := ⟨ha.1, hs, ha.2⟩
          rw [Set.indicator_of_mem ha, hFapp, Set.indicator_of_mem hin]
          rfl
        · rw [Set.indicator_of_notMem ha, hFapp,
            Set.indicator_of_notMem
              (fun hmem : ((a, s) : ℝ × ℝ) ∈ faceRegion => ha ⟨hmem.1, hmem.2.2⟩)]
      rw [hV, setLIntegral_congr (faceSliceA_ae s)]
    · rw [Set.indicator_of_notMem hs]
      have hz : (fun a => F a s) = fun _ => (0 : ENNReal) := by
        funext a
        rw [hFapp, Set.indicator_of_notMem
          (fun hmem : ((a, s) : ℝ × ℝ) ∈ faceRegion => hs hmem.2.1)]
      rw [hz]
      simp
  calc ∫⁻ a in Set.Ioc (0 : ℝ) 1, ∫⁻ s in faceSliceS a, f a s
      = ∫⁻ a, (Set.Ioc (0 : ℝ) 1).indicator
          (fun a => ∫⁻ s in faceSliceS a, f a s) a :=
        (lintegral_indicator measurableSet_Ioc _).symm
    _ = ∫⁻ a, ∫⁻ s, F a s := lintegral_congr fun a => (hrow a).symm
    _ = ∫⁻ s, ∫⁻ a, F a s := lintegral_lintegral_swap hFm.aemeasurable
    _ = ∫⁻ s, (Set.Ioo (0 : ℝ) 2).indicator
          (fun s => ∫⁻ a in Set.Icc (a0 s) 1, f a s) s := lintegral_congr fun s => hcol s
    _ = ∫⁻ s in Set.Ioo (0 : ℝ) 2, ∫⁻ a in Set.Icc (a0 s) 1, f a s :=
        lintegral_indicator measurableSet_Ioo _

/-! #### The integrand, and what the swap buys

`bandLen a s` is the clipped length of the admissible `d`-interval at `(a,s)`
(`Δ₄_face_b_pos_iff` for the interval, `L1` for "never clips above").  The full
`(a,s)` integrand of `S_b` carries the Jacobian `2s/(3a)` of `c = (1-s²)/(3a)`.
After the swap the inner integral is exactly `F(s)`. -/

/-- Clipped length of the admissible `d`-interval, in units of `u = 27a²`. -/
noncomputable def bandLen (a s : ℝ) : ℝ :=
  Kp s / (27 * a ^ 2) + min (Km s / (27 * a ^ 2)) 1

/-- The `(a,s)` integrand of `S_b`, Jacobian included. -/
noncomputable def faceIntegrand (a s : ℝ) : ENNReal :=
  ENNReal.ofReal (bandLen a s / a * (2 * s / 3))

theorem continuous_Kp : Continuous Kp := by
  unfold Kp; fun_prop

theorem continuous_Km : Continuous Km := by
  unfold Km; fun_prop

theorem measurable_faceIntegrand : Measurable (Function.uncurry faceIntegrand) := by
  have h : Function.uncurry faceIntegrand = fun p : ℝ × ℝ =>
      ENNReal.ofReal ((Kp p.2 / (27 * p.1 ^ 2)
        + min (Km p.2 / (27 * p.1 ^ 2)) 1) / p.1 * (2 * p.2 / 3)) := by
    funext p; rfl
  rw [h]
  have h1 : Measurable fun p : ℝ × ℝ => Kp p.2 / (27 * p.1 ^ 2) :=
    (continuous_Kp.measurable.comp measurable_snd).div (by fun_prop)
  have h2 : Measurable fun p : ℝ × ℝ => Km p.2 / (27 * p.1 ^ 2) :=
    (continuous_Km.measurable.comp measurable_snd).div (by fun_prop)
  exact ENNReal.measurable_ofReal.comp
    (((h1.add (h2.min measurable_const)).div measurable_fst).mul (by fun_prop))

/-- The clipped band length is nonnegative: if the bottom does not clip we get
`(K₊+K₋)/(27a²) = 4s³/(27a²) ≥ 0` by `Kp_add_Km`, and if it does we get
`K₊/(27a²) + 1 ≥ 0` since `K₊ = (s-1)²(2s+1) ≥ 0`. -/
theorem bandLen_nonneg {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) : 0 ≤ bandLen a s := by
  have hu : (0 : ℝ) < 27 * a ^ 2 := by positivity
  have hKp : 0 ≤ Kp s := by unfold Kp; nlinarith [sq_nonneg (s - 1)]
  unfold bandLen
  rcases le_total (Km s / (27 * a ^ 2)) 1 with h | h
  · have hK : Km s = 4 * s ^ 3 - Kp s := by linarith [Kp_add_Km s]
    have hsum : Kp s / (27 * a ^ 2) + (4 * s ^ 3 - Kp s) / (27 * a ^ 2)
        = 4 * s ^ 3 / (27 * a ^ 2) := by field_simp; ring
    rw [min_eq_left h, hK, hsum]
    positivity
  · rw [min_eq_right h]
    have : 0 ≤ Kp s / (27 * a ^ 2) := div_nonneg hKp hu.le
    linarith

theorem continuousOn_bandLen_div (s : ℝ) {u v : ℝ} (hu : 0 < u) :
    ContinuousOn (fun a : ℝ => bandLen a s / a) (Set.Icc u v) := by
  have hxne : ∀ x ∈ Set.Icc u v, x ≠ 0 := fun x hx => ne_of_gt (lt_of_lt_of_le hu hx.1)
  have hden : ∀ x ∈ Set.Icc u v, (27 : ℝ) * x ^ 2 ≠ 0 :=
    fun x hx => mul_ne_zero (by norm_num) (pow_ne_zero 2 (hxne x hx))
  have h1 : ContinuousOn (fun a : ℝ => Kp s / (27 * a ^ 2)) (Set.Icc u v) :=
    continuousOn_const.div (by fun_prop) hden
  have h2 : ContinuousOn (fun a : ℝ => Km s / (27 * a ^ 2)) (Set.Icc u v) :=
    continuousOn_const.div (by fun_prop) hden
  have hone : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc u v) := continuousOn_const
  unfold bandLen
  exact (h1.add (h2.inf hone)).div (continuousOn_id' _) hxne

/-- **PROVED.**  `F(s) ≥ 0` — it is an integral of the nonnegative band length. -/
theorem Fs_nonneg {s : ℝ} (h0 : 0 < s) (h2 : s < 2) (hs1 : s ≠ 1) : 0 ≤ Fs s := by
  have ha1 : a0 s ≤ 1 := (a0_lt_one ⟨h0, h2⟩).le
  rw [Fs_eq_face_integral h0 h2 hs1]
  refine intervalIntegral.integral_nonneg ha1 fun x hx => ?_
  have hxp : 0 < x := lt_of_lt_of_le (by
    rcases lt_or_eq_of_le (a0_nonneg s) with h | h
    · exact h
    · exfalso
      apply hs1
      have : |s ^ 2 - 1| = 0 := by unfold a0 at h; linarith [h]
      have := abs_eq_zero.1 this
      nlinarith) hx.1
  exact div_nonneg (bandLen_nonneg hxp h0.le) hxp.le

/-- **PROVED — the inner integral after the swap is exactly `(2s/3)·F(s)`.** -/
theorem inner_lintegral_eq {s : ℝ} (h0 : 0 < s) (h2 : s < 2) (hs1 : s ≠ 1) :
    ∫⁻ a in Set.Icc (a0 s) 1, faceIntegrand a s
      = ENNReal.ofReal (2 / 3 * (s * Fs s)) := by
  have ha0 : 0 < a0 s := by
    rcases lt_or_eq_of_le (a0_nonneg s) with h | h
    · exact h
    · exfalso
      apply hs1
      have habs : |s ^ 2 - 1| = 0 := by unfold a0 at h; linarith [h]
      have := abs_eq_zero.1 habs
      nlinarith
  have ha1 : a0 s ≤ 1 := (a0_lt_one ⟨h0, h2⟩).le
  have hcont : ContinuousOn (fun a : ℝ => bandLen a s / a * (2 * s / 3))
      (Set.Icc (a0 s) 1) := (continuousOn_bandLen_div s ha0).mul continuousOn_const
  have hint : IntegrableOn (fun a : ℝ => bandLen a s / a * (2 * s / 3)) (Set.Icc (a0 s) 1) :=
    hcont.integrableOn_Icc
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Icc (a0 s) 1)]
      fun a : ℝ => bandLen a s / a * (2 * s / 3) := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    refine Filter.Eventually.of_forall fun a ha => ?_
    have hap : 0 < a := lt_of_lt_of_le ha0 ha.1
    simp only [Pi.zero_apply]
    have := bandLen_nonneg hap h0.le
    positivity
  unfold faceIntegrand
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha1,
    intervalIntegral.integral_mul_const]
  simp only [bandLen]
  rw [← Fs_eq_face_integral h0 h2 hs1]
  ring

/-- **PROVED — the post-swap evaluation.**  Combining `inner_lintegral_eq` with
the closed form `integral_s_Fs` turns the swapped double integral into
`(2/3)∫₀² s F(s) ds`. -/
theorem post_swap_eval :
    ∫⁻ s in Set.Ioo (0 : ℝ) 2, ∫⁻ a in Set.Icc (a0 s) 1, faceIntegrand a s
      = ENNReal.ofReal (2 / 3 * ∫ s in (0 : ℝ)..2, s * Fs s) := by
  have hne : ∀ᵐ x : ℝ, x ≠ 1 := by rw [MeasureTheory.ae_iff]; simp
  have hcongr : ∫⁻ s in Set.Ioo (0 : ℝ) 2, ∫⁻ a in Set.Icc (a0 s) 1, faceIntegrand a s
      = ∫⁻ s in Set.Ioo (0 : ℝ) 2, ENNReal.ofReal (2 / 3 * (s * Fs s)) := by
    refine lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_of_ae hne,
      MeasureTheory.ae_restrict_mem measurableSet_Ioo] with s hs hmem
    exact inner_lintegral_eq hmem.1 hmem.2 hs
  rw [hcongr]
  -- the outer integrand is integrable and nonnegative
  have hsplit : IntervalIntegrable (fun s : ℝ => s * Fs s) volume 0 2 :=
    intervalIntegrable_s_mul_Fs_low.trans intervalIntegrable_s_mul_Fs_high
  have hint : IntegrableOn (fun s : ℝ => 2 / 3 * (s * Fs s)) (Set.Ioo (0 : ℝ) 2) := by
    have h1 : IntegrableOn (fun s : ℝ => s * Fs s) (Set.Ioc (0 : ℝ) 2) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).1 hsplit
    exact (h1.mono_set Set.Ioo_subset_Ioc_self).const_mul (2 / 3 : ℝ)
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 2)] fun s : ℝ => 2 / 3 * (s * Fs s) := by
    filter_upwards [MeasureTheory.ae_restrict_of_ae hne,
      MeasureTheory.ae_restrict_mem measurableSet_Ioo] with s hs hmem
    have := Fs_nonneg hmem.1 hmem.2 hs
    have h0 : (0 : ℝ) < s := hmem.1
    simp only [Pi.zero_apply]
    positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2),
    intervalIntegral.integral_const_mul]

/-! #### Step 1 of the pre-swap identity: the `a ↔ -a` symmetry -/

/-- Substituting `x ↦ -x` in the roots sends `a x³ + x² + c x + d` to
`-a x³ + x² - c x + d`, and the discriminant is unchanged.  A `ring` identity. -/
theorem Δ₄_face_b_symm (a c d : ℝ) : Δ₄ (-a) 1 (-c) d = Δ₄ a 1 c d := by
  unfold Δ₄; ring

/-- The reflection `(a,c,d) ↦ (-a,-c,d)`. -/
def faceRefl : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ :=
  Prod.map (fun a : ℝ => -a) (Prod.map (fun c : ℝ => -c) (id : ℝ → ℝ))

theorem measurePreserving_faceRefl : MeasurePreserving faceRefl volume volume :=
  (Measure.measurePreserving_neg (volume : Measure ℝ)).prod
    ((Measure.measurePreserving_neg (volume : Measure ℝ)).prod (MeasurePreserving.id _))

/-- `FaceB` with the leading coefficient positive / negative. -/
def FaceBPos : Set (ℝ × ℝ × ℝ) := {p | p ∈ FaceB ∧ 0 < p.1}

def FaceBNeg : Set (ℝ × ℝ × ℝ) := {p | p ∈ FaceB ∧ p.1 < 0}

theorem faceRefl_preimage_pos : faceRefl ⁻¹' FaceBPos = FaceBNeg := by
  ext ⟨a, c, d⟩
  simp only [faceRefl, FaceBPos, FaceBNeg, FaceB, Set.mem_preimage, Set.mem_ofPred_eq,
    Prod.map_apply, id_eq, Set.mem_Icc, Δ₄_face_b_symm]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5, h6⟩, h7⟩
    exact ⟨⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, h5, h6⟩,
      by linarith⟩
  · rintro ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5, h6⟩, h7⟩
    exact ⟨⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, h5, h6⟩,
      by linarith⟩

theorem measurableSet_FaceB : MeasurableSet FaceB := by
  have hc : Continuous fun p : ℝ × ℝ × ℝ => Δ₄ p.1 1 p.2.1 p.2.2 := by
    unfold Δ₄; fun_prop
  have h : FaceB = ((Prod.fst ⁻¹' Set.Icc (-1 : ℝ) 1)
      ∩ ((fun p : ℝ × ℝ × ℝ => p.2.1) ⁻¹' Set.Icc (-1 : ℝ) 1)
      ∩ ((fun p : ℝ × ℝ × ℝ => p.2.2) ⁻¹' Set.Icc (-1 : ℝ) 1))
      ∩ {p : ℝ × ℝ × ℝ | 0 < Δ₄ p.1 1 p.2.1 p.2.2} := by
    ext p; simp only [FaceB, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]; tauto
  rw [h]
  exact (((measurable_fst measurableSet_Icc).inter
      ((measurable_fst.comp measurable_snd) measurableSet_Icc)).inter
      ((measurable_snd.comp measurable_snd) measurableSet_Icc)).inter
    (measurableSet_lt measurable_const hc.measurable)

theorem measurableSet_FaceBPos : MeasurableSet FaceBPos :=
  measurableSet_FaceB.inter (measurableSet_lt measurable_const measurable_fst)

theorem measurableSet_FaceBNeg : MeasurableSet FaceBNeg :=
  measurableSet_FaceB.inter (measurableSet_lt measurable_fst measurable_const)

theorem volume_fst_eq_zero :
    (volume : Measure (ℝ × ℝ × ℝ)) {p : ℝ × ℝ × ℝ | p.1 = 0} = 0 := by
  have h : {p : ℝ × ℝ × ℝ | p.1 = 0}
      = ({0} : Set ℝ) ×ˢ (Set.univ : Set (ℝ × ℝ)) := by
    ext p; simp
  rw [h, show (volume : Measure (ℝ × ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
    Measure.prod_prod]
  simp

/-- **PROVED.**  The `±a` symmetry: `vol₃(FaceB) = 2 · vol₃(FaceB ∩ {a > 0})`. -/
theorem volume_FaceB_eq_two_mul_pos : volume FaceB = 2 * volume FaceBPos := by
  have hneg : volume FaceBNeg = volume FaceBPos := by
    rw [← faceRefl_preimage_pos, measurePreserving_faceRefl.measure_preimage
      measurableSet_FaceBPos.nullMeasurableSet]
  have hdisj : Disjoint FaceBPos FaceBNeg := by
    rw [Set.disjoint_left]
    rintro p ⟨-, hp⟩ ⟨-, hq⟩
    linarith
  have hsub : FaceB \ (FaceBPos ∪ FaceBNeg) ⊆ {p : ℝ × ℝ × ℝ | p.1 = 0} := by
    rintro p ⟨hp, hq⟩
    rw [Set.mem_ofPred_eq]
    rcases lt_trichotomy p.1 0 with h | h | h
    · exact absurd (Or.inr ⟨hp, h⟩) hq
    · exact h
    · exact absurd (Or.inl ⟨hp, h⟩) hq
  have hnull : volume (FaceB \ (FaceBPos ∪ FaceBNeg)) = 0 :=
    measure_mono_null hsub volume_fst_eq_zero
  have hunion : volume (FaceBPos ∪ FaceBNeg) = volume FaceB := by
    refine le_antisymm (measure_mono (Set.union_subset (fun p hp => hp.1) fun p hp => hp.1)) ?_
    calc volume FaceB
        ≤ volume ((FaceBPos ∪ FaceBNeg) ∪ (FaceB \ (FaceBPos ∪ FaceBNeg))) :=
          measure_mono (fun p hp => by
            by_cases h : p ∈ FaceBPos ∪ FaceBNeg
            · exact Or.inl h
            · exact Or.inr ⟨hp, h⟩)
      _ ≤ volume (FaceBPos ∪ FaceBNeg) + volume (FaceB \ (FaceBPos ∪ FaceBNeg)) :=
          measure_union_le _ _
      _ = volume (FaceBPos ∪ FaceBNeg) := by rw [hnull, add_zero]
  rw [← hunion, measure_union hdisj measurableSet_FaceBNeg, hneg, two_mul]

/-! #### Step 2: the `(c,d)`-slice at fixed `a ∈ (0,1]`

The pleasant fact that makes this clean: for `a > 0` and `s = √(1-3ac)`,

    a₀ s = |s² - 1|/3 = |−3ac|/3 = a·|c|,

so the window constraint `|c| ≤ 1` is *exactly* `a₀ s ≤ a`, which is exactly the
hypothesis under which `L1` says the band never clips above. -/

/-- `s` as a function of `(a,c)` on the face. -/
noncomputable def sOf (a c : ℝ) : ℝ := Real.sqrt (1 - 3 * a * c)

/-- Largest admissible `c` at fixed `a > 0`: `c ≤ 1` and `1 - 3ac ≥ 0`. -/
noncomputable def cmax (a : ℝ) : ℝ := min 1 (1 / (3 * a))

/-- Bottom of the admissible `d`-interval, clipped to the window. -/
noncomputable def dLo (a c : ℝ) : ℝ := max (-(Km (sOf a c)) / (27 * a ^ 2)) (-1)

/-- Top of the admissible `d`-interval (never clipped, by `L1`). -/
noncomputable def dHi (a c : ℝ) : ℝ := Kp (sOf a c) / (27 * a ^ 2)

theorem continuous_sOf (a : ℝ) : Continuous (sOf a) := by
  unfold sOf; fun_prop

theorem continuous_dLo (a : ℝ) : Continuous (dLo a) := by
  unfold dLo
  exact ((continuous_Km.comp (continuous_sOf a)).neg.div_const _).max continuous_const

theorem continuous_dHi (a : ℝ) : Continuous (dHi a) := by
  unfold dHi
  exact (continuous_Kp.comp (continuous_sOf a)).div_const _

theorem one_sub_nonneg_of_le_cmax {a c : ℝ} (ha : 0 < a) (hc : c ≤ cmax a) :
    0 ≤ 1 - 3 * a * c := by
  have h : c ≤ 1 / (3 * a) := le_trans hc (min_le_right _ _)
  have h3a : (0 : ℝ) < 3 * a := by linarith
  rw [le_div_iff₀ h3a] at h
  nlinarith

theorem neg_one_le_cmax {a : ℝ} (ha : 0 < a) : (-1 : ℝ) ≤ cmax a := by
  have h3a : (0 : ℝ) < 3 * a := by linarith
  have : (0 : ℝ) < 1 / (3 * a) := by positivity
  unfold cmax
  exact le_min (by norm_num) (by linarith)

theorem cmax_le_one {a : ℝ} : cmax a ≤ 1 := min_le_left _ _

/-- **The key identity of the substitution**: `a₀ (√(1-3ac)) = a |c|` for `a > 0`. -/
theorem a0_sOf {a c : ℝ} (ha : 0 < a) (h : 0 ≤ 1 - 3 * a * c) : a0 (sOf a c) = a * |c| := by
  have hsq : sOf a c ^ 2 = 1 - 3 * a * c := Real.sq_sqrt h
  unfold a0
  rw [hsq, show 1 - 3 * a * c - 1 = -(3 * a * c) by ring, abs_neg, abs_mul, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 3), abs_of_pos ha]
  ring

/-- **`L1` in `(a,c)` coordinates**: the band never clips above. -/
theorem dHi_le_one {a c : ℝ} (ha : 0 < a) (hc1 : -1 ≤ c) (hc2 : c ≤ 1)
    (h : 0 ≤ 1 - 3 * a * c) : dHi a c ≤ 1 := by
  have hL := L1 (sOf a c)
  rw [a0_sOf ha h] at hL
  have hexp : (a * |c|) ^ 2 = a ^ 2 * c ^ 2 := by rw [mul_pow, sq_abs]
  rw [hexp] at hL
  have hc2sq : c ^ 2 ≤ 1 := by nlinarith
  unfold dHi
  rw [div_le_one (by positivity)]
  nlinarith [hL, mul_le_mul_of_nonneg_left hc2sq (sq_nonneg a)]

theorem Kp_sOf_nonneg (a c : ℝ) : 0 ≤ Kp (sOf a c) := by
  have hs : 0 ≤ sOf a c := Real.sqrt_nonneg _
  unfold Kp
  nlinarith [sq_nonneg (sOf a c - 1)]

theorem dLo_le_dHi {a c : ℝ} (ha : 0 < a) : dLo a c ≤ dHi a c := by
  have hs : 0 ≤ sOf a c := Real.sqrt_nonneg _
  have hu : (0 : ℝ) < 27 * a ^ 2 := by positivity
  have hsum : Kp (sOf a c) + Km (sOf a c) = 4 * sOf a c ^ 3 := Kp_add_Km _
  have hKp := Kp_sOf_nonneg a c
  unfold dLo dHi
  refine max_le ?_ ?_
  · gcongr
    nlinarith [pow_nonneg hs 3]
  · linarith [div_nonneg hKp hu.le]

/-- The band width is `bandLen`. -/
theorem dHi_sub_dLo {a : ℝ} (ha : 0 < a) (c : ℝ) :
    dHi a c - dLo a c = bandLen a (sOf a c) := by
  have hu : (0 : ℝ) < 27 * a ^ 2 := by positivity
  have hd : -(Km (sOf a c)) / (27 * a ^ 2) = -(Km (sOf a c) / (27 * a ^ 2)) := by ring
  unfold dHi dLo bandLen
  rcases le_total (-(Km (sOf a c)) / (27 * a ^ 2)) (-1 : ℝ) with h | h
  · rw [max_eq_right h, min_eq_right (by rw [hd] at h; linarith)]
    ring
  · rw [max_eq_left h, min_eq_left (by rw [hd] at h; linarith)]
    ring

/-! ##### The slice, up to null sets -/

theorem volume_fst_eq_const (x : ℝ) :
    (volume : Measure (ℝ × ℝ)) {q : ℝ × ℝ | q.1 = x} = 0 := by
  have h : {q : ℝ × ℝ | q.1 = x} = ({x} : Set ℝ) ×ˢ (Set.univ : Set ℝ) := by ext q; simp
  rw [h, show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
    Measure.prod_prod]
  simp

theorem volume_snd_eq_const (y : ℝ) :
    (volume : Measure (ℝ × ℝ)) {q : ℝ × ℝ | q.2 = y} = 0 := by
  have h : {q : ℝ × ℝ | q.2 = y} = (Set.univ : Set ℝ) ×ˢ ({y} : Set ℝ) := by ext q; simp
  rw [h, show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
    Measure.prod_prod]
  simp

theorem region_subset_sliceB {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    regionBetween (dLo a) (dHi a) (Set.Ico (-1) (cmax a)) ⊆ Prod.mk a ⁻¹' FaceB := by
  rintro ⟨c, d⟩ ⟨⟨hc1, hc2⟩, hd1, hd2⟩
  have hcle : c ≤ cmax a := hc2.le
  have hnn : 0 ≤ 1 - 3 * a * c := one_sub_nonneg_of_le_cmax ha hcle
  have hc2' : c ≤ 1 := le_trans hcle cmax_le_one
  have hs : 0 ≤ sOf a c := Real.sqrt_nonneg _
  have hsq : sOf a c ^ 2 = 1 - 3 * a * c := Real.sq_sqrt hnn
  have hdHi : dHi a c ≤ 1 := dHi_le_one ha hc1 hc2' hnn
  have hdLo : (-1 : ℝ) ≤ dLo a c := le_max_right _ _
  have hu : (0 : ℝ) < 27 * a ^ 2 := by positivity
  refine ⟨⟨by linarith, ha1⟩, ⟨hc1, hc2'⟩, ⟨by linarith, by linarith⟩, ?_⟩
  refine (Δ₄_face_b_pos_iff (ne_of_gt ha) hs hsq).2 ⟨?_, ?_⟩
  · have h := lt_of_le_of_lt (le_max_left (-(Km (sOf a c)) / (27 * a ^ 2)) (-1)) hd1
    rw [div_lt_iff₀ hu] at h
    linarith
  · have h := hd2
    unfold dHi at h
    rw [lt_div_iff₀ hu] at h
    linarith

theorem sliceB_sdiff_subset {a : ℝ} (ha : 0 < a) :
    (Prod.mk a ⁻¹' FaceB) \ regionBetween (dLo a) (dHi a) (Set.Ico (-1) (cmax a))
      ⊆ {q : ℝ × ℝ | q.1 = cmax a} ∪ {q : ℝ × ℝ | q.2 = -1} := by
  rintro ⟨c, d⟩ ⟨⟨-, ⟨hc1, hc2⟩, ⟨hd1, hd2⟩, hΔ⟩, hout⟩
  by_contra hcon
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or] at hcon
  obtain ⟨hcne, hdne⟩ := hcon
  refine hout ?_
  have hnn : 0 ≤ 1 - 3 * a * c := by
    by_contra hneg
    rw [not_le] at hneg
    exact absurd hΔ (not_lt.2 (Δ₄_face_b_neg (ne_of_gt ha) hneg).le)
  have hs : 0 ≤ sOf a c := Real.sqrt_nonneg _
  have hsq : sOf a c ^ 2 = 1 - 3 * a * c := Real.sq_sqrt hnn
  have hu : (0 : ℝ) < 27 * a ^ 2 := by positivity
  obtain ⟨hlo, hhi⟩ := (Δ₄_face_b_pos_iff (ne_of_gt ha) hs hsq).1 hΔ
  have hccm : c ≤ cmax a := by
    refine le_min hc2 ?_
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 3 * a)]
    nlinarith
  refine ⟨⟨hc1, lt_of_le_of_ne hccm hcne⟩, ?_, ?_⟩
  · refine max_lt ?_ (lt_of_le_of_ne hd1 (Ne.symm hdne))
    rw [div_lt_iff₀ hu]
    linarith
  · unfold dHi
    rw [lt_div_iff₀ hu]
    linarith

/-- **PROVED.**  The `(c,d)`-slice area at fixed `a ∈ (0,1]`. -/
theorem volume_sliceB {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    volume (Prod.mk a ⁻¹' FaceB)
      = ENNReal.ofReal (∫ c in (-1 : ℝ)..(cmax a), bandLen a (sOf a c)) := by
  have hle : (-1 : ℝ) ≤ cmax a := neg_one_le_cmax ha
  have hregion : volume (Prod.mk a ⁻¹' FaceB)
      = volume (regionBetween (dLo a) (dHi a) (Set.Ico (-1) (cmax a))) := by
    refine le_antisymm ?_ (measure_mono (region_subset_sliceB ha ha1))
    calc volume (Prod.mk a ⁻¹' FaceB)
        ≤ volume (regionBetween (dLo a) (dHi a) (Set.Ico (-1) (cmax a))
            ∪ ({q : ℝ × ℝ | q.1 = cmax a} ∪ {q : ℝ × ℝ | q.2 = -1})) := by
          refine measure_mono fun q hq => ?_
          by_cases h : q ∈ regionBetween (dLo a) (dHi a) (Set.Ico (-1) (cmax a))
          · exact Or.inl h
          · exact Or.inr (sliceB_sdiff_subset ha ⟨hq, h⟩)
      _ ≤ volume (regionBetween (dLo a) (dHi a) (Set.Ico (-1) (cmax a)))
            + volume ({q : ℝ × ℝ | q.1 = cmax a} ∪ {q : ℝ × ℝ | q.2 = -1}) :=
          measure_union_le _ _
      _ = volume (regionBetween (dLo a) (dHi a) (Set.Ico (-1) (cmax a))) := by
          have : volume ({q : ℝ × ℝ | q.1 = cmax a} ∪ {q : ℝ × ℝ | q.2 = -1}) = 0 :=
            measure_union_null (volume_fst_eq_const _) (volume_snd_eq_const _)
          rw [this, add_zero]
  rw [hregion, show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
    volume_regionBetween_eq_integral
      ((continuous_dLo a).continuousOn.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self)
      ((continuous_dHi a).continuousOn.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self)
      measurableSet_Ico (fun c _ => dLo_le_dHi ha)]
  congr 1
  rw [setIntegral_congr_fun measurableSet_Ico
    (fun c _ => by simpa using dHi_sub_dLo ha c),
    MeasureTheory.integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]

/-! #### Step 3: the substitution `c = (1-s²)/(3a)` at fixed `a` -/

/-- The `s`-range at fixed `a`: `s² ∈ [max 0 (1-3a), 1+3a]`. -/
noncomputable def sLo (a : ℝ) : ℝ := Real.sqrt (max 0 (1 - 3 * a))

noncomputable def sHi (a : ℝ) : ℝ := Real.sqrt (1 + 3 * a)

/-- The substitution map `s ↦ c`. -/
noncomputable def cOf (a s : ℝ) : ℝ := (1 - s ^ 2) / (3 * a)

theorem sLo_nonneg (a : ℝ) : 0 ≤ sLo a := Real.sqrt_nonneg _

theorem sLo_sq (a : ℝ) : sLo a ^ 2 = max 0 (1 - 3 * a) :=
  Real.sq_sqrt (le_max_left _ _)

theorem sHi_sq {a : ℝ} (ha : 0 < a) : sHi a ^ 2 = 1 + 3 * a :=
  Real.sq_sqrt (by linarith)

theorem sHi_pos {a : ℝ} (ha : 0 < a) : 0 < sHi a := Real.sqrt_pos.2 (by linarith)

theorem sHi_le_two {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) : sHi a ≤ 2 := by
  have h := sHi_sq ha
  nlinarith [sHi_pos ha]

theorem sLo_le_sHi {a : ℝ} (ha : 0 < a) : sLo a ≤ sHi a :=
  Real.sqrt_le_sqrt (max_le (by linarith) (by linarith))

theorem cOf_sHi {a : ℝ} (ha : 0 < a) : cOf a (sHi a) = -1 := by
  unfold cOf
  rw [sHi_sq ha]
  field_simp
  ring

theorem cOf_sLo {a : ℝ} (ha : 0 < a) : cOf a (sLo a) = cmax a := by
  have h3a : (0 : ℝ) < 3 * a := by linarith
  unfold cOf cmax
  rw [sLo_sq a]
  rcases le_total (1 - 3 * a) 0 with h | h
  · have hmin : min (1 : ℝ) (1 / (3 * a)) = 1 / (3 * a) := by
      refine min_eq_right ?_
      rw [div_le_one h3a]; linarith
    rw [max_eq_left h, hmin]
    ring
  · have hmin : min (1 : ℝ) (1 / (3 * a)) = 1 := by
      refine min_eq_left ?_
      rw [le_div_iff₀ h3a]; linarith
    rw [max_eq_right h, hmin]
    field_simp
    ring

theorem continuous_bandLen {a : ℝ} (ha : a ≠ 0) : Continuous (bandLen a) := by
  have hden : (27 : ℝ) * a ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 ha)
  unfold bandLen
  exact (continuous_Kp.div_const _).add ((continuous_Km.div_const _).min continuous_const)

theorem sOf_cOf {a : ℝ} (ha : 0 < a) (s : ℝ) : sOf a (cOf a s) = |s| := by
  unfold sOf cOf
  rw [show 1 - 3 * a * ((1 - s ^ 2) / (3 * a)) = s ^ 2 by field_simp; ring]
  exact Real.sqrt_sq_eq_abs s

theorem hasDerivAt_cOf (a s : ℝ) : HasDerivAt (cOf a) (-2 * s / (3 * a)) s := by
  have h : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2 * s)) s := by
    simpa using ((hasDerivAt_id s).fun_pow 2).const_sub (1 : ℝ)
  refine (h.div_const (3 * a)).congr_deriv ?_
  ring

/-- **PROVED — the substitution.**  `∫ dc` over the admissible `c` becomes
`∫ ds` over `[sLo, sHi]` with the Jacobian `2s/(3a)`. -/
theorem integral_c_eq_integral_s {a : ℝ} (ha : 0 < a) :
    ∫ c in (-1 : ℝ)..(cmax a), bandLen a (sOf a c)
      = ∫ s in (sLo a)..(sHi a), bandLen a s / a * (2 * s / 3) := by
  have hgc : Continuous fun c : ℝ => bandLen a (sOf a c) :=
    (continuous_bandLen (ne_of_gt ha)).comp (continuous_sOf a)
  have hsub := intervalIntegral.integral_deriv_smul_comp
    (a := sHi a) (b := sLo a) (f := cOf a) (f' := fun s : ℝ => -2 * s / (3 * a))
    (g := fun c : ℝ => bandLen a (sOf a c))
    (fun x _ => hasDerivAt_cOf a x) (by fun_prop) hgc
  rw [cOf_sHi ha, cOf_sLo ha] at hsub
  rw [← hsub, intervalIntegral.integral_symm (sLo a) (sHi a),
    ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le (sLo_le_sHi ha), Set.mem_Icc] at hs
  have hs0 : 0 ≤ s := le_trans (sLo_nonneg a) hs.1
  simp only [Function.comp_apply, smul_eq_mul, sOf_cOf ha, abs_of_nonneg hs0]
  field_simp

/-! #### Step 4: the `s`-range is `faceSliceS a` -/

theorem faceSliceS_ae {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    faceSliceS a =ᵐ[volume] Set.Ioo (sLo a) (sHi a) := by
  have hlo := sLo_sq a
  have hhi := sHi_sq ha
  have hlo0 := sLo_nonneg a
  have hhi0 := (sHi_pos ha).le
  have hsub1 : Set.Ioo (sLo a) (sHi a) ⊆ faceSliceS a := by
    rintro s ⟨h1, h2⟩
    have hs0 : 0 < s := lt_of_le_of_lt hlo0 h1
    refine ⟨⟨hs0, lt_of_lt_of_le h2 (sHi_le_two ha ha1)⟩, ?_⟩
    have hsq1 : max 0 (1 - 3 * a) < s ^ 2 := by nlinarith
    have hsq2 : s ^ 2 < 1 + 3 * a := by nlinarith
    unfold a0
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3), abs_le]
    constructor <;> [nlinarith [le_max_right (0 : ℝ) (1 - 3 * a)]; nlinarith]
  have hsub2 : faceSliceS a ⊆ Set.Icc (sLo a) (sHi a) := by
    rintro s ⟨⟨hs0, -⟩, hle⟩
    unfold a0 at hle
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3), abs_le] at hle
    constructor
    · have hle2 : max 0 (1 - 3 * a) ≤ s ^ 2 :=
        max_le (by positivity) (by linarith [hle.1])
      calc sLo a = Real.sqrt (max 0 (1 - 3 * a)) := rfl
        _ ≤ Real.sqrt (s ^ 2) := Real.sqrt_le_sqrt hle2
        _ = s := by rw [Real.sqrt_sq hs0.le]
    · nlinarith [hle.2]
  rw [MeasureTheory.ae_eq_set]
  constructor
  · refine measure_mono_null (fun s hs => ?_)
      (measure_union_null (measure_singleton (sLo a)) (measure_singleton (sHi a)))
    obtain ⟨h1, h2⟩ := hs
    have h3 := hsub2 h1
    rw [Set.mem_Icc] at h3
    rw [Set.mem_union, Set.mem_singleton_iff, Set.mem_singleton_iff]
    by_contra hc
    rw [not_or] at hc
    exact h2 ⟨lt_of_le_of_ne h3.1 (Ne.symm hc.1), lt_of_le_of_ne h3.2 hc.2⟩
  · rw [Set.sdiff_eq_empty.2 hsub1, measure_empty]

theorem bandLen_div_nonneg {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) :
    0 ≤ bandLen a s / a * (2 * s / 3) := by
  have := bandLen_nonneg ha hs
  positivity

/-- **PROVED.**  The `s`-lintegral over `faceSliceS a` is the interval integral. -/
theorem lintegral_faceSliceS_eq {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    ∫⁻ s in faceSliceS a, faceIntegrand a s
      = ENNReal.ofReal (∫ s in (sLo a)..(sHi a), bandLen a s / a * (2 * s / 3)) := by
  have hcont : Continuous fun s : ℝ => bandLen a s / a * (2 * s / 3) := by
    exact ((continuous_bandLen (ne_of_gt ha)).div_const a).mul (by fun_prop)
  have hint : IntegrableOn (fun s : ℝ => bandLen a s / a * (2 * s / 3))
      (Set.Ioo (sLo a) (sHi a)) :=
    (hcont.continuousOn.integrableOn_Icc (a := sLo a) (b := sHi a)).mono_set
      Set.Ioo_subset_Icc_self
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo (sLo a) (sHi a))]
      fun s : ℝ => bandLen a s / a * (2 * s / 3) := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioo]
    refine Filter.Eventually.of_forall fun s hs => ?_
    simp only [Pi.zero_apply]
    exact bandLen_div_nonneg ha (le_trans (sLo_nonneg a) hs.1.le)
  rw [setLIntegral_congr (faceSliceS_ae ha ha1)]
  unfold faceIntegrand
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (sLo_le_sHi ha)]

/-! #### Step 5: assembly -/

theorem volume_FaceBPos_eq :
    volume FaceBPos = ∫⁻ a in Set.Ioc (0 : ℝ) 1, volume (Prod.mk a ⁻¹' FaceB) := by
  rw [show (volume : Measure (ℝ × ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
    Measure.prod_apply measurableSet_FaceBPos]
  have hfun : (fun a : ℝ => (volume : Measure (ℝ × ℝ)) (Prod.mk a ⁻¹' FaceBPos))
      = (Set.Ioc (0 : ℝ) 1).indicator
        (fun a => (volume : Measure (ℝ × ℝ)) (Prod.mk a ⁻¹' FaceB)) := by
    funext a
    by_cases ha : a ∈ Set.Ioc (0 : ℝ) 1
    · rw [Set.indicator_of_mem ha]
      congr 1
      ext ⟨c, d⟩
      simp only [Set.mem_preimage, FaceBPos, Set.mem_ofPred_eq]
      exact ⟨fun h => h.1, fun h => ⟨h, ha.1⟩⟩
    · rw [Set.indicator_of_notMem ha]
      have hempty : Prod.mk a ⁻¹' FaceBPos = ∅ := by
        ext ⟨c, d⟩
        simp only [Set.mem_preimage, FaceBPos, FaceB, Set.mem_ofPred_eq,
          Set.mem_empty_iff_false, iff_false, not_and]
        rintro ⟨⟨h1, h2⟩, -, -, -⟩ h3
        exact ha ⟨h3, h2⟩
      rw [hempty, measure_empty]
  rw [hfun, lintegral_indicator measurableSet_Ioc]

/-- **PROVED — the pre-swap identity.**

    vol₃(FaceB) = 2 · ∫_{a ∈ (0,1]} ∫_{s ∈ faceSliceS a} bandLen a s / a · (2s/3)

Assembled from the three steps above:

* `volume_FaceB_eq_two_mul_pos` — the symmetry `(a,c,d) ↦ (-a,-c,d)` (which is
  `x ↦ -x` on the roots) gives the factor `2`;
* `volume_FaceBPos_eq` — Fubini in `a`;
* `volume_sliceB` — the `(c,d)`-slice at fixed `a ∈ (0,1]` is the region between
  the clipped band edges, of width `bandLen a (sOf a c)`; this is where
  `Δ₄_face_b_pos_iff` and `L1` (via `dHi_le_one`) are used;
* `integral_c_eq_integral_s` — the substitution `c = (1-s²)/(3a)`, Jacobian
  `2s/(3a)`;
* `lintegral_faceSliceS_eq` — the resulting `s`-range is `faceSliceS a`. -/
theorem volume_FaceB_eq_pre_swap :
    volume FaceB
      = 2 * ∫⁻ a in Set.Ioc (0 : ℝ) 1, ∫⁻ s in faceSliceS a, faceIntegrand a s := by
  rw [volume_FaceB_eq_two_mul_pos, volume_FaceBPos_eq]
  congr 1
  refine setLIntegral_congr_fun measurableSet_Ioc fun a ha => ?_
  rw [volume_sliceB ha.1 ha.2, integral_c_eq_integral_s ha.1,
    ← lintegral_faceSliceS_eq ha.1 ha.2]

/-- **PROVED from `volume_FaceB_eq_pre_swap`.**  The Tonelli swap plus the
post-swap evaluation turn the pre-swap double integral into `(4/3)∫₀² s F(s) ds`.
This is `VERDICT.md`'s "the move: integrating over `a` first, at fixed `s`". -/
theorem volume_FaceB_eq_integral :
    volume FaceB = ENNReal.ofReal (4 / 3 * ∫ s in (0 : ℝ)..2, s * Fs s) := by
  rw [volume_FaceB_eq_pre_swap, lintegral_faceRegion_swap measurable_faceIntegrand,
    post_swap_eval,
    show (4 : ℝ) / 3 * (∫ s in (0 : ℝ)..2, s * Fs s)
        = 2 * (2 / 3 * ∫ s in (0 : ℝ)..2, s * Fs s) from by ring,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- **PROVED from `volume_FaceB_eq_integral`.**  `S_b = 1454/405 − (5/6) log 3`.

The closed-form evaluation — which is the mathematical content of `S_b`, and
where the `log 3` in Theorem 3 actually comes from — is `integral_s_Fs`, proved
above. -/
theorem volume_FaceB :
    volume FaceB = ENNReal.ofReal (1454 / 405 - 5 / 6 * Real.log 3) := by
  rw [volume_FaceB_eq_integral, integral_s_Fs]
  congr 1
  ring

/-! ## Assembly -/

theorem log_three_le_two : Real.log 3 ≤ 2 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
  linarith

/-- **PROVED.**  The face decomposition plus the two face volumes give
Theorem 3.  This is the arithmetic
`(766/1215 + log 3/6) + (1454/405 − (5/6) log 3) = 16 (641/2430 − log 3/24)`. -/
theorem theorem3_of_faces
    (hface : volume T3Set = volume FaceA + volume FaceB)
    (hB : volume FaceB = ENNReal.ofReal (1454 / 405 - 5 / 6 * Real.log 3)) :
    volume T3Set = ENNReal.ofReal ((641 / 2430 - Real.log 3 / 24) * 16) := by
  have hlog := log_three_le_two
  have hlog0 : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hA : (0 : ℝ) ≤ 766 / 1215 + Real.log 3 / 6 := by linarith
  have hBnn : (0 : ℝ) ≤ 1454 / 405 - 5 / 6 * Real.log 3 := by linarith
  rw [hface, volume_FaceA, hB, ← ENNReal.ofReal_add hA hBnn]
  congr 1
  ring

/-- **THEOREM 3, fully proved.**  Let `(a,b,c,d)` be i.i.d. uniform on `[-1,1]`.
The set of `(a,b,c,d) ∈ [-1,1]⁴` for which `a x³ + b x² + c x + d` has three
distinct real roots (equivalently `Δ₄ > 0`, `DiscriminantRootCount.lean`) has
Lebesgue measure `16 · (641/2430 − log 3 / 24)`.

This is `reference/VERDICT.md`'s value, now machine-checked. -/
theorem theorem3 : volume T3Set = ENNReal.ofReal ((641 / 2430 - Real.log 3 / 24) * 16) :=
  theorem3_of_faces volume_T3Set_eq_faces volume_FaceB

/-- **THEOREM 3, probability form, fully proved.**
`P( a x³ + b x² + c x + d has three real roots ) = 641/2430 − log 3 / 24`. -/
theorem theorem3_probability :
    (volume T3Set).toReal
      / (volume (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1
          ×ˢ Icc (-1 : ℝ) 1)).toReal
      = 641 / 2430 - Real.log 3 / 24 := by
  have hlog : Real.log 3 ≤ 2 := log_three_le_two
  have hnn : (0 : ℝ) ≤ (641 / 2430 - Real.log 3 / 24) * 16 := by linarith
  rw [theorem3, volume_cube4, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 16),
    ENNReal.toReal_ofReal hnn]
  ring

/-! ## Theorem 3 in root-count form

`theorem3` is a statement about the *sign of `Δ₄`*.  The English statement talks
about *roots*.  `DiscriminantRootCount.lean` bridges the two for `a ≠ 0`, and the
hyperplane `{a = 0}` is Lebesgue-null in `ℝ⁴`, so the two sets have equal measure.
This is the analogue of `theorem1_root_count` / `theorem2_root_count`. -/

theorem volume_fst_eq_zero_four :
    (volume : Measure (ℝ × ℝ × ℝ × ℝ)) {p : ℝ × ℝ × ℝ × ℝ | p.1 = 0} = 0 := by
  have h : {p : ℝ × ℝ × ℝ × ℝ | p.1 = 0}
      = ({0} : Set ℝ) ×ˢ (Set.univ : Set (ℝ × ℝ × ℝ)) := by
    ext p; simp
  rw [h, show (volume : Measure (ℝ × ℝ × ℝ × ℝ))
      = (volume : Measure ℝ).prod volume from rfl, Measure.prod_prod]
  simp

/-- **THEOREM 3, root-count form, fully proved.**  The set of `(a,b,c,d) ∈ [-1,1]⁴`
for which `a x³ + b x² + c x + d` genuinely *has three distinct real roots* has
measure `16 · (641/2430 − log 3 / 24)`; dividing by `vol([-1,1]⁴) = 16` gives the
probability `641/2430 − log 3 / 24`.

No `Δ₄` appears in the statement: this is `reference/VERDICT.md`'s Theorem 3 as
originally worded, machine-checked end to end. -/
theorem theorem3_root_count :
    volume {p : ℝ × ℝ × ℝ × ℝ | p.1 ∈ Icc (-1 : ℝ) 1 ∧ p.2.1 ∈ Icc (-1 : ℝ) 1 ∧
      p.2.2.1 ∈ Icc (-1 : ℝ) 1 ∧ p.2.2.2 ∈ Icc (-1 : ℝ) 1 ∧
      HasThreeDistinctRealRoots p.1 p.2.1 p.2.2.1 p.2.2.2}
      = ENNReal.ofReal ((641 / 2430 - Real.log 3 / 24) * 16) := by
  rw [← theorem3]
  refine measure_congr ?_
  rw [MeasureTheory.ae_eq_set]
  constructor
  · refine measure_mono_null (fun p hp => ?_) volume_fst_eq_zero_four
    obtain ⟨⟨h1, h2, h3, h4, hroots⟩, hout⟩ := hp
    rw [Set.mem_ofPred_eq]
    by_contra hne
    exact hout ⟨h1, h2, h3, h4,
      (Δ₄_pos_iff_three_distinct_real_roots hne).2 hroots⟩
  · refine measure_mono_null (fun p hp => ?_) volume_fst_eq_zero_four
    obtain ⟨⟨h1, h2, h3, h4, hΔ⟩, hout⟩ := hp
    rw [Set.mem_ofPred_eq]
    by_contra hne
    exact hout ⟨h1, h2, h3, h4,
      (Δ₄_pos_iff_three_distinct_real_roots hne).1 hΔ⟩

end NonmonicCubic
