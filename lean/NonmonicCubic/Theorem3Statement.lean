/-
# Theorem 3 — the statement

> **Theorem 3.** Let `(a,b,c,d)` be i.i.d. uniform on `[−1,1]`.  Then
> `P( a x³ + b x² + c x + d has three real roots ) = 641/2430 − ln(3)/24`
> `= 0.21801049620261477108898412335868…`

(`reference/VERDICT.md`, "Suggested amendment to THEOREMS.md"; identical wording
in `reference/THEOREMS.md`, "Statements".)

## Word-by-word transcription check

| informal | formal |
|---|---|
| `(a,b,c,d)` i.i.d. uniform on `[−1,1]` | Lebesgue measure on `Icc (-1) 1` in each of the four coordinates of `ℝ × ℝ × ℝ × ℝ`, in the order `(a,b,c,d)` |
| `a x³ + b x² + c x + d` | leading coefficient is the **first** coordinate `a`; constant term is the **last**, `d` |
| "has three real roots" | `0 < Δ₄ a b c d` — see the caveat below |
| `Δ = 18abcd − 4b³d + b²c² − 4ac³ − 27a²d²` (`VERDICT.md`, line 69) | `Δ₄` in `Basic.lean`, character for character |
| `P = 641/2430 − ln(3)/24` | `ENNReal.ofReal ((641/2430 - Real.log 3 / 24) * 16)`, the `16` being `vol([−1,1]⁴)` |

Two independent confirmations that `Δ₄` is the right polynomial:

* `Δ₄_eq_cubic_discr` below proves, by `ring`, that `Δ₄ a b c d` is **literally
  Mathlib's own** `Cubic.discr ⟨a, b, c, d⟩` (`Mathlib/Algebra/CubicDiscriminant.lean`).
  So the transcription is checked against Mathlib, not only against the reference.
* `Δ₄_one` (`Basic.lean`) proves `Δ₄ 1 b c d = Δ₃ b c d`, and `Δ₃` is the monic
  discriminant already used in the fully-proved Theorems 1 and 2.

## Caveat on "three real roots" (this is Stage 5, `DiscriminantRootCount.lean`)

`0 < Δ₄ a b c d` is the classical criterion for *three distinct real roots* when
`a ≠ 0`.  The equivalence itself is **not** proved here and is **not** in Mathlib
(Mathlib has `Cubic.discr` and `Cubic.discr_ne_zero_iff_roots_nodup`, but nothing
linking the *sign* of the discriminant to the *number of real* roots).  It is
stated as its own theorem, with `sorry`, in `DiscriminantRootCount.lean`.  Note:

* the set where `Δ₄ = 0` (repeated roots) and the set where `a = 0` (not a cubic)
  are both Lebesgue-null, so they cannot change the value of the probability;
* but "three real roots" counted *with multiplicity* would include `Δ₄ = 0`,
  whereas `0 < Δ₄` means three *distinct* real roots.  Again a null-set
  difference, and the reference's Monte-Carlo check used `sign(Δ)` too
  (`VERDICT.md`, "4×10^10 samples, raw `sign(Δ)`").
-/
import NonmonicCubic.Theorem2

namespace NonmonicCubic

open Real Set MeasureTheory

/-- The real-rooted region of the 4-cube `[-1,1]⁴`, coordinates `(a,b,c,d)` for
the cubic `a x³ + b x² + c x + d`. -/
def T3Set : Set (ℝ × ℝ × ℝ × ℝ) :=
  {p | p.1 ∈ Icc (-1 : ℝ) 1 ∧ p.2.1 ∈ Icc (-1 : ℝ) 1 ∧ p.2.2.1 ∈ Icc (-1 : ℝ) 1 ∧
    p.2.2.2 ∈ Icc (-1 : ℝ) 1 ∧ 0 < Δ₄ p.1 p.2.1 p.2.2.1 p.2.2.2}

/-- **Our `Δ₄` is Mathlib's `Cubic.discr`.**  Proved by `ring`; this is the
strongest available check that the Theorem 3 statement transcribes the right
polynomial. -/
theorem Δ₄_eq_cubic_discr (a b c d : ℝ) :
    Δ₄ a b c d = (Cubic.mk a b c d).discr := by
  unfold Δ₄ Cubic.discr
  ring

theorem continuous_Δ₄ :
    Continuous fun p : ℝ × ℝ × ℝ × ℝ => Δ₄ p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  unfold Δ₄; fun_prop

theorem measurableSet_T3Set : MeasurableSet T3Set := by
  have h : T3Set = ((((Prod.fst ⁻¹' Icc (-1 : ℝ) 1)
      ∩ ((fun p : ℝ × ℝ × ℝ × ℝ => p.2.1) ⁻¹' Icc (-1 : ℝ) 1))
      ∩ ((fun p : ℝ × ℝ × ℝ × ℝ => p.2.2.1) ⁻¹' Icc (-1 : ℝ) 1))
      ∩ ((fun p : ℝ × ℝ × ℝ × ℝ => p.2.2.2) ⁻¹' Icc (-1 : ℝ) 1))
      ∩ {p : ℝ × ℝ × ℝ × ℝ | 0 < Δ₄ p.1 p.2.1 p.2.2.1 p.2.2.2} := by
    ext p; simp only [T3Set, mem_ofPred_eq, mem_inter_iff, mem_preimage]; tauto
  rw [h]
  exact ((((measurable_fst measurableSet_Icc).inter
      ((measurable_fst.comp measurable_snd) measurableSet_Icc)).inter
      ((measurable_fst.comp (measurable_snd.comp measurable_snd)) measurableSet_Icc)).inter
      ((measurable_snd.comp (measurable_snd.comp measurable_snd)) measurableSet_Icc)).inter
    (measurableSet_lt measurable_const continuous_Δ₄.measurable)

/-- The volume of the 4-cube `[-1,1]⁴` is `16`. -/
theorem volume_cube4 :
    volume (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
      = ENNReal.ofReal 16 := by
  rw [show (volume : Measure (ℝ × ℝ × ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
    Measure.prod_prod,
    show (volume : Measure (ℝ × ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
    Measure.prod_prod,
    show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
    Measure.prod_prod, Real.volume_Icc]
  norm_num

/-- **THEOREM 3 (volume form).**  The set of `(a,b,c,d) ∈ [-1,1]⁴` for which the
cubic `a x³ + b x² + c x + d` has three distinct real roots (equivalently
`Δ₄ > 0`) has Lebesgue measure `16 · (641/2430 − log 3 / 24)`.

**UNPROVED — the proof below is `sorry`.**  What is missing is exactly Stage 4:
the cone/face decomposition reducing this to `V(1) + S_b`, and the closed-form
evaluation of `S_b`.  See `Theorem3Proof.lean` for the decomposition into
sub-lemmas and for which of them *are* proved. -/
theorem theorem3 :
    volume T3Set = ENNReal.ofReal ((641 / 2430 - Real.log 3 / 24) * 16) := by
  sorry

/-- **THEOREM 3 (probability form).**  `P = 641/2430 − log 3 / 24`.

**UNPROVED**: this is a two-line consequence of `theorem3` (which is `sorry`d)
and `volume_cube4` (which is proved). -/
theorem theorem3_probability :
    (volume T3Set).toReal
      / (volume (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)).toReal
      = 641 / 2430 - Real.log 3 / 24 := by
  have hlog : Real.log 3 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    nlinarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)]
  have hnn : (0 : ℝ) ≤ (641 / 2430 - Real.log 3 / 24) * 16 := by nlinarith
  rw [theorem3, volume_cube4, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 16),
    ENNReal.toReal_ofReal hnn]
  ring

end NonmonicCubic
