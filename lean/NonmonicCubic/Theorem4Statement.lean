/-
# Theorem 4 — the statement

> **Theorem 4.** Let `(a,b,c,d)` be i.i.d. uniform on `[0,1]`.  Then
> `P( a x³ + b x² + c x + d has three real roots ) = 719/2880 − ln(2)/3`
> `= 0.018603717591129341305367070625…`

This is the missing corner of the 2×2 table completed by this development:

|                | uniform `[−1,1]`      | uniform `[0,1]`      |
|----------------|-----------------------|----------------------|
| monic          | `383/4860 + ln3/48`   | `1/2880`             |
| non-monic      | `641/2430 − ln3/24`   | **`719/2880 − ln2/3`** |

## Word-by-word transcription check

* `(a,b,c,d)` i.i.d. uniform on `[0,1]` ↦ Lebesgue measure on `Icc 0 1` in each of
  the four coordinates of `ℝ × ℝ × ℝ × ℝ`, in the order `(a,b,c,d)`.
* `a x³ + b x² + c x + d` ↦ leading coefficient is the **first** coordinate `a`;
  the constant term is the **last**, `d`.  (Not reversed.)
* "has three real roots" ↦ `0 < Δ₄ a b c d`; `Δ₄` is `Basic.lean`'s
  `18abcd − 4b³d + b²c² − 4ac³ − 27a²d²`, proved equal to Mathlib's
  `Cubic.discr` in `Δ₄_eq_cubic_discr` (`Theorem3Statement.lean`).
  `Theorem4Proof.theorem4_root_count` restates the result with no `Δ₄` in sight.
* The unit 4-cube has volume `1`, so the volume and the probability coincide —
  no normalising factor, unlike Theorem 3's `16`.
-/
import NonmonicCubic.Theorem3Proof

namespace NonmonicCubic

open Real Set MeasureTheory

/-- The real-rooted region of the unit 4-cube `[0,1]⁴`, coordinates `(a,b,c,d)`
for the cubic `a x³ + b x² + c x + d`. -/
def T4Set : Set (ℝ × ℝ × ℝ × ℝ) :=
  {p | p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2.1 ∈ Icc (0 : ℝ) 1 ∧ p.2.2.1 ∈ Icc (0 : ℝ) 1 ∧
    p.2.2.2 ∈ Icc (0 : ℝ) 1 ∧ 0 < Δ₄ p.1 p.2.1 p.2.2.1 p.2.2.2}

theorem measurableSet_T4Set : MeasurableSet T4Set := by
  have h : T4Set = ((((Prod.fst ⁻¹' Icc (0 : ℝ) 1)
      ∩ ((fun p : ℝ × ℝ × ℝ × ℝ => p.2.1) ⁻¹' Icc (0 : ℝ) 1))
      ∩ ((fun p : ℝ × ℝ × ℝ × ℝ => p.2.2.1) ⁻¹' Icc (0 : ℝ) 1))
      ∩ ((fun p : ℝ × ℝ × ℝ × ℝ => p.2.2.2) ⁻¹' Icc (0 : ℝ) 1))
      ∩ {p : ℝ × ℝ × ℝ × ℝ | 0 < Δ₄ p.1 p.2.1 p.2.2.1 p.2.2.2} := by
    ext p; simp only [T4Set, mem_ofPred_eq, mem_inter_iff, mem_preimage]; tauto
  rw [h]
  exact ((((measurable_fst measurableSet_Icc).inter
      ((measurable_fst.comp measurable_snd) measurableSet_Icc)).inter
      ((measurable_fst.comp (measurable_snd.comp measurable_snd)) measurableSet_Icc)).inter
      ((measurable_snd.comp (measurable_snd.comp measurable_snd)) measurableSet_Icc)).inter
    (measurableSet_lt measurable_const continuous_Δ₄.measurable)

/-- The volume of the unit 4-cube `[0,1]⁴` is `1`. -/
theorem volume_cube4_unit :
    volume (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) = 1 := by
  rw [show (volume : Measure (ℝ × ℝ × ℝ × ℝ))
      = (volume : Measure ℝ).prod volume from rfl,
    Measure.prod_prod,
    show (volume : Measure (ℝ × ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
    Measure.prod_prod,
    show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
    Measure.prod_prod, Real.volume_Icc]
  norm_num

end NonmonicCubic
