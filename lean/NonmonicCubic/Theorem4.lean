/-
# Theorem 4 — the missing corner of the 2×2 table

> **Theorem 4.**  Let `(a,b,c,d)` be i.i.d. uniform on `[0,1]`.  Then
> `P( a x³ + b x² + c x + d has three real roots ) = 719/2880 − log 2 / 3`
> `= 0.01860371759112934130536707062510…`

|                | uniform `[−1,1]`      | uniform `[0,1]`        |
|----------------|-----------------------|------------------------|
| monic          | `383/4860 + ln3/48`   | `1/2880`               |
| non-monic      | `641/2430 − ln3/24`   | **`719/2880 − ln2/3`** |

The constant is `log 2`, not `log 3`: the `log 3` contributions of the two
branches of the face integral cancel (`integral_A1u` + `integral_A2u`).

Ingredients:
* `Theorem4Proof.volume_T4Set_eq` — the four-piece cone decomposition of the unit
  4-cube, with the `a = 1` and `d = 1` faces identified as Theorem 2's `T2Set`:
  `vol₄(T4Set) = 1/5760 + (1/2)·vol₃(FaceB0)`;
* `Face4B.volume_FaceB0` — the new face computation, `479/960 − (2/3) log 2`.
-/
import NonmonicCubic.Face4B

namespace NonmonicCubic

open Real Set MeasureTheory

theorem log_two_lt_seven_tenths : Real.log 2 < 7 / 10 :=
  lt_trans Real.log_two_lt_d9 (by norm_num)

theorem FaceB0_value_nonneg : (0 : ℝ) ≤ 479 / 960 - 2 / 3 * Real.log 2 := by
  have := log_two_lt_seven_tenths; linarith

theorem theorem4_value_nonneg : (0 : ℝ) ≤ 719 / 2880 - Real.log 2 / 3 := by
  have := log_two_lt_seven_tenths; linarith

/-- **THEOREM 4, fully proved.**  The set of `(a,b,c,d) ∈ [0,1]⁴` for which
`a x³ + b x² + c x + d` has three distinct real roots (equivalently `Δ₄ > 0`) has
Lebesgue measure `719/2880 − log 2 / 3`.  Since `vol([0,1]⁴) = 1` this *is* the
probability. -/
theorem theorem4 : volume T4Set = ENNReal.ofReal (719 / 2880 - Real.log 2 / 3) := by
  rw [volume_T4Set_eq, volume_FaceB0,
    ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1 / 2),
    ← ENNReal.ofReal_add (by norm_num : (0:ℝ) ≤ 1 / 5760)
      (by have := FaceB0_value_nonneg; linarith)]
  congr 1
  ring

/-- **THEOREM 4, probability form, fully proved.** -/
theorem theorem4_probability :
    (volume T4Set).toReal
      / (volume (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)).toReal
      = 719 / 2880 - Real.log 2 / 3 := by
  rw [theorem4, volume_cube4_unit, ENNReal.toReal_ofReal theorem4_value_nonneg]
  norm_num

/-- **THEOREM 4, root-count form, fully proved.**  No `Δ₄` in the statement: the
set of `(a,b,c,d) ∈ [0,1]⁴` for which the cubic genuinely *has three distinct real
roots* has measure `719/2880 − log 2 / 3`.  The bridge is
`DiscriminantRootCount.Δ₄_pos_iff_three_distinct_real_roots` together with the
fact that `{a = 0}` is Lebesgue-null in `ℝ⁴`. -/
theorem theorem4_root_count :
    volume {p : ℝ × ℝ × ℝ × ℝ | p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2.1 ∈ Icc (0 : ℝ) 1 ∧
      p.2.2.1 ∈ Icc (0 : ℝ) 1 ∧ p.2.2.2 ∈ Icc (0 : ℝ) 1 ∧
      HasThreeDistinctRealRoots p.1 p.2.1 p.2.2.1 p.2.2.2}
      = ENNReal.ofReal (719 / 2880 - Real.log 2 / 3) := by
  rw [← theorem4]
  refine measure_congr ?_
  rw [MeasureTheory.ae_eq_set]
  constructor
  · refine measure_mono_null (fun p hp => ?_) volume_fst_eq_zero_four
    obtain ⟨⟨h1, h2, h3, h4, hroots⟩, hout⟩ := hp
    rw [Set.mem_ofPred_eq]
    by_contra hne
    exact hout ⟨h1, h2, h3, h4, (Δ₄_pos_iff_three_distinct_real_roots hne).2 hroots⟩
  · refine measure_mono_null (fun p hp => ?_) volume_fst_eq_zero_four
    obtain ⟨⟨h1, h2, h3, h4, hΔ⟩, hout⟩ := hp
    rw [Set.mem_ofPred_eq]
    by_contra hne
    exact hout ⟨h1, h2, h3, h4, (Δ₄_pos_iff_three_distinct_real_roots hne).1 hΔ⟩

end NonmonicCubic
