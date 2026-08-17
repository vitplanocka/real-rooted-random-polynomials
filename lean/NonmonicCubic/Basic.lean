/-
Core algebra for the cubic discriminant.

Everything downstream (Theorems 1, 2, 3) rests on the single polynomial identity
`disc_completeSquare` below, which is provable by `ring`:

  -27 * Δ₃ a b c = (27c - 9ab + 2a³)² - 4(a² - 3b)³

Writing `t = (a² - 3b)^{3/2}` (so `t² = (a² - 3b)³` when `a² - 3b ≥ 0`) this
factors the discriminant, as a quadratic in `c`, into `-27 (c - cLo)(c - cHi)`.
That is identity **S2** of `reference/THEOREMS.md`, and it simultaneously gives:

* `b > a²/3` (i.e. `a² - 3b < 0`)  ⟹  `Δ₃ < 0` (one real root);
* `b ≤ a²/3`                        ⟹  `Δ₃ > 0 ↔ cLo < c < cHi` (the *band*).

The band endpoints admit the closed forms `27 cHi = (a-s)²(a+2s)` and
`27 cLo = (a+s)²(a-2s)` with `s = √(a²-3b)`, which is what makes the
never-clipped lemma of Theorem 1 a two-line `nlinarith`.
-/
import Mathlib

namespace NonmonicCubic

open Real Set

/-! ## Discriminants -/

/-- Discriminant of the **monic** cubic `x³ + a x² + b x + c`.
Matches `sp.discriminant(x^3+a*x^2+b*x+c, x)` in `reference/exact_anchors.py`. -/
def Δ₃ (a b c : ℝ) : ℝ :=
  18 * a * b * c - 4 * a ^ 3 * c + a ^ 2 * b ^ 2 - 4 * b ^ 3 - 27 * c ^ 2

/-- Discriminant of the **general** cubic `a x³ + b x² + c x + d`.
This is the `Δ` of `reference/VERDICT.md`:
`Δ = 18abcd − 4b³d + b²c² − 4ac³ − 27a²d²`. -/
def Δ₄ (a b c d : ℝ) : ℝ :=
  18 * a * b * c * d - 4 * b ^ 3 * d + b ^ 2 * c ^ 2 - 4 * a * c ^ 3 - 27 * a ^ 2 * d ^ 2

/-- The general discriminant specialises to the monic one. -/
theorem Δ₄_one (b c d : ℝ) : Δ₄ 1 b c d = Δ₃ b c d := by
  unfold Δ₄ Δ₃; ring

/-- `Δ₄` is homogeneous of degree 4: this is what makes `{Δ₄ > 0}` a cone. -/
theorem Δ₄_smul (l a b c d : ℝ) :
    Δ₄ (l * a) (l * b) (l * c) (l * d) = l ^ 4 * Δ₄ a b c d := by
  unfold Δ₄; ring

/-- Coefficient reversal `(a,b,c,d) ↦ (d,c,b,a)` (i.e. `x ↦ 1/x` on the roots)
preserves the discriminant. -/
theorem Δ₄_reverse (a b c d : ℝ) : Δ₄ d c b a = Δ₄ a b c d := by
  unfold Δ₄; ring

/-- Central symmetry preserves the discriminant. -/
theorem Δ₄_neg (a b c d : ℝ) : Δ₄ (-a) (-b) (-c) (-d) = Δ₄ a b c d := by
  unfold Δ₄; ring

/-- `(a,b,c) ↦ (-a,b,-c)` preserves `Δ₃` (used for the `cLo`/`cHi` symmetry). -/
theorem Δ₃_neg (a b c : ℝ) : Δ₃ (-a) b (-c) = Δ₃ a b c := by
  unfold Δ₃; ring

/-! ## The completed square -/

/-- **The key identity.** Pure `ring`; everything else follows from it. -/
theorem disc_completeSquare (a b c : ℝ) :
    -27 * Δ₃ a b c = (27 * c - 9 * a * b + 2 * a ^ 3) ^ 2 - 4 * (a ^ 2 - 3 * b) ^ 3 := by
  unfold Δ₃; ring

/-- `x ↦ x^{3/2}`, extended by `0` below `0` (so it is the honest `x * √x`). -/
noncomputable def p32 (x : ℝ) : ℝ := x * Real.sqrt x

theorem p32_sq {x : ℝ} (hx : 0 ≤ x) : p32 x ^ 2 = x ^ 3 := by
  unfold p32; rw [mul_pow, Real.sq_sqrt hx]; ring

theorem p32_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ p32 x := mul_nonneg hx (Real.sqrt_nonneg x)

theorem p32_eq_sq_mul (s : ℝ) (hs : 0 ≤ s) : p32 (s ^ 2) = s ^ 3 := by
  unfold p32; rw [Real.sqrt_sq hs]; ring

/-! ## The band `[cLo, cHi]` -/

/-- Lower edge of the admissible `c`-band: `-g(x₋)` where `x₋` is the local max
of `g(x) = x³ + a x² + b x`.  Equals `(a+s)²(a-2s)/27` with `s = √(a²-3b)`. -/
noncomputable def cLo (a b : ℝ) : ℝ := (9 * a * b - 2 * a ^ 3 - 2 * p32 (a ^ 2 - 3 * b)) / 27

/-- Upper edge of the admissible `c`-band: `-g(x₊)` where `x₊` is the local min.
Equals `(a-s)²(a+2s)/27` with `s = √(a²-3b)`. -/
noncomputable def cHi (a b : ℝ) : ℝ := (9 * a * b - 2 * a ^ 3 + 2 * p32 (a ^ 2 - 3 * b)) / 27

theorem cLo_le_cHi (a b : ℝ) (h : 0 ≤ a ^ 2 - 3 * b) : cLo a b ≤ cHi a b := by
  have := p32_nonneg h
  unfold cLo cHi; linarith

/-- **Identity S1**: the band has width `(4/27) (a²-3b)^{3/2}`. -/
theorem cHi_sub_cLo (a b : ℝ) : cHi a b - cLo a b = 4 / 27 * p32 (a ^ 2 - 3 * b) := by
  unfold cLo cHi; ring

/-- **Identity S2**: the discriminant factors over the band. -/
theorem Δ₃_factor {a b : ℝ} (h : 0 ≤ a ^ 2 - 3 * b) (c : ℝ) :
    Δ₃ a b c = -27 * (c - cLo a b) * (c - cHi a b) := by
  have ht : p32 (a ^ 2 - 3 * b) ^ 2 = (a ^ 2 - 3 * b) ^ 3 := p32_sq h
  unfold Δ₃ cLo cHi
  linear_combination (-(4 : ℝ) / 27) * ht

/-- Below the parabola `b = a²/3` the discriminant is positive exactly on the band. -/
theorem Δ₃_pos_iff {a b : ℝ} (h : 0 ≤ a ^ 2 - 3 * b) (c : ℝ) :
    0 < Δ₃ a b c ↔ c ∈ Ioo (cLo a b) (cHi a b) := by
  have hle := cLo_le_cHi a b h
  rw [Δ₃_factor h, mem_Ioo]
  constructor
  · intro hpos
    constructor
    · by_contra hc
      rw [not_lt] at hc
      nlinarith
    · by_contra hc
      rw [not_lt] at hc
      nlinarith
  · rintro ⟨h1, h2⟩
    nlinarith

/-- Above the parabola `b = a²/3` the cubic has exactly one real root. -/
theorem Δ₃_neg_of_lt {a b : ℝ} (h : a ^ 2 - 3 * b < 0) (c : ℝ) : Δ₃ a b c < 0 := by
  have key := disc_completeSquare a b c
  have hsq : 0 ≤ (27 * c - 9 * a * b + 2 * a ^ 3) ^ 2 := sq_nonneg _
  have hcube : (a ^ 2 - 3 * b) ^ 3 < 0 := (Odd.pow_neg_iff (by decide)).2 h
  linarith

/-! ## Closed forms for the band edges, and the never-clipped lemma -/

theorem cHi_eq {a b s : ℝ} (hs : 0 ≤ s) (hsq : s ^ 2 = a ^ 2 - 3 * b) :
    cHi a b = (a - s) ^ 2 * (a + 2 * s) / 27 := by
  unfold cHi
  rw [← hsq, p32_eq_sq_mul s hs]
  have : b = (a ^ 2 - s ^ 2) / 3 := by linarith
  subst this; ring

theorem cLo_eq {a b s : ℝ} (hs : 0 ≤ s) (hsq : s ^ 2 = a ^ 2 - 3 * b) :
    cLo a b = (a + s) ^ 2 * (a - 2 * s) / 27 := by
  unfold cLo
  rw [← hsq, p32_eq_sq_mul s hs]
  have : b = (a ^ 2 - s ^ 2) / 3 := by linarith
  subst this; ring

/-- The scalar heart of the **never-clipped lemma**: `(a-s)²(a+2s) ≤ 27` on
`a ∈ [-1,1]`, `s ∈ [0,2]`, with equality exactly at `(a,s) = (-1,2)`. -/
theorem band_top_bound {a s : ℝ}
    (ha1 : -1 ≤ a) (ha2 : a ≤ 1) (hs0 : 0 ≤ s) (hs2 : s ≤ 2) :
    (a - s) ^ 2 * (a + 2 * s) ≤ 27 := by
  nlinarith [sq_nonneg (a - s), sq_nonneg (a + s), sq_nonneg (s - 2), sq_nonneg (a + 1),
    mul_nonneg (sub_nonneg.2 hs2) (sub_nonneg.2 ha2),
    mul_nonneg (sub_nonneg.2 hs2) (by linarith : (0 : ℝ) ≤ a + 1),
    mul_nonneg hs0 (by linarith : (0 : ℝ) ≤ a + 1),
    mul_nonneg hs0 (sub_nonneg.2 ha2)]

/-- **Never-clipped lemma, upper half.**  On `D = {a ∈ [-1,1], -1 ≤ b ≤ a²/3}`
the top of the band never leaves the window: `cHi ≤ 1`, with equality only at
`(a,b) = (-1,-1)`. -/
theorem cHi_le_one {a b : ℝ}
    (ha1 : -1 ≤ a) (ha2 : a ≤ 1) (hb : -1 ≤ b) (hb' : 3 * b ≤ a ^ 2) :
    cHi a b ≤ 1 := by
  set s := Real.sqrt (a ^ 2 - 3 * b) with hs_def
  have hnn : 0 ≤ a ^ 2 - 3 * b := by linarith
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsq : s ^ 2 = a ^ 2 - 3 * b := Real.sq_sqrt hnn
  have hs2 : s ≤ 2 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (a + 1)]
  rw [cHi_eq hs0 hsq]
  have := band_top_bound ha1 ha2 hs0 hs2
  linarith

/-- **Never-clipped lemma, lower half**, by the symmetry `(a,b,c) ↦ (-a,b,-c)`. -/
theorem neg_one_le_cLo {a b : ℝ}
    (ha1 : -1 ≤ a) (ha2 : a ≤ 1) (hb : -1 ≤ b) (hb' : 3 * b ≤ a ^ 2) :
    -1 ≤ cLo a b := by
  set s := Real.sqrt (a ^ 2 - 3 * b) with hs_def
  have hnn : 0 ≤ a ^ 2 - 3 * b := by linarith
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsq : s ^ 2 = a ^ 2 - 3 * b := Real.sq_sqrt hnn
  have hs2 : s ≤ 2 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (a + 1)]
  rw [cLo_eq hs0 hsq]
  have := band_top_bound (a := -a) (s := s) (by linarith) (by linarith) hs0 hs2
  nlinarith

/-! ## Sign of the band edges on the unit cube (Theorem 2) -/

/-- Below the curve `b = a²/4` the bottom of the band is at or below `0`,
so on the unit cube the window's floor `c = 0` clips it. -/
theorem cLo_nonpos {a b : ℝ} (hb : 0 ≤ b) (h4 : 4 * b ≤ a ^ 2) : cLo a b ≤ 0 := by
  have hnn : 0 ≤ a ^ 2 - 3 * b := by linarith
  have hs0 : 0 ≤ Real.sqrt (a ^ 2 - 3 * b) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (a ^ 2 - 3 * b) ^ 2 = a ^ 2 - 3 * b := Real.sq_sqrt hnn
  set s := Real.sqrt (a ^ 2 - 3 * b) with hs_def
  rw [cLo_eq hs0 hsq]
  have h2s : a ≤ 2 * s := by nlinarith [sq_nonneg (a - 2 * s), sq_nonneg (a + 2 * s)]
  nlinarith [sq_nonneg (a + s)]

/-- Above the curve `b = a²/4` the bottom of the band is at or above `0`,
so the window's floor does not clip. -/
theorem cLo_nonneg {a b : ℝ} (ha : 0 ≤ a) (h4 : a ^ 2 ≤ 4 * b) (h3 : 3 * b ≤ a ^ 2) :
    0 ≤ cLo a b := by
  have hnn : 0 ≤ a ^ 2 - 3 * b := by linarith
  have hs0 : 0 ≤ Real.sqrt (a ^ 2 - 3 * b) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (a ^ 2 - 3 * b) ^ 2 = a ^ 2 - 3 * b := Real.sq_sqrt hnn
  set s := Real.sqrt (a ^ 2 - 3 * b) with hs_def
  rw [cLo_eq hs0 hsq]
  have h2s : 2 * s ≤ a := by nlinarith [sq_nonneg (a - 2 * s), sq_nonneg (a + 2 * s)]
  nlinarith [sq_nonneg (a + s)]

/-- On the unit cube the top of the band is nonnegative. -/
theorem cHi_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h3 : 3 * b ≤ a ^ 2) :
    0 ≤ cHi a b := by
  have hnn : 0 ≤ a ^ 2 - 3 * b := by linarith
  have hs0 : 0 ≤ Real.sqrt (a ^ 2 - 3 * b) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (a ^ 2 - 3 * b) ^ 2 = a ^ 2 - 3 * b := Real.sq_sqrt hnn
  set s := Real.sqrt (a ^ 2 - 3 * b) with hs_def
  rw [cHi_eq hs0 hsq]
  have hsa : s ≤ a := by nlinarith [sq_nonneg (a - s), sq_nonneg (a + s)]
  nlinarith [sq_nonneg (a - s)]

/-- **Never-clipped-above, unit-cube version.**  On `a ∈ [0,1]`, `0 ≤ b ≤ a²/3`
the top of the band satisfies `cHi ≤ 1/9 < 1`, so the window's ceiling `c = 1`
never clips. -/
theorem cHi_le_one_unit {a b : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b)
    (h3 : 3 * b ≤ a ^ 2) : cHi a b ≤ 1 := by
  have hnn : 0 ≤ a ^ 2 - 3 * b := by linarith
  have hs0 : 0 ≤ Real.sqrt (a ^ 2 - 3 * b) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (a ^ 2 - 3 * b) ^ 2 = a ^ 2 - 3 * b := Real.sq_sqrt hnn
  set s := Real.sqrt (a ^ 2 - 3 * b) with hs_def
  rw [cHi_eq hs0 hsq]
  have hsa : s ≤ a := by nlinarith [sq_nonneg (a - s), sq_nonneg (a + s)]
  nlinarith [sq_nonneg (a - s), sq_nonneg s]

end NonmonicCubic
