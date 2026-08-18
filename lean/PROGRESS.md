# PROGRESS — Lean 4 / Mathlib formalization of the non-monic cubic theorem

Timestamps via `date '+%F %T'` (local).

---

## 2026-08-17 21:45:47 — Stage 0: environment sanity — DONE

- `lake build` on the bare template: **success**, 0.54s wall clock (4 jobs).
- `lakefile.toml` already requires `mathlib` at `rev = "v4.33.0"`;
  `lean-toolchain` = `leanprover/lean4:v4.33.0`. `lake update` had already been
  run by the operator (`lake-manifest.json` present, 9 packages under
  `.lake/packages/`).
- Mathlib `.olean` cache already populated: **8322** `.olean` files under
  `.lake/packages/mathlib/.lake/build/`. So `lake exe cache get` was already
  done; no re-download needed.
- `import Mathlib` compile check (`lake env lean` on a scratch file with
  `import Mathlib` + `#eval 1+1` → prints `2`): **success, 2.65s wall clock**.

**Wall-clock for Stage 0 this session: ~10 seconds** (everything was pre-warmed
by the operator). Data point for next time: with a populated olean cache,
`import Mathlib` costs ~2.6s per file invocation, which sets the floor for every
edit/compile cycle below.

---

## 2026-08-17 22:03:38 — Stage 1: Theorem 1 — **DONE, ZERO `sorry`**

Files: `NonmonicCubic/Basic.lean` (180 lines), `NonmonicCubic/Integrals.lean`
(156 lines), `NonmonicCubic/Theorem1.lean` (167 lines). Total 503 lines.

`lake build` output:
```
✔ [8709/8710] Built NonmonicCubic (4.8s)
Build completed successfully (8710 jobs).
```
Full-project build from a warm olean cache: **~5s**. Individual file check
(`lake env lean NonmonicCubic/Theorem1.lean`): 6.5s.

`#print axioms`:
```
'NonmonicCubic.theorem1' depends on axioms: [propext, Classical.choice, Quot.sound]
'NonmonicCubic.theorem1_probability' depends on axioms: [propext, Classical.choice, Quot.sound]
'NonmonicCubic.volume_T1Set' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Only the three standard Lean axioms — **no `sorryAx`**. `grep -rn sorry
NonmonicCubic/` returns nothing.

### Statements proved

* `NonmonicCubic.theorem1` (`Theorem1.lean:132`):
  `volume {p : ℝ×ℝ×ℝ | p.1 ∈ Icc (-1) 1 ∧ p.2.1 ∈ Icc (-1) 1 ∧ p.2.2 ∈ Icc (-1) 1
   ∧ 0 < Δ₃ p.1 p.2.1 p.2.2} = ENNReal.ofReal ((383/4860 + Real.log 3/48) * 8)`
* `NonmonicCubic.theorem1_probability` (`Theorem1.lean:149`): the same as a
  probability, `(volume T1Set).toReal / (volume cube).toReal = 383/4860 + log 3/48`.

### One simplification vs. the informal proof, worth recording

`reference/THEOREMS.md` derives the band via the critical points `x₋, x₊` of
`g(x) = x³+ax²+bx` and identity S2. In Lean it is much cheaper to skip the
critical points entirely and use the single `ring`-provable identity

```
-27 * Δ₃ a b c = (27c - 9ab + 2a³)² - 4(a² - 3b)³      (Basic.lean:64)
```

which yields *both* branches at once:
* `a² - 3b < 0` ⟹ `Δ₃ < 0` (`Δ₃_neg_of_lt`, Basic.lean:122);
* `a² - 3b ≥ 0` ⟹ `Δ₃ = -27 (c - cLo)(c - cHi)` (`Δ₃_factor`, Basic.lean:98),
  hence `Δ₃ > 0 ↔ cLo < c < cHi` (`Δ₃_pos_iff`, Basic.lean:105),
with `cLo, cHi = (9ab - 2a³ ∓ 2(a²-3b)^{3/2})/27`. This is the *same* S1/S2
content, just obtained by completing the square instead of by symmetric
functions of `x₋, x₊`.

Similarly, the never-clipped lemma is not proved by the reference's
monotonicity argument (∂c_hi/∂a = −x₊² ≤ 0, then the edge a = −1) but from the
closed forms `27 cHi = (a-s)²(a+2s)`, `27 cLo = (a+s)²(a-2s)` (`cHi_eq`,
`cLo_eq`, Basic.lean:130,137): the whole lemma reduces to the scalar inequality
`(a-s)²(a+2s) ≤ 27` on `a ∈ [-1,1], s ∈ [0,2]` (`band_top_bound`,
Basic.lean:146), which `nlinarith` discharges with product hints. The equality
case `(a,s) = (-1,2)`, i.e. `(a,b) = (-1,-1)`, matches the reference's corner.

Both routes are the same mathematics; only the reference's *presentation* was
replaced, not its content. Nothing in the informal proof was found to be wrong.

### Numerical cross-check of the antiderivative (before writing it in Lean)

`F(x) = x(r⁵/6 + 5r³/8 + 45r/16) + (135/16) log(x+r)`, `r = √(x²+3)`, checked by
central differences at 6 points against `(x²+3)^{5/2}` (agreement ~1e-9, the
finite-difference floor), and `F(1)-F(-1) = 383/12 + (135/16) log 3`, giving
`P = 0.10169434037605886` vs `reference/THEOREMS.md`'s
`0.10169434037605886959954086…` — 16 digits.

---

## 2026-08-17 22:11:51 — Stage 2: Theorem 2 — **DONE, ZERO `sorry`**

File `NonmonicCubic/Theorem2.lean` (224 lines) plus 4 new sign lemmas appended to
`Basic.lean`. Whole project: 818 lines, `lake build` **success**, ~6s.

`#print axioms`:
```
'NonmonicCubic.theorem2' depends on axioms: [propext, Classical.choice, Quot.sound]
'NonmonicCubic.theorem2_probability' depends on axioms: [propext, Classical.choice, Quot.sound]
```
No `sorryAx`. `grep -rn sorry NonmonicCubic/` → nothing.

Statements: `theorem2` (volume `= ENNReal.ofReal (1/2880)` on `[0,1]³`) and
`theorem2_probability` (same, divided by the unit cube's volume `1`).

### The one genuinely new difficulty vs. Theorem 1

In Theorem 1 the never-clipped lemma makes the slice of the cube *equal* to the
open region between the band edges. In Theorem 2 the window floor `c = 0` really
does clip (exactly on `b ≤ a²/4`, `cLo_nonpos`/`cLo_nonneg` in `Basic.lean`), and
then the slice and the open region `regionBetween (max cLo 0) cHi` are **not**
equal — they differ on `{c = 0}`, where the cube's slice contains points with
`Δ₃ > 0` (e.g. `Δ₃ a b 0 = b²(a²-4b) > 0`) that the open region excludes.
Handled by a sandwich (`region_subset_slice2`, `slice2_sdiff_subset`,
`volume_snd_eq_zero`, `volume_slice2`, Theorem2.lean:55–116) rather than a set
equality. This is a Lean-side bookkeeping point, not a gap in the informal proof
— the informal proof works with lengths of interval intersections, where the
endpoint is invisible.

The "small miracle" (all fractional powers cancelling) is `slice2_area`
(Theorem2.lean:119): the two `p52` values at `b = a²/4` and `b = 0` are
`(a/2)⁵` and `a⁵`, and after `integral_cHi_gen` + `integral_band_width_gen` the
whole thing is `19a⁵/12960 + a⁵/1620 = a⁵/480` by `ring`.

---

## 2026-08-17 22:22:23 — Stages 3, 4, 5 — statement DONE, proof partial

`lake build`: **success**, 8714 jobs, ~6s warm. Whole project 1374 lines across
7 files. Exactly **5 `sorry`s**, all in Theorem-3 territory, all listed below and
in `REPORT.md`.

### Stage 3 — Theorem 3 statement — **DONE (type-checks; proof `sorry`d)**

`NonmonicCubic/Theorem3Statement.lean`.

* `T3Set` (line 54) — the region of `[-1,1]⁴` with `0 < Δ₄ a b c d`.
* `theorem3` (line 105) — `volume T3Set = ENNReal.ofReal ((641/2430 - Real.log 3/24) * 16)`.
  **`sorry`d.**
* `theorem3_probability` (line 113) — the probability form. **`sorry`-dependent.**
* `volume_cube4`, `measurableSet_T3Set` — **proved.**

**Second-pass check of the transcription** (this was the deliverable that had to
be right): a `ring` proof that our `Δ₄` is *literally Mathlib's own*
`Cubic.discr` —

* `Δ₄_eq_cubic_discr` (line 61): `Δ₄ a b c d = (Cubic.mk a b c d).discr`, where
  `Cubic.discr` is `Mathlib/Algebra/CubicDiscriminant.lean:461`,
  `b²c² - 4ac³ - 4b³d - 27a²d² + 18abcd`. **Proved**, axioms clean.
* plus `Δ₄_one : Δ₄ 1 b c d = Δ₃ b c d`, tying it to the `Δ₃` of the fully
  proved Theorems 1 and 2.

So the Theorem 3 statement is checked against Mathlib, not only against
`VERDICT.md`. Coefficient order verified explicitly: first coordinate is the
**leading** coefficient `a`, last is the constant term `d`.

### Stage 4 — Theorem 3 proof — **PARTIAL (3 `sorry`s)**

`NonmonicCubic/Theorem3Proof.lean`.

**A correction to `TASK.md`'s strategic steer, which I did not follow.**
`TASK.md` says to prefer "`VERDICT.md`'s route 1 … computes the same answer by
nested integration … every step is `intervalIntegral` of an explicit
piecewise-elementary function (polynomials, one `log`)". That is a misreading of
the reference. **Route 1 is a numerical route, not a closed form.** Evidence:

* `VERDICT.md`'s own results table gives route 1 as `0.21801049620261477102`
  with agreement `7.0e-20` — a 19-digit numerical match, not an identity;
* `reference/route1_closed_a.py`'s docstring: only the innermost `a`-integral is
  closed-form ("`G = int_{a0}^1 L/a da`"); the outer `(b, σ)` integral is done by
  tanh-sinh / Gauss-Legendre with bisected breakpoints;
* `VERDICT.md`, "The stretch goal, and a negative result worth recording", says
  outright that this integration order "leaves integrals of algebraic functions
  of the roots of a cubic whose coefficients move with the outer variable, which
  is not elementary in general", with PSLQ finding nothing for `V(1/2)`, `V(1/3)`.

The section of `VERDICT.md` that `TASK.md` points at ("How the closed form is
obtained", the `L1`/`L2`/`F(s)` material) is **route 2's face integral `S_b`**,
not route 1. So the elementary chain really is route 2, and route 2 is what I
formalized.

**And the cone step does not need the divergence theorem.** `TASK.md` avoids
route 2 on the grounds that it "needs Stokes'/divergence-theorem machinery on a
region with a non-smooth (cusped) boundary". It does not. For a cone `R` and the
cube, partitioning by which coordinate attains `max_j |x_j|` and rescaling
`(t,y) ↦ (ty, t)` (Jacobian `t^{n-1}`) gives, by homogeneity alone,
`vol(R ∩ [-1,1]ⁿ) = (1/n) Σ_faces S_face`. It is a change of variables, not a
boundary integral, so the cusps are irrelevant. Written out in the module
docstring of `Theorem3Proof.lean`.

**Proved in Stage 4:**

| lemma | line | content |
|---|---|---|
| `Δ₄_completeSquare` | 110 | `-27a²Δ₄ = (27a²d - 9abc + 2b³)² - 4(b²-3ac)³` (`ring`) |
| `Δ₄_face_b_pos_iff` | 130 | the exact `d`-band on the face `b=1`: `-K₋ < 27a²d < K₊` |
| `Δ₄_face_b_neg` | 159 | `1-3ac < 0 ⟹ Δ₄ < 0` |
| `Kp_add_Km` | 125 | `K₊ + K₋ = 4s³` |
| `L1` | 184 | never clips above: `K₊/27 ≤ a₀²`, for **all** real `s` |
| `L2_clips` | 192 | clips below for `2/3 < s < 2` |
| `L2_no_clip` | 199 | does not clip for `0 < s ≤ 2/3` |
| `L2_alphaM_lt_one` | 207 | `K₋ < 27 ↔ s < 2`, equality exactly at `s = 2` |
| `Fs_branches_agree` | 228 | both branches of `F` equal `11264/18225` at `s = 2/3` |
| `FaceA_eq_T1Set` | 259 | the `a=1` face **is** Theorem 1's set |
| `volume_FaceA` | 264 | `S_a = V(1) = 766/1215 + log 3/6`, **derived from proved Theorem 1** |
| `theorem3_of_faces` | 1961 | the two `sorry`d inputs ⟹ Theorem 3 (the arithmetic) |

`K₊ = (s-1)²(2s+1)`, `K₋ = (s+1)²(2s-1)`, `u = 27a²`, `a₀ = |s²-1|/3`,
`α₋ = √(K₋/27)` all reproduce `VERDICT.md` character for character.

**`sorry`d in Stage 4** (3): `volume_T3Set_eq_faces` (line 253),
`Fs_eq_face_integral` (263), `volume_FaceB` (279). See `REPORT.md`.

**Independent numerical re-verification done this session** (not taken on trust
from the reference): Gauss-Legendre with geometrically graded panels around the
integrable `log` singularity at `s = 1` gives
`S_b = 2.6746132162333494` vs `1454/405 - (5/6)log 3 = 2.674613216233365`
(diff `-1.6e-14`), hence `P = 0.21801049620261376` vs
`641/2430 - log 3/24 = 0.21801049620261476` (diff `-1.0e-15`, i.e. double
precision). Also `F(2/3±)` agrees with `11264/18225` to 11 digits. So the
reference's route 2 reproduces here.

### Stage 5 — discriminant ↔ root count — **STATED, one direction proved**

`NonmonicCubic/DiscriminantRootCount.lean`.

Mathlib scan result (this is the "grep before assuming it's missing" the brief
asked for): Mathlib **has** `Cubic.discr` and
`Cubic.discr_ne_zero_iff_roots_nodup` / `Cubic.card_roots_of_discr_ne_zero`, but
those are about `discr ≠ 0` and *distinctness over a splitting field*. Mathlib
has **nothing** relating the *sign* of a cubic discriminant to the number of
*real* roots. (`discrim` in `QuadraticDiscriminant.lean` does have the sign
story, but only in degree 2.) So this is a genuine Mathlib gap.

* `Δ₄_of_roots` (line 58) — **proved**: `Δ = a⁴((x-y)(x-z)(y-z))²` (`ring`).
* `coeffs_of_factorisation` (line 64) — **proved**.
* `Δ₄_pos_of_three_distinct_roots` (line 73) — **proved**: three distinct real
  roots ⟹ `Δ₄ > 0`.
* `three_distinct_roots_of_Δ₄_pos` (line 101) — **`sorry`**. The converse; needs
  IVT bookkeeping at the two critical points. Classical, not deep, no time.
* `Δ₄_pos_iff_three_distinct_real_roots` (line 110) — the `↔`, hence
  `sorry`-dependent through the above.

---

## 2026-08-17 22:42:14 — Stage 4, `sorry` #3 discharged: `Fs_eq_face_integral`

**`Fs_eq_face_integral` is now fully proved.** Project `sorry` count 5 → **4**.
`NonmonicCubic/Theorem3Proof.lean` grew 308 → 496 lines; project 1374 → 1562.

```
'NonmonicCubic.Fs_eq_face_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
```
No `sorryAx`. `lake build` clean, no warnings other than the 4 remaining
`declaration uses 'sorry'`. Theorem3Proof.lean now takes ~9.4s to check.

### Statement (Theorem3Proof.lean:660)

```lean
theorem Fs_eq_face_integral {s : ℝ} (h0 : 0 < s) (h2 : s < 2) (hs1 : s ≠ 1) :
    Fs s = ∫ a in (a0 s)..1, (Kp s / (27 * a ^ 2) + min (Km s / (27 * a ^ 2)) 1) / a
```

### The statement had to be corrected: `s ≠ 1` was missing

The version I wrote in the first pass (`0 < s`, `s < 2` only) is **false**.
At `s = 1`: `a₀ = |s²−1|/3 = 0`, the integrand behaves like `1/a` near `0`, and
the integral genuinely diverges. Both sides then degenerate to unrelated Lean
junk values. Checked in Lean rather than asserted:

```lean
example : Fs 1 = 23 / 54 := by            -- `0/0 = 0` and `Real.log 0 = 0`
  have ha : a0 1 = 0 := by unfold a0; norm_num
  have hk : Kp 1 = 0 := by unfold Kp; norm_num
  unfold Fs
  rw [if_neg (by norm_num : ¬ (1:ℝ) ≤ 2/3), ha, hk]
  norm_num                                -- ✓ compiles
```
while a non-integrable `intervalIntegral` is `0` by definition. `23/54 ≠ 0`.

Adding `s ≠ 1` is the right fix and costs nothing downstream: `{1}` is
Lebesgue-null in the outer `s`-integral that `volume_FaceB` needs, and `F` does
genuinely blow up there — logarithmically, hence integrably, which is exactly
why `S_b` is finite. **Lesson recorded: a `sorry`d lemma is an unchecked
*claim*, not merely an unfinished proof.**

### Proof structure (follows `VERDICT.md`'s two clipping regimes)

* **`s ≤ 2/3`** — `L2_no_clip` gives `K₋/27 ≤ a₀²`, hence on all of `[a₀,1]`
  `min (K₋/(27a²)) 1 = K₋/(27a²)`; the integrand collapses to
  `(K₊+K₋)/(27a³) = 4s³/(27a³)` by `Kp_add_Km`, and the single antiderivative
  `−2s³/(27a²)` finishes via `integral_eq_sub_of_hasDerivAt`.
* **`2/3 < s < 2`** — `L2_clips` + `L2_alphaM_lt_one` give `a₀ < α₋ < 1`, so the
  integral splits at `α₋` (`integral_add_adjacent_intervals`). Below `α₋` the
  `min` is `1` and the antiderivative `−K₊/(54a²) + log a` produces the `log`
  term; above `α₋` we are back in the first case. The cross terms
  `−K₊/(54α₋²) + 2s³/(27α₋²)` collapse to the constant `1/2` via `α₋² = K₋/27`
  and `K₊ + K₋ = 4s³` — `VERDICT.md`'s "the awkward term `−K₊/(2K₋) + 2s³/K₋`
  collapses to the constant `1/2`". In Lean that whole collapse is the single
  `linear_combination (1458 * a0 s ^ 2) * Kp_add_Km s` closing the branch.

### Mathlib notes for next time

* `div_add_div_same` does not exist under that name in this Mathlib; rewriting
  `Km s = 4*s^3 - Kp s` by `linarith [Kp_add_Km s]` and then `field_simp; ring`
  is the robust substitute.
* `inf_eq_min` does not exist either; `⊓` and `min` are defeq on `ℝ`, so
  `ContinuousOn.inf` can be used directly (`exact hquot.inf hone`) to get
  continuity of `fun a => min (K₋/(27a²)) 1`.
* `((hasDerivAt_id x).fun_pow 2).const_mul (27:ℝ)` normalises to derivative
  `27 * (2 * x)`, **not** `54 * x`; state the `have` in that exact shape and let
  the downstream `congr_deriv` + `field_simp; ring` do the arithmetic.

---

## 2026-08-17 23:01:05 — Stage 4, `sorry` #4 half discharged: `S_b`'s closed form

**`integral_s_Fs` is fully proved**, and with it `volume_FaceB` now reduces to a
single, purely *geometric* `sorry`. Project 1562 → **1903 lines**;
`Theorem3Proof.lean` 496 → 837. Total `sorry` count stays at 4, but one of them
was replaced by a strictly smaller one.

```
'NonmonicCubic.integral_s_Fs' depends on axioms: [propext, Classical.choice, Quot.sound]
'NonmonicCubic.Fs_eq_face_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'NonmonicCubic.volume_FaceB' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```
`lake build` clean; `Theorem3Proof.lean` now checks in ~9.4s.

### What is now proved (Theorem3Proof.lean)

```lean
theorem integral_s_Fs :                                                   -- :757
    ∫ s in (0 : ℝ)..2, s * Fs s = 727 / 270 - 5 / 8 * Real.log 3
theorem volume_FaceB :                                                    -- :1126
    volume FaceB = ENNReal.ofReal (1454 / 405 - 5 / 6 * Real.log 3)       -- from :1112
```
`(4/3) · (727/270 − (5/8)log 3) = 1454/405 − (5/6)log 3`, exactly `VERDICT.md`'s
`S_b`. **So the `log 3` that appears in Theorem 3 is now machine-checked**; what
is not yet checked is that `S_b` equals that integral.

### How

Both branches of `F` are first rewritten with `a₀` and `α₋` eliminated:

* `s_mul_Fs_le` (:848), `s ≤ 2/3`: integrand `= 2s⁴/(3(s²−1)²) − 2s⁴/27`, rational.
* `s_mul_Fs_gt` (:869), `s > 2/3`, `s ≠ 1`: integrand `= G s` where
  `G s = s(2s+1)/(6(s+1)²) + s/2 + (s/2)log(2s−1) − s·log(s−1) − (s/2)log 3 − 2s⁴/27`.

The key cancellation: `K₊/(54a₀²)` is **not** singular at `s = 1`, because
`K₊ = (s−1)²(2s+1)` and `a₀² = (s−1)²(s+1)²/9` share `(s−1)²`, leaving
`(2s+1)/(6(s+1)²)`. The only surviving singularity is the integrable
`−s·log(s−1)`.

Then explicit antiderivatives `H1` (:905) and `H2` (:940) plus the FTC, with
three Mathlib facts doing the heavy lifting at `s = 1`:

* `Real.continuous_mul_log` — `x ↦ x log x` is continuous **at 0**. Writing
  `H2`'s log term as `((s+1)/2)·((s−1)log(s−1))` therefore makes `H2` continuous
  across `s = 1` for free (`continuousOn_H2`, :988), so
  `integral_eq_sub_of_hasDeriv_right_of_le` applies on `[2/3,1]` and `[1,2]`.
* `intervalIntegrable_log'` — `Real.log` is interval integrable on **every**
  interval, unconditionally; translated with `IntervalIntegrable.comp_sub_right`
  it gives integrability of `log(s−1)` across the singularity
  (`intervalIntegrable_G`, :1005).
* `Real.log = log ∘ |·|` in Mathlib, so `log|s−1|` is literally
  `Real.log (s - 1)` — no absolute values appear anywhere in the formalization.

The exceptional point `s = 1` (where `s * Fs s` takes a junk value, cf. the
22:42 entry) is handled by `intervalIntegral.integral_congr_ae` and
`IntervalIntegrable.congr_ae` — `{1}` is null.

### An internal check that fell out of the formalization

Each half of the integral separately produces a `log 5`:
`H1(2/3) = 27638/32805 − (1/2)log 5` (from `log((1−s)/(1+s))` at `s = 2/3`) and
`H2(2/3) = 70457/131220 + (1/16)log 3 − (1/2)log 5` (from `log(s+1)`). They
cancel exactly in `H1(2/3) − H1(0) + H2(2) − H2(2/3) = 727/270 − (5/8)log 3`.
Since `log 5` is not in the final answer, this is a genuine consistency check on
the whole computation, and it is now verified by `ring` rather than by eye.

### What is left of `sorry` #4

`volume_FaceB_eq_integral`: `S_b = (4/3)∫₀² s F(s) ds`. Purely geometric —
slice by `a`, then `c`; the `(a,c,d) ↦ (−a,−c,d)` symmetry (factor 2);
substitute `c = (1−s²)/(3a)` (factor 2/3, region becomes
`{s ∈ (0,2), a ∈ [a₀ s, 1]}`); **then a Tonelli swap** to integrate `a` first.
The swap is the substantive work left, and it is essential rather than
cosmetic: in the other order the `min`'s breakpoint is a root of
`(s+1)²(2s−1) = 27a²` that moves with `a`, and the integral stops being
elementary — `VERDICT.md`'s "negative result worth recording".

Both analytic halves this reduction feeds — `Fs_eq_face_integral` (inner
`a`-integral) and `integral_s_Fs` (outer `s`-integral) — are now proved.

### Mathlib notes

* Interval-integral notation extends to the right: `∫ s in a..b, f s + ∫ ...`
  parses as `∫ s in a..b, (f s + ∫ ...)`. Parenthesise sums of integrals.
* `integral_add_adjacent_intervals` used under `rw [← …]` leaves the midpoint as
  a metavariable; bind the two integrability arguments to `have`s with explicit
  types first.

---

## 2026-08-17 23:15:21 — Stage 4: **the Tonelli swap is proved**, and with it everything after it

`Theorem3Proof.lean` 837 → 1157 lines; project 1903 → **2223**. Total `sorry`
count unchanged at **4** — as with the previous step, the remaining `sorry` was
replaced by a strictly smaller one.

```
'NonmonicCubic.lintegral_faceRegion_swap' depends on axioms: [propext, Classical.choice, Quot.sound]
'NonmonicCubic.post_swap_eval'            depends on axioms: [propext, Classical.choice, Quot.sound]
'NonmonicCubic.inner_lintegral_eq'        depends on axioms: [propext, Classical.choice, Quot.sound]
'NonmonicCubic.Fs_nonneg'                 depends on axioms: [propext, Classical.choice, Quot.sound]
'NonmonicCubic.volume_FaceB_eq_integral'  depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```
`lake build` clean; `Theorem3Proof.lean` checks in ~10s.

### The swap (Theorem3Proof.lean:1222)

```lean
theorem lintegral_faceRegion_swap {f : ℝ → ℝ → ENNReal}
    (hf : Measurable (Function.uncurry f)) :
    ∫⁻ a in Set.Ioc (0:ℝ) 1, ∫⁻ s in faceSliceS a, f a s
      = ∫⁻ s in Set.Ioo (0:ℝ) 2, ∫⁻ a in Set.Icc (a0 s) 1, f a s
```

over `faceRegion = {(a,s) : a ∈ (0,1], s ∈ (0,2), a₀ s ≤ a}` (:1173). Horizontal
slices `faceSliceS a = {s ∈ (0,2) : a₀ s ≤ a}` are exactly where
`reference/route1_closed_a.py`'s `√(1±3a)` limits come from; vertical slices are
`[a₀ s, 1]`, the domain of `F`.

**Doing it in `ℝ≥0∞` was the key decision.** Tonelli
(`lintegral_lintegral_swap`) needs *measurability only* — no integrability
obligations at all — whereas a Bochner/Fubini version would have required
integrability of the un-evaluated double integral, which is exactly the thing we
do not have yet. Both iterated integrals are routed through the indicator of
`faceRegion`; the one wrinkle is that the vertical slice is
`Ioc 0 1 ∩ Ici (a₀ s)`, not `Icc (a₀ s) 1`. They differ by `{0}`, and only when
`a₀ s = 0`, i.e. only at `s = 1` — handled by `faceSliceA_ae` (:1206).

### Everything after the swap is proved too

* `bandLen` (:1301) — clipped `d`-interval length; `faceIntegrand` (:1305) — same
  with the Jacobian `2s/(3a)` of `c = (1−s²)/(3a)`.
* `bandLen_nonneg` (:1330) — by cases on whether the bottom clips: if not, the
  sum telescopes to `4s³/(27a²)` via `Kp_add_Km`; if it does, it is
  `K₊/(27a²) + 1` with `K₊ = (s−1)²(2s+1) ≥ 0`.
* `Fs_nonneg` (:1358) — `F ≥ 0`, being the integral of that length.
* `inner_lintegral_eq` (:1373) — the inner integral is `(2s/3)·F(s)`; **this is
  where `Fs_eq_face_integral` finally gets used**.
* `post_swap_eval` (:1409) — the outer integral is `(2/3)∫₀² s F(s) ds`, whose
  value is `integral_s_Fs`.

### The swap is load-bearing, not decorative

`volume_FaceB_eq_integral` (:1932) is now **proved**:
```lean
  rw [volume_FaceB_eq_pre_swap, lintegral_faceRegion_swap measurable_faceIntegrand,
    post_swap_eval, …]
```

### What is left of `sorry` #4

`volume_FaceB_eq_pre_swap` (:1920):
`vol₃(FaceB) = 2 · ∫_{a ∈ (0,1]} ∫_{s ∈ faceSliceS a} bandLen a s / a · (2s/3)`.
This bundles the three steps *before* the swap: Fubini slicing by `a` then `c`
(the `d`-interval from `Δ₄_face_b_pos_iff`, clipping from `L1`/`L2_clips`); the
symmetry `(a,c,d) ↦ (−a,−c,d)` for the factor `2`; and the substitution
`c = (1−s²)/(3a)` for the Jacobian. All three are standard and need no new
theory.

### Mathlib notes

* `ℝ≥0∞` notation needs `open scoped ENNReal`; without it the parser fails with a
  bare "expected token". Writing `ENNReal` is simpler.
* `set F := … with hFdef` then `rw [hFdef]` does **not** beta-reduce. Add
  `have hFapp : ∀ a s, F a s = … := fun _ _ => rfl` and rewrite with that.
* Inline set-builder braces inside `∫⁻ x in {y | …}, …` fail to parse; name the
  set with a `def` first.
* `div_add_div_same` and `inf_eq_min` (noted earlier) still do not exist here;
  `ContinuousAt.min` doesn't either — use `ContinuousOn.inf` (`⊓` and `min` are
  defeq on `ℝ`).

---

## 2026-08-17 23:31:09 — **`S_b` is fully proved**; `sorry` count 4 → 3

`volume_FaceB_eq_pre_swap` is proved, hence so is `volume_FaceB`. Project
2223 → **2689 lines**; `Theorem3Proof.lean` 1157 → 1623.

```
'NonmonicCubic.volume_FaceB_eq_pre_swap' depends on axioms: [propext, Classical.choice, Quot.sound]
'NonmonicCubic.volume_FaceB'             depends on axioms: [propext, Classical.choice, Quot.sound]
'NonmonicCubic.volume_FaceA'             depends on axioms: [propext, Classical.choice, Quot.sound]
'NonmonicCubic.theorem3''                depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

**Both ingredients of Theorem 3 are now machine-checked:**

| | value | status |
|---|---|---|
| `S_a = V(1)` (`volume_FaceA`, :264) | `766/1215 + log 3/6` | proved (from Theorem 1) |
| `S_b` (`volume_FaceB`, :1946) | `1454/405 − (5/6) log 3` | **proved** |

Only `volume_T3Set_eq_faces` (:625), the cone/face identity `vol₄ = S_a + S_b`,
separates the project from a `sorry`-free Theorem 3.

### How the pre-swap identity went

`volume_FaceB_eq_pre_swap` (:1920) is assembled from four steps:

1. **Symmetry** (`volume_FaceB_eq_two_mul_pos`, :1502). `(a,c,d) ↦ (−a,−c,d)` is
   `x ↦ −x` on the roots and preserves `Δ₄ · 1 · ·` — `Δ₄_face_b_symm` (:1444) is
   the `ring` identity. Measure-preservation comes from
   `Measure.measurePreserving_neg` in each coordinate plus `MeasurePreserving.prod`.
   `FaceB` splits into `{a>0} ⊔ {a<0}` up to the null slab `{a = 0}`, so
   `vol(FaceB) = 2·vol(FaceB ∩ {a>0})`.
2. **Fubini in `a`** (`volume_FaceBPos_eq`, :1881), with the `a`-support
   collapsing to `Ioc 0 1`.
3. **The `(c,d)`-slice** (`volume_sliceB`, :1693). Same shape as Theorems 1–2:
   the slice is the region between the clipped band edges, of width
   `bandLen a (sOf a c)`. The `d`-interval comes from `Δ₄_face_b_pos_iff`; the
   top edge is unclipped by `dHi_le_one` (:1588), i.e. **`L1`**. As in Theorem 2
   the slice and the open region differ on a null set (here `{c = cmax}` and
   `{d = −1}`), handled by a sandwich.
4. **The substitution** `c = (1−s²)/(3a)` (`integral_c_eq_integral_s`, :1792) via
   `intervalIntegral.integral_deriv_smul_comp`, with `cOf a (sHi a) = −1` and
   `cOf a (sLo a) = cmax a`; then `faceSliceS_ae` (:1812) identifies the
   resulting `s`-range `[sLo, sHi]` with `faceSliceS a` up to endpoints.

### The identity that made it clean

`a0_sOf` (:1580): for `a > 0`,

    a₀(√(1−3ac)) = |(1−3ac) − 1|/3 = |−3ac|/3 = a·|c|.

So the **window constraint `|c| ≤ 1` is exactly `a₀ s ≤ a`** — which is exactly
the hypothesis under which `L1` says the band never clips above, and exactly the
condition defining `faceRegion` for the Tonelli swap. The `(a,c)` and `(a,s)`
pictures line up with no case analysis at all. This is not spelled out in
`reference/VERDICT.md`; it fell out of trying to formalize the two descriptions
of the same region and finding they had to agree.

### Mathlib notes

* `div_le_div_iff` no longer exists under that name; `gcongr` handles
  `x/u ≤ y/u` given `0 < u` and is more robust than hunting for the lemma.
* For `√X ≤ √Y` prefer `Real.sqrt_le_sqrt` over `nlinarith` on the squares —
  `nlinarith` needs a product hint it will not find on its own.
* `intervalIntegral.integral_deriv_smul_comp` (the old `integral_comp_smul_deriv`
  is a deprecated alias) wants `∀ x ∈ uIcc a b, HasDerivAt f (f' x) x`,
  `ContinuousOn f'`, and `Continuous g`; the orientation flip afterwards is
  `intervalIntegral.integral_symm` + `← intervalIntegral.integral_neg`.

---

## 2026-08-18 00:00 — **Stage 5 DONE (zero `sorry`)** and the cone identity reduced to its combinatorial core; count 3 → **2**

Project 2689 → **3234 lines**. `lake build` clean: **no warnings at all other
than the two `sorry` notices** (note: `lake build` runs the mathlibStandardSet
linters, `lake env lean` does not — the former is the authoritative check).

### Stage 5 is fully proved — a real Mathlib gap closed

`NonmonicCubic/DiscriminantRootCount.lean` 120 → 311 lines, **0 `sorry`**.
This was done by a sub-agent, on the user's instruction, in parallel with the
cone work; it was interrupted but had already finished.

```
'NonmonicCubic.three_distinct_roots_of_Δ₄_pos'        [propext, Classical.choice, Quot.sound]
'NonmonicCubic.Δ₄_pos_iff_three_distinct_real_roots'  [propext, Classical.choice, Quot.sound]
'NonmonicCubic.theorem1_root_count'                   [propext, Classical.choice, Quot.sound]
'NonmonicCubic.theorem2_root_count'                   [propext, Classical.choice, Quot.sound]
```

The `→` direction (`three_distinct_roots_of_Δ₄_pos`, :257): the completed square
forces `p = b²−3ac > 0`; at the points where `3at+b = ∓√p` the identity
`27a²·f t = u³ − 3pu + q` gives values `q ± 2p^{3/2}`, whose **product** is
`−27a²Δ₄ < 0` and whose **difference** is `4p^{3/2} > 0`, so `f > 0` at one and
`f < 0` at the other. IVT on three intervals (with two explicit far-out points,
no `Tendsto`/`Polynomial` machinery) gives three roots, and three distinct roots
force the factorisation by linear algebra on the quadratic remainder. **No
derivatives anywhere** — the "critical points" are just explicit numbers.

**Capstone**: `theorem1_root_count` (:291) and `theorem2_root_count` (:302) now
state Theorems 1 and 2 as claims about *roots*, with no discriminant in the
statement — i.e. literally the sentences of `reference/THEOREMS.md`, fully
machine-checked. Theorem 3 is not yet in that position only because its volume
still rests on `sorry` #2. (I corrected an over-broad claim the sub-agent had
written in that file's header, which said the sentence was checked "on top of
Theorems 1–3".)

### The cone identity: all analytic content proved

`volume_T3Set_eq_faces` (:625) is now **proved** from a single combinatorial
`sorry`. What got proved:

* `volume_conePiece1` (:390) — **the radial identity**, and the heart of the
  whole cone argument. For any measurable cone `R`, the piece of `[-1,1]⁴` where
  coordinate 1 attains `max_j |x_j|` positively has volume `(1/4)·vol₃(face)`.
  Slice at `x₁ = t`, use homogeneity to identify the slice with `t·face`, and
  `∫₀¹ t³ dt = 1/4`. **This is Fubini plus `vol₃(t·E) = t³ vol₃(E)` — there is no
  boundary integral, so the cusps of `{Δ₄ = 0}` never enter.** It is the concrete
  form of this session's claim that `TASK.md`'s Stokes worry does not apply.
* `volume_conePiece2` (:475) via `measurePreserving_swap12` (:439);
* the other six pieces via `measurePreserving_revMap` (:503) and
  `measurePreserving_negMap` (:490), i.e. the two `ring` symmetries `Δ₄_reverse`
  and `Δ₄_neg`, transported by `volume_piece_transport` (:557).

Left: `volume_T3Set_eq_pieces` (:618) — the eight pieces partition `[-1,1]⁴`
(cover: every nonzero point lies in the piece of its largest coordinate, and
`x = 0` is not in the cone since `Δ₄ 0 0 0 0 = 0`; overlaps: only where
`|x_i| = |x_j|`, a null union of hyperplanes). Pure `measure_iUnion₀` bookkeeping.

### Mathlib notes

* `volume` on `ℝ×ℝ×ℝ` is **not** an `IsAddHaarMeasure` instance out of the box.
  The only missing piece is `IsAddLeftInvariant`, and
  `(inferInstance : ((volume : Measure ℝ).prod volume).IsAddLeftInvariant)`
  supplies it; then `Measure.addHaar_smul_of_nonneg` gives the scaling law
  (`Module.finrank ℝ (ℝ×ℝ×ℝ) = 3` is found by `simp`).
* Coordinate permutations of `ℝ⁴` are cheap: reassociate to `(ℝ×ℝ)×(ℝ×ℝ)` with
  `MeasureTheory.volume_preserving_prodAssoc`, permute with `Prod.swap`/`Prod.map`
  (`Measure.measurePreserving_swap`), reassociate back, `funext x; rfl`. Reversal
  is `Prod.swap ∘ Prod.map Prod.swap Prod.swap` in that presentation — four steps.
* `Ne.lt_or_lt` does not exist here; use `lt_or_gt_of_ne`.
* `Real.sq_sqrt`/`Real.sqrt_pos` live in `Mathlib/Analysis/Real/Sqrt.lean`, not
  `Analysis/SpecialFunctions/Sqrt.lean`.
* Set-scalar-multiplication `t • E` needs `open scoped Pointwise`; `ℝ≥0∞` needs
  `open scoped ENNReal` (or just write `ENNReal`).

---

## 2026-08-18 00:20 — **MISSION 1 COMPLETE: all three theorems proved, zero `sorry`**

`volume_T3Set_eq_pieces` — the eight-piece partition, the last gap — is proved,
and with it `volume_T3Set_eq_faces`, `theorem3`, and `theorem3_probability`.

Project **3780 lines**, 7 files. `lake build`: **no errors, no warnings of any
kind**. The string `sorry` appears nowhere in `NonmonicCubic/` except one
docstring saying so. Full rebuild from a warm Mathlib cache: **55 s**.

```
'NonmonicCubic.theorem1'             [propext, Classical.choice, Quot.sound]
'NonmonicCubic.theorem1_probability' [propext, Classical.choice, Quot.sound]
'NonmonicCubic.theorem1_root_count'  [propext, Classical.choice, Quot.sound]
'NonmonicCubic.theorem2'             [propext, Classical.choice, Quot.sound]
'NonmonicCubic.theorem2_probability' [propext, Classical.choice, Quot.sound]
'NonmonicCubic.theorem2_root_count'  [propext, Classical.choice, Quot.sound]
'NonmonicCubic.theorem3'             [propext, Classical.choice, Quot.sound]
'NonmonicCubic.theorem3_probability' [propext, Classical.choice, Quot.sound]
'NonmonicCubic.Δ₄_pos_iff_three_distinct_real_roots'
                                     [propext, Classical.choice, Quot.sound]
```
No `sorryAx` anywhere.

### How the partition went

* `nrm x = max_j |x_j|`, and each piece gets an inequality-free description:
  `conePiece1 = {x | 0 < nrm x ∧ nrm x ≤ 1 ∧ x.1 = nrm x}`, and likewise for the
  other seven with the appropriate signed coordinate (`conePiece*_eq`). All eight
  follow from the first by `nrm_swap12`/`nrm_revMap`/`nrm_negMap`.
* `tieSet` = the twelve hyperplanes `x_i = ±x_j`; null via
  `Measure.addHaar_submodule` applied to `LinearMap.ker` of an explicit
  functional (`volume_hyper`). This needed a hand-supplied
  `IsAddLeftInvariant` instance for `volume` on `ℝ⁴`.
* **Covering** (`T3Set_diff_eq`): `nrm_eq_abs` says `nrm x = |x_i|` for some `i`,
  and `abs_choice` splits the sign — eight cases. `x = 0` needs no special
  handling because `Δ₄ 0 0 0 0 = 0`, so the origin is not in the cone.
* **Disjointness**: 28 pairwise lemmas, each 5 lines and machine-generated. Two
  pieces force two signed coordinates to be equal, which either contradicts
  `0 < nrm x` (same coordinate, opposite signs) or lands in `tieSet`.
* **Sum** (`volume_T3Set_sum`): seven `measure_union` steps on a right-nested
  union, disjointness discharged by `Set.disjoint_union_right` + the 28 lemmas.
* Six symmetry transports collapse eight terms to `4·P₁ + 4·P₂`; `ring` finishes
  (ENNReal is a commutative semiring, so `ring` works on `+`).

### Final restructure

`theorem3` could not be proved in `Theorem3Statement.lean` (that file is
*imported by* the proof file), so the statement file now holds only the
definitions and the transcription check, and `theorem3` /
`theorem3_probability` live and are proved in `Theorem3Proof.lean`. That removes
the last `sorry`, which was purely an artefact of file ordering.

### Mathlib notes from this step

* `Measure.addHaar_submodule` + `LinearMap.ker_eq_top` is the cheap route to
  "a hyperplane is null"; building the functional as a bare `LinearMap` with
  `map_add'`/`map_smul'` by `simp; ring` takes ten lines.
* `measure_diff_null` → `measure_sdiff_null` in this Mathlib.
* When a right-nested union bottoms out at a single set,
  `simp only [Set.disjoint_union_right]` makes no progress and errors — the last
  step of such a chain must pass the disjointness lemma directly.

`REPORT.md` has been rewritten as the final mission report.
