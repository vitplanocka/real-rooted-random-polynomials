# VERDICT — non-monic cubic on [0,1]^4

**Status: COMPLETE (2026-08-18). Closed form derived, verified numerically and
symbolically by nine independent routes, and machine-checked in Lean 4 / Mathlib
with zero `sorry` and standard axioms only.**

## Result

Let $(a,b,c,d)$ be i.i.d. uniform on $[0,1]$. Then

> **P( a x^3 + b x^2 + c x + d has three real roots ) = 719/2880 − ln(2)/3
> = 0.01860371759112934130536707062510…**

This completes the 2×2 table of the sibling project:

| | uniform [−1,1] | uniform [0,1] |
|---|---|---|
| monic x³+ax²+bx+c | 383/4860 + ln3/48 | 1/2880 |
| non-monic | 641/2430 − ln3/24 | **719/2880 − ln2/3** |

Note the constant is **ln 2**, not ln 3 — the ln 3 contributions cancel between the
two branches of the s-integral (they cancel in both of the two independent
integration orders we ran). This matches the structure of the known *quadratic*
one-sided answer (5+6ln2)/36 rather than that of the symmetric-interval cubics.

## The intermediate quantity

P = 1/5760 + S/2 with

> **S = vol₃{ (a,c,d) ∈ [0,1]³ : a x³ + x² + c x + d has three real roots }
> = 479/960 − (2/3) ln 2 = 0.03686021296003646038851191902788…**

## How it was obtained

1. **Cone decomposition.** Δ₄ is homogeneous of degree 4, so R = {Δ₄ > 0} is a cone.
   Partition [0,1]⁴ by which coordinate is the largest (ties have measure 0). On the
   piece where coordinate j is largest, slice at x_j = t; by homogeneity the slice is
   t·(face x_j = 1), and vol₃(t·E) = t³vol₃(E), so that piece has volume
   (∫₀¹t³dt)·F_j = F_j/4. Hence P = (F_a+F_b+F_c+F_d)/4. Only **four** pieces (not the
   eight of Theorem 3) because on the positive orthant max|x_i| = max x_i.
2. **Face identifications.** The face a = 1 is the *monic* cubic on [0,1]³, i.e.
   exactly Theorem 2, so F_a = 1/2880. Coefficient reversal (a,b,c,d) → (d,c,b,a)
   (i.e. x → 1/x) preserves Δ₄ and [0,1]⁴, so F_d = F_a and F_c = F_b. Hence
   **P = 1/5760 + S/2** with S = F_b.
3. **The face b = 1.** f = a x³ + x² + c x + d. Critical points exist iff 1−3ac > 0;
   with s = √(1−3ac) ∈ (0,1] (the positive orthant forces ac ≥ 0, hence **s ≤ 1** —
   this is the one place where the [0,1] problem differs from Theorem 3, whose s ran
   over (0,2)). Writing u = 27a², the d-band is [−K₋/u, K₊/u] with
   K₊ = (s−1)²(2s+1), K₋ = (s+1)²(2s−1), K₊+K₋ = 4s³, and
   Δ₄(a,1,c,d) = −27a²(d − d_lo)(d − d_hi) identically.
   Domain: c = (1−s²)/(3a) ∈ [0,1] ⟺ a ≥ a₀(s) = (1−s²)/3.
   - **L1 (top never clips):** K₊/27 < a₀² since a₀² − K₊/27 = (s−1)²(3s²+4s+2)/27 > 0.
   - **L2 (bottom clips exactly for s > 1/2):** K₋ < 0 ⟺ s < 1/2, and then
     0 < d_lo < d_hi < 1 so the band is entirely inside the window; for s > 1/2,
     d_lo < 0 and the band is cut at 0.
   So the clipped length is L = C(s)/(27a²) with C(s) = K₊ + min(K₋,0), i.e.
   C = 4s³ for s ≤ 1/2 and C = K₊ for s ≥ 1/2. Then, with the Jacobian
   dc = −(2s/3a)ds,
   S = (2/3)∫₀¹ s F(s) ds,  F(s) = ∫_{a₀(s)}^1 L/a da = (C(s)/54)(9/(1−s²)² − 1).
   The (s−1)² of K₊ cancels the (1−s)⁻² pole, so **the integrand is rational** —
   no arcsinh/arctan, and after integration only ln 2 survives:
   ∫₀^{1/2} = 1199/2160 − ln3/2, ∫_{1/2}^1 = 3341/17280 + ln3/2 − ln2,
   giving S = (2/3)(1199/2160 + 3341/17280 − ln2) = 479/960 − (2/3)ln2.

## Verification performed (all independent of each other)

| check | result |
|---|---|
| Raw 4-D Monte Carlo, N = 2×10⁹, sign of Δ₄ (`src/mc4d.py`) | 0.0186035540 ± 3.0×10⁻⁶ vs closed form 0.0186037176 → **0.054 σ** |
| 12 exact sympy identities for the band, the discriminant factorisation, L1, L2, continuity at s = 1/2 (`src/derive_S.py`) | **all PASS** |
| Second symbolic derivation, opposite integration order (a first at fixed c, then c) (`src/derive_S_alt.py`) | identical closed form, `S_alt − S = 0` symbolically |
| Independent mpmath quadrature at 40 dps, no s-substitution, no case analysis (band endpoints computed numerically from the critical points, clipped numerically) (`src/verify_S.py`) | agrees with 479/960 − (2/3)ln2 to **2.5×10⁻³⁹** |
| Blind `mp.identify(S, ['log(2)','log(3)'])` | returns `479/960 + (−2/3)·log(2)` **unprompted** |
| Blind `mp.pslq([1, S, ln2, ln3])` | `[−479, 960, 640, 0]` ⟹ S = (479 − 640 ln2)/960 |
| Blind `mp.pslq([1, P, ln2, ln3])` | `[−719, 2880, 960, 0]` ⟹ P = (719 − 960 ln2)/2880 |
| **Lean 4 / Mathlib machine proof** (`~/math/nonmonic-cubic-lean/nonmonic_cubic`, `theorem4`) | **`volume T4Set = ENNReal.ofReal (719/2880 − log 2/3)`, zero sorry, axioms `propext, Classical.choice, Quot.sound`** |

## Novelty

Li (1988) (*Comm. Statist. Theory Methods* 17(2):395–409) is the only prior work
claiming exact random-cubic results. Its MR review (reviewer G. Samal, recovered in
full by the sibling project and quoted in that project's `LITERATURE.md` §1) shows
Li treats x³+3ax²+3bx+2c with a,b,c uniform on the **symmetric** intervals
[−h,h], [−k,k], [−l,l]. The one-sided [0,1] cube is not among his cases, and neither
the monic [0,1] value 1/2880 nor the present non-monic [0,1] value is covered.
**UNVERIFIED (inherited):** Li's paper itself remains unobtained; Taylor & Francis
blocks automated fetching and Semantic Scholar shows the abstract elided by the
publisher (and 0 citations). This rests on the MR review only, as in the sibling
project.

A targeted search for this constant was run on 2026-08-18 — see `LITERATURE.md`.
`719/2880`, `479/960` and `0.0186037` return **zero** full-text hits on
Math.StackExchange and MathOverflow (with `1/2880` as a working control), nothing
on OEIS (weak: the *published* comparison constants are absent there too), nothing
relevant on arXiv, and nothing on the general web. The canonical Math.SE thread
(1745310) and the dxdy.ru thread are both about symmetric intervals only.

## Verification performed — second wave (independent agents / methods)

| check | result |
|---|---|
| Randomized-Sobol' QMC of the full 4-D volume via the exact d-band, 32 scramblings × 2²² pts, no cone reduction / no Thm 2 / no s-substitution (`src/qmc_P.py`) | 0.01860360902 ± 2.2×10⁻⁷ → **−0.50 σ** |
| Fully independent 4-D MC by numerical **root counting** (never forms Δ₄; y = ax rescaling + critical-point sign test), N = 2×10⁹, different seed (`src/mc4d_rootcount.py`) | 0.018601804 ± 3.0×10⁻⁶ → **−0.63 σ** |
| — cross-checked per-sample against companion-matrix eigenvalues, N = 2×10⁶ | 2,000,000/2,000,000 agreement, 0 disagreements |
| — same root counter re-run on the three *known* cells (Thm 1, 2, 3) | −1.21σ, +0.29σ, −1.26σ — all reproduce |
| Second, independent QMC of the same 3-D reduced integral (12 scramblings × 2²²) | 0.0186037956 ± 3.0×10⁻⁷ → **+0.26 σ** |
| Direct 3-D MC of all four faces, N = 2×10⁹ each (`src/faces_mc.py`) | F_a−F_d = 1.06σ, F_b−F_c = 0.56σ, F_a−1/2880 = 0.90σ; (F_a+F_b+F_c+F_d)/4 = 0.0186042 ± 1.5×10⁻⁶ → **0.19 σ**; 1/5760 + F_b/2 → **0.04 σ** |
| Deterministic 2-D quadrature of the a=1 face, mpmath at dps 30/40/50 (`src/face_a_check.py`) | **F_a = 1/2880 with residual exactly 0 at all three precisions**; `mp.identify` returns `1/2880` unprompted — the cone slicing + face identification is decisively correct |
| MC of the a=1 face alone, N = 1.2×10¹⁰ pooled, plus a stratified estimator | −1.39σ and +1.49σ from 1/2880 |


## Lean formalization

`~/math/nonmonic-cubic-lean/nonmonic_cubic/` (same development as Theorems 1–3),
four new files, 1268 lines, **zero `sorry`**, axioms `propext, Classical.choice,
Quot.sound` only.

| file | content |
|---|---|
| `NonmonicCubic/Theorem4Statement.lean` | `T4Set`, its measurability, `vol([0,1]⁴) = 1`, and the word-by-word transcription check of the statement |
| `NonmonicCubic/Theorem4Proof.lean` | the **positive-orthant cone decomposition**: `conePieceP1..P4`, `volume_conePieceP1` (Fubini + `vol₃(t·E) = t³vol₃(E)` + `∫₀¹t³ = 1/4`), the four-piece partition modulo the null tie set, `coneFaceP1 RCone = T2Set` (Theorem 2!), and `revMap` for `F_d = F_a`, `F_c = F_b` — giving `volume_T4Set_eq : vol₄(T4Set) = 1/5760 + (1/2)·vol₃(FaceB0)` |
| `NonmonicCubic/Face4B.lean` | the new face computation: the rescaling `Δ₃ 1 (ac) (a²d) = a²·Δ₄ a 1 c d`, `L1` in the form `cHi 1 B ≤ B²`, the slice as a `regionBetween`, the slice area in three regimes, and the outer `a`-integral by explicit antiderivatives in `u = √(1−3a)` — `volume_FaceB0 = 479/960 − (2/3)log 2` |
| `NonmonicCubic/Theorem4.lean` | `theorem4`, `theorem4_probability`, and `theorem4_root_count` (stated with `HasThreeDistinctRealRoots`, no `Δ₄` in sight) |

Reuse from `Theorem3Proof.lean` was substantial: `IsCone`, `RCone`, `isCone_RCone`,
`volume_smul_three`, `lintegral_pow_three`, `swap12`/`revMap` and their
measure-preservation, `nrm`, `tieSet`/`tieCover`/`volume_tieCover`, `Qp`,
`volume_piece_transport`, `nrm_pos_of_mem_RCone`; and from `Basic.lean` /
`Integrals.lean` / `Theorem2.lean`: `cLo`/`cHi`, `Δ₃_pos_iff`, `Δ₃_neg_of_lt`,
`cHi_sub_cLo`, `cLo_nonpos`, `cLo_nonneg`, `cHi_nonneg`, `p32`/`p52` and
`volume_T2Set = 1/2880`.

Two places where the `[0,1]` problem genuinely differs from Theorem 3, and where a
copy of the Theorem 3 proof would have been wrong:

1. **Four pieces, not eight.**  On the positive orthant `maxⱼ|xⱼ| = maxⱼ xⱼ`, so the
   central symmetry `negMap` contributes nothing and the cube splits into four cone
   pieces.  (`Theorem4Proof.T4Set_diff_eq`.)
2. **`s` ranges over `(0,1]`, not `(0,2)`.**  Positivity forces `ac ≥ 0`, hence
   `s = √(1−3ac) ≤ 1`; the bottom of the `d`-band clips at `s = 1/2` (i.e. `ac = 1/4`)
   rather than at Theorem 3's `s = 2/3`, and the top never clips.  Because the
   clipping boundary is where `cLo = 0` — not where the band leaves a window at
   `−1` — `F(s)` here is a **rational** function of `s` with no `log` term at all;
   the logarithm appears only on the final `s`-integration, and only as `log 2`.
