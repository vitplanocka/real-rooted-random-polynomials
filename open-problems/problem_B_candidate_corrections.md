# Corrections to the external `C_clip` submission

Standalone, copy-pasteable. Concerns `problem_B_candidate_result.md`.
Full verification record: `problem_B_verification_2026-08-18.md`.

Overall: the submission is substantially correct and its 1-D reduction is
sound. Three errors below are transcription-level — each was found by
independent symbolic re-derivation, and with corrections (1) and (2) applied the
1-D formula reproduces the target to **all 75 quoted significant digits** at
dps 120. Item (4) is not an error but a simplification worth making.

---

## (1) `A_1`: the `artanh` coefficient is 3× too large

**As written** (with `h(z) = 1 − 3z²`):

    A_1(z) = z/(256 h^4) + 7z/(1536 h^3) + 35z/(6144 h^2) + 35z/(4096 h)
             + (35*sqrt(3)/4096) * artanh(sqrt(3) z)

This does **not** satisfy the stated `A_1'(z) = [2(1−3z²)]^{-5}`. The exact
symbolic residual is

    A_1'(z) − [2(1−3z^2)]^{-5}  =  35/(2048*(1 − 3z^2))   ≠ 0

**Correct version** — solving the ansatz gives a *unique* solution, and the first
four coefficients are right; only the last is wrong:

    A_1(z) = z/(256 h^4) + 7z/(1536 h^3) + 35z/(6144 h^2) + 35z/(4096 h)
             + (35*sqrt(3)/12288) * artanh(sqrt(3) z)

i.e. **`35*sqrt(3)/12288`, not `35*sqrt(3)/4096`**. With this the residual is
exactly 0 (sympy `simplify` → 0), confirmed numerically at
z = 0.05, 0.15, 0.3, 0.45, 0.57.

`A_2(z) = −1/(9·4^10·z^9)` with `A_2'(z) = (4z)^{-10}` is correct as written.

---

## (2) The Möbius / cross-ratio map is inverted

**As written:**

    t_S(z) = [A*(z − beta)] / [B*(z − alpha)]

This sends `z = beta -> 0`, `z = S -> 1`, `z = alpha -> infinity`, so on
`alpha < z < S` it takes values in `(1, infinity)`, **not** `(0,1)` as the
submission states. All four Möbius identities fail with it, and because
`(1−t)^{-10/3}` is then evaluated across its branch cut, `E(S;u,v)` comes out
**complex** (e.g. `0.1148 − 0.1988i` at `S = 1.10`, against the true `7.5446`).

**Correct version** — the reciprocal, with `alpha` and `beta` exchanged:

    t_S(z) = [B*(z − alpha)] / [A*(z − beta)]
           = [(z − alpha)/(z − beta)] * [(S − beta)/(S − alpha)]

    (inverse:  z(t) = (B*alpha − A*t*beta)/(B − A*t) )

With this map `t_S(alpha) = 0`, `t_S(S) = 1`, `t` is monotone increasing on
`(alpha, S)`, and all four stated identities

    z − alpha = t*A*D/(B − A*t)
    z − beta  = B*D/(B − A*t)
    S − z     = A*B*(1 − t)/(B − A*t)
    dz        = [A*B*D/(B − A*t)^2] dt

hold with **exact zero residuals**. The incomplete-beta sum then matches direct
quadrature of `Integral P_S(z)^{-10/3} dz` to **45–58 digits** at every `S`
tested.

Everything else in that section is correct as written: the factorization
`4(S^3−S+z−z^3) = 4(S−z)(z−alpha)(z−beta)`; `A = (3S−D)/2`, `B = (3S+D)/2`,
`B − A = D`; the exponent `(A*B*D)^{17/3}` (all three exponents genuinely equal
`−17/3`, so lumping them is legitimate); the factor `(B − A*t)^8`; and the
incomplete-beta parameters `(j − 7/3, −7/3)`.

---

## (3) The minimum bound has its fraction inverted

**As written:** "the cubic in `u` has positive minimum `54 − (11/108)*sqrt(22) > 0`".

For `q(u) = 11u^3 − 33u^2 − 21u + 97` on `u >= 2`:
`q'(u) = 3(11u^2 − 22u − 7)`, critical points `u = 1 ± 3*sqrt(22)/11`, the
relevant one being `u = 1 + 3*sqrt(22)/11 ≈ 2.27920`. Hence

    **min_{u >= 2} q(u) = 54 − (108/11)*sqrt(22) ≈ 7.948645**

not `54 − (11/108)*sqrt(22) ≈ 53.522272`. The fraction `108/11` was inverted.
(Cross-check: `q(2) = 11`, consistent with a minimum of ≈ 7.95 just to its
right.)

**The conclusion is unaffected** — `q > 0` on `[2, infinity)`; `q` has only one
real root, at `u ≈ −1.60627`.

Two related strengthenings worth folding in, both verified here:

* The palindromic substitution
  `11ρ^6 − 33ρ^5 + 12ρ^4 + 31ρ^3 + 12ρ^2 − 33ρ + 11 = ρ^3*(11u^3 − 33u^2 − 21u + 97)`,
  `u = ρ + 1/ρ`, is **exact** (the constants `−21` and `97` are right).
* The submission asserts `γ(ρ) ≠ 0` on `(0,1)` without proof. Sturm
  root-counting supplies one, and gives more than claimed: **`γ` has no real
  root at all**, and `γ < 0` throughout `(0,1)` (`γ(0) = γ(1) = −110/7`,
  `γ(1/2) = −1215/896`). Since all three roots of `P_S` are real for
  `S < 2/sqrt(3)`, `ρ` is real, so the conclusion holds for **every** admissible
  `S`, not merely generic ones.

The `γ(ρ)` formula itself is confirmed exactly, as is the Hermite relation
`t(1−t)R' + (7/3)(2t−1)R + γ*t^3*(1−t)^3 = (1 − ρt)^8` (coefficient `7/3`, sign
of `(2t−1)` and power `t^3(1−t)^3` all correct; 9×9 system has a unique
solution; pointwise differential residual ~1e-33).

---

## (4) Section 5 is over-engineered: Chebyshev settles the residual in one line

The genus-1 / Rosenlicht / Riemann–Roch argument is **sound** — the curve
`y^3 = t(1−t)` really is genus 1 (confirmed three ways: Riemann–Hurwitz with
total ramification over `0, 1, infinity`; the homogenisation is a smooth plane
cubic; Weierstrass form `V^2 = U^3 + 16`, `j = 0`), and
`div(dt/y) = P_0 + P_1 − 2P_inf` really does have one double pole, zero
residues, and degree `0 = 2g − 2`.

But it proves something classical. The residual

    Integral t^{-1/3} (1−t)^{-1/3} dt

is a **binomial differential** `Integral t^m (a + b t^n)^p dt` with `m = −1/3`,
`n = 1`, `p = −1/3`. **Chebyshev (1853)**: elementary iff one of `p`,
`(m+1)/n`, `(m+1)/n + p` is an integer. Here they are `−1/3`, `2/3`, `1/3` —
none an integer. **Non-elementary, one line, no Riemann surfaces.**

Recommendation: replace the whole of Section 5's geometric apparatus with a
citation of Chebyshev, and present the **Hermite reduction** as the new
contribution — which it is, since `(1 − ρt)^8 t^{-10/3} (1−t)^{-10/3}` is a
*trinomial* and therefore outside Chebyshev's reach. That is the part genuinely
doing work, and it is also the part whose key assertion (`γ ≠ 0`) was left
unproved; see (3) above for the proof.

If the geometric argument is kept anyway, four expository gaps should be closed:

* "choose the constants `Q`-linearly independent" needs the integer-exponent
  rescaling **plus** "a function with empty divisor on a *complete* curve is
  constant" — the latter is where compactness of the smooth projective model is
  essential and it is omitted;
* Rosenlicht's no-new-constants hypothesis should be invoked explicitly;
* the map to `y^3 = t(1−t)` is **birational**, not literally "the same Möbius
  transformation" — `w` must also be rescaled by `(γt + δ)` and by a cube root of
  a constant;
* "three distinct branch points" requires `S ≠ 1/sqrt(3)`; harmless here, since
  `S` ranges over `(1.0738, 1.1547)`, but it should be stated.

---

## Not an error, but must not be repeated downstream

The submission's "factor of 2" report is **arithmetically correct** — the
correct integrand is `2*m^{7/2}*Lambda(tau)`, the `2` being the Jacobian
`|d(b,c,d)/d(b,m,tau)| = 2*m^{3/2}` — but the omission was in the ad-hoc problem
statement handed to the external agent, **not** in this campaign's derivations,
which already carry the factor. `U`, `C_clip` and `16 p_B = U − C_clip` are
unchanged. Do not "fix" anything on the basis of that report.

One further correction in the other direction: this campaign's earlier remark
that the `b`-integral "runs over a **high-genus curve**" was wrong. The relevant
curve is genus **1**.
