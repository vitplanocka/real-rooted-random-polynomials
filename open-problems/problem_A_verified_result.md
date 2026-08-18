# Problem A: verified 1D integral representation

*Result contributed by an external agent (not this campaign), independently
verified by the operator's local session on 2026-08-18 before being handed
here for integration. Read this file, verify it AGAIN yourself (do not just
trust this write-up), then integrate into VERDICT.md/PROGRESS.md if your own
check agrees.*

## The result

For $(a,b,c)$ i.i.d. $N(0,1)$,

$$p = \mathbb{P}(x^3+ax^2+bx+c \text{ has three real roots}) = \frac{1}{\pi}\int_0^\infty e^{-\frac{x^4(x^4+4x^2+9)}{2(x^4+4x^2+1)}} \cdot \frac{2(x^4+6x^2+3)}{\sqrt{x^4+4x^2+1}\,(x^4+4x^2+9)}\,dx$$

This is a **single one-dimensional integral of elementary functions only** —
no discriminant indicator, no multivariate integration, no normal CDF/erf in
the final form. It is derived via a Kac–Rice level-crossing argument (the
same technique underlying Edelman–Kostlan, which our own novelty search
already confirmed doesn't contain this specific result) plus an exact
cancellation using Owen's T-function to eliminate the CDF term that a naive
Kac–Rice application would leave behind.

## What was independently verified here (methodology + exact results)

Everything below was re-derived/re-checked from scratch by this operator's
session, using sympy for symbolic identities and mpmath for numerics — the
external agent's derivation was **not** taken on trust at any step.

1. **Foundational quantities**, from first principles (not from the agent's
   write-up): with $q(x)=x^4+x^2+1$, $u(x) = (x^2,x,1)/\sqrt{q(x)}$ (unit
   vector), $Z(x) = (a,b,c)\cdot u(x) \sim N(0,1)$ pointwise, $h(x) = x^3/\sqrt{q(x)}$:
   - $v(x)^2 := \operatorname{Var}(Z'(x)) = \|u'(x)\|^2$ — computed directly via
     sympy, confirmed **exactly equal** to the claimed $\dfrac{x^4+4x^2+1}{q(x)^2}$
     (residual `0`, symbolic).
   - $h'(x)$ — computed directly, confirmed **exactly equal** to the claimed
     $\dfrac{x^2(x^4+2x^2+3)}{q(x)^{3/2}}$ (residual `0`, symbolic).
2. **Equation (7)** ($h^2+z^2 = x^4(x^4+4x^2+9)/(x^4+4x^2+1)$): verified
   **exactly by hand** (polynomial expansion) and confirmed by sympy
   (residual `0`).
3. **Equation (8)** ($v+\theta' = 2(x^4+6x^2+3)/[\sqrt{x^4+4x^2+1}\,(x^4+4x^2+9)]$,
   where $\theta=\arctan(z/h)$): sympy could not simplify the symbolic
   difference to zero (nested-radical limitation, not a red flag by itself),
   so checked numerically at 6 points via central-difference $\theta'$ at 50
   decimal digits working precision — agreement **to ~31 digits at every
   point** (limited by the finite-difference step, not the formula).
4. **The main integral**: assembled directly from the *verified* pieces
   above (not from the agent's possibly-mistyped "boxed" display, which had
   OCR/formatting corruption) and evaluated at 90 digits of working
   precision via `mpmath.quad`. Result:

       0.169929382623479502656443157131761902134057261454631531532741970757068791033074179...

   This **matches our own independently-established value to all 54
   previously-known digits and extends it by dozens more** — the two were
   derived by completely different methods (ours: coefficient/root-space
   quadrature of the discriminant region; this: Kac–Rice level-crossing).
5. **Independent second check** (the agent's discriminant-completing-the-square
   route, their eq. 9–10): eq. (9), the algebraic identity
   $\Delta = -27(c-ab/3+2a^3/27)^2+\frac{4}{27}(a^2-3b)^3$, verified by sympy
   to be **exactly** our own already-proven discriminant identity (residual
   `0` against $\text{-}27\Delta_3=(27c-9ab+2a^3)^2-4(a^2-3b)^3$ from
   `THEOREMS.md`/the Lean development). The resulting 2D integral (10) was
   evaluated independently at double precision: **agrees to ~15 digits**
   (`0.16992938262347948` vs. target, estimated quadrature error `2.4e-12`).

**Not independently re-verified**: the closing Risch-algorithm argument for
why the integral has no elementary antiderivative (the pole analysis at
zeros of $x^4+4x^2+9$). The pattern of argument is standard and plausible,
but this operator's session did not re-derive it. Treat as *unverified, not
false* — worth a fresh check if the "no closed form" conclusion matters for
how this gets written up (it does not affect the correctness of the boxed
formula itself, only whether it can be reduced further).

## What to do

1. Verify all of the above yourselves — re-run the same checks
   independently (do not just re-read this file and take it on faith; the
   whole point of this campaign's evidence standard is that a write-up
   claiming verification is not itself verification).
2. If your independent check agrees: this **resolves Problem A** to
   `TASK2.md`'s standard — not as a finite combination of named constants,
   but as an honest, fully rigorous, single-integral-of-elementary-functions
   closed form, in the same spirit as Owen's T-function or the error
   function itself being accepted "closed forms" in the literature. Update
   `VERDICT.md`'s Problem A section accordingly: change the status from
   "best numeric, no closed form found" to reflect this, but preserve the
   existing 54-digit numeric evidence and the honest PSLQ-negative section
   (a *named-constant* closed form genuinely was not found; a *definite
   integral* closed form was — say both, don't let one erase the other).
3. Re-run (or at least sanity-check) the novelty search specifically for
   this integral representation / this Kac–Rice + Owen's-T reduction
   technique applied to cubic real-rootedness — it is a different kind of
   artifact than a numeric value, and the existing novelty section's digit
   searches don't cover it.
4. Consider whether this is now a legitimate Lean formalization candidate:
   unlike Problem B (which still has an unresolved numeric gap), Problem A's
   boxed formula is a fully closed, provable statement (a specific
   Kac–Rice/Rice-formula identity plus an explicit definite integral) — a
   real but different formalization target than the Mission-1 style
   discriminant-volume statements. Flag this as a stretch goal in
   `VERDICT.md` rather than starting it immediately, consistent with
   `TASK2.md`'s original sequencing.
5. Get the exact statement of the Risch/non-elementary-antiderivative claim
   independently checked (or explicitly re-flagged as unverified) before
   asserting "no elementary closed form" anywhere final-sounding.
