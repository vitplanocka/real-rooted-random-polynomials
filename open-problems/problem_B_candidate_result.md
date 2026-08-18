# Problem B: candidate result for C_clip (UNVERIFIED — external agent, not this campaign)

*Pasted in by the operator on 2026-08-18. This has NOT been independently
verified by anyone in this campaign yet. Treat every claim below as a
hypothesis to be checked from scratch, not as fact. In particular, verify
the headline "factor of 2" claim first — it is the cheapest to check and the
most consequential if wrong, since it asserts an error in the master
`C_clip` triple-integral definition in `open-problems/c_clip_problem_statement.md`,
not just in a closed-form attempt.*

## Claim summary (paraphrased, see full text below for exact statements)

1. **A normalization/factor-of-2 discrepancy.** Let `C_w` denote the triple
   integral exactly as written in `c_clip_problem_statement.md` (domain
   `b in [-1,1]`, `m in (0,M(b)]`, `tau in (-tau_c,tau_c)`, indicator
   `|d(b,m,tau)|>1`). The agent claims:
   - `C_w = 0.000318837105593545968125467766220014008108209807034603431069369321734508358179...`
   - `2*C_w = 0.000637674211187091936250935532440028016216419614069206862138738643469016716358...`,
     which matches the previously-established target to all quoted digits.
   - Conclusion claimed: "the displayed triple integral and the target
     cannot both be correct" — i.e. the agent asserts the formula in
     `c_clip_problem_statement.md` is missing a factor of 2, even though the
     numeric target itself (independently cross-checked there by direct
     Monte Carlo of the geometric clipping problem, not by evaluating this
     formula) is correct.
   - **This is the load-bearing claim and must be checked FIRST, independently,
     via a fresh Monte Carlo or quadrature evaluation of the literal formula
     as written** (do not reuse any of the agent's own code/reasoning for
     this check). If `C_w` (literal formula) really does evaluate to
     `0.0003188...`, that means the formula in `c_clip_problem_statement.md`
     itself has a bug distinct from "no closed form found" — worth
     understanding exactly where before propagating any correction, since
     `C_clip` feeds directly into `16P = U - C_clip` and thus the master
     quartic result.
   - Also sanity-check: does their own Section 1 symmetry rewrite
     (`C_w = 2 * integral over b in [0,1] of the mirrored problem`) actually
     equal the literal full-domain integral as an *identity* (i.e. is it a
     legitimate change of variables using the `(b,tau)->(-b,-tau)`
     involution, with no value change), or does their claimed extra
     "missing factor of 2" sneak in somewhere inside that rewrite instead of
     being a genuine defect in the original problem statement? Distinguish
     these two possibilities explicitly.

2. **A one-dimensional reduction** (Section 2-3) expressing `C_w` as a
   single integral over `S in [S_0, 2/sqrt3]` of an integrand built from:
   elementary boundary terms (`A_1`, `A_2`, both explicitly checkable by
   direct differentiation), and a finite sum of incomplete Beta function
   differences `E(S;u,v)` derived from an explicit Mobius substitution.
   Every algebraic identity here (the roots `alpha,beta`, the cross-ratio
   `t_S(z)`, the Jacobian, the binomial expansion of `(B-At)^8`) should be
   checkable symbolically (sympy) exactly like `Basic.lean`/`closed_form.py`
   style checks elsewhere in this project.

3. **A non-elementary-integrability proof** (Section 5) for the residual
   integral, via: reduction to `y^3 = t(1-t)` (genus 1), a Hermite-reduction
   computation of the coefficient `gamma(rho)` (claimed never zero for
   `0<rho<1`, with an explicit cubic-in-`u=rho+1/rho` positivity argument),
   and a Rosenlicht/Liouville-theorem argument that the resulting abelian
   differential `dt/y` cannot be exact (via Riemann-Roch on a genus-1
   curve). This is a more sophisticated argument than anything checked so
   far in this campaign (previous non-elementary claims, e.g. for Problem
   A's Risch step, were explicitly left UNVERIFIED, not confirmed) — treat
   with commensurate scrutiny. At minimum: verify the `gamma(rho)` formula
   and its claimed positivity numerically/symbolically; the Riemann-Roch
   argument itself can be sanity-checked in spirit (does the differential
   really have a single double pole at infinity and zero residues
   everywhere? is genus really 1 and not 0?) even if a full formal check is
   out of scope.

4. **Numerical verification claim** (Section 4): the agent claims a smooth
   `(S,theta)` reparametrization (`S = (2/sqrt3) cos(theta)`,
   `tau = tau_c cos(3 theta)`) gives an independent quadrature matching the
   1D formula (1) to 75 significant digits. This smooth reparametrization
   itself is worth checking independently (does it actually reproduce
   `Lambda(tau)|dtau| = (128/3) cos(theta) sin^4(theta)(4cos^2(theta)-1) dtheta`
   correctly? — checkable directly from the existing `Lambda` closed form
   already established in this project).

## What to do

1. **Do not integrate anything yet.** Re-derive/re-check every claim above
   from scratch, the same evidence standard as everywhere else in this
   campaign (a write-up claiming verification is not itself verification).
2. Start with claim 1 (the factor-of-2 issue) since it is cheapest to check
   and most consequential — a fresh, independent Monte Carlo or nested
   quadrature of the literal formula in `c_clip_problem_statement.md`,
   written from scratch without reference to the agent's code.
3. If claim 1 checks out as a genuine formula bug in the original problem
   statement (not the agent's error), figure out exactly which step of the
   *original* four independent derivations of that triple-integral formula
   (referenced in `c_clip_problem_statement.md` as "verified independently
   four separate ways") the missing factor of 2 comes from, since all four
   would need the same fix, and it may also implicate other parts of the
   `16P = U - C_clip` decomposition that reused the same reduction.
4. Only after claim 1 is resolved, work through claims 2-4 (the 1D
   reduction and the non-elementary-integrability proof) with the same
   from-scratch discipline used for Problem A.
5. Update `VERDICT.md`/`PROGRESS.md` only for whatever survives independent
   verification, explicitly noting what did and did not check out, exactly
   as was done for Problem A.

## Full text of the agent's submission

(pasted verbatim by the operator, LaTeX rendering partially garbled in
transit — treat all displayed formulas as needing reconstruction from
context/first principles rather than trusted transcription, same caveat as
applied to the Problem A paste)

---

Let `C_w` denote the integral exactly as written in the question. I obtain a
genuine one-dimensional reduction in incomplete beta functions, together
with a rigorous elementary-integrability obstruction.

There is also an important normalization issue:

C_w = 0.000318837105593545968125467766220014008108209807034603431069369321734508358179...

Consequently,

2*C_w = 0.000637674211187091936250935532440028016216419614069206862138738643469016716358...

which agrees with every digit of the quoted target.

Thus the displayed triple integral and the target cannot both be correct.
To obtain the target, the definition must contain an additional factor 2:

C_clip^target = 2 * Integral_{-1}^{1} db Integral_0^{M(b)} dm Integral_{-tau_c}^{tau_c} dtau
                  m^{7/2} Lambda(tau) 1[|d(b,m,tau)|>1]

The discrepancy is not caused by a missed b- or tau-symmetry; those
symmetries are included explicitly below.

### 1. Exact elimination of the b-symmetry

Write d(b,m,tau) = tau*m^{3/2} + b^3/16 - b*m.

The involution (b,tau) -> (-b,-tau) satisfies d(-b,m,-tau) = -d(b,m,tau).

Moreover, d>1 is impossible when b>=0. Indeed,

d(b,m,tau) <= tau_c * m^{3/2} + b^3/16 - b*m
           <= tau_c * (11/16)^{3/2} + 1/16
           = (11*sqrt(33))/72 + 1/16 < 1.

Therefore the d>1 portion occurs only for b<0, while the d<-1 portion is its
mirror image for b>0. Hence, putting x=-b,

C_w = 2 * Integral_0^1 dx Integral_0^{M(x)} dm Integral_{-tau_c}^{tau_c} dtau
        m^{7/2} Lambda(tau) 1[tau*m^{3/2} + x*m - x^3/16 > 1]

This is the only sign factor.

### 2. The useful substitution

Set z = x/(4*sqrt(m)), i.e. x = 4*z*sqrt(m). Then

x*m - x^3/16 = 4*z*(1-z^2)*m^{3/2}.

Define q(z) := 4*z*(1-z^2), P_tau(z) := tau + q(z).

Thus the clipping inequality becomes simply m^{3/2} * P_tau(z) > 1.

The Jacobian is dx = 4*sqrt(m) dz, so m^{7/2} dx = 4*m^4 dz.

The original upper bound m<=M(x) and the constraint x<=1 become

m <= 1/(2*(1-3z^2))   and   m <= 1/(16 z^2)

respectively. Their crossover is z_0 = 1/sqrt(11).

Define Y(z) = sqrt(2*(1-3z^2)) for 0<=z<=z_0, Y(z) = 4z for z>=z_0, so the
upper bound for m is L(z) = Y(z)^{-2}.

Integrating m exactly:

Integral_{P_tau(z)^{-2/3}}^{L(z)} m^4 dm = (1/5) * (Y(z)^{-10} - P_tau(z)^{-10/3})

Therefore

C_w = (8/5) * Integral Integral_{tau > T(z)} Lambda(tau) *
        [ Y(z)^{-10} - (tau+q(z))^{-10/3} ] dtau dz

where T(z) := Y(z)^3 - q(z). Explicitly,

T(z) = [2*(1-3z^2)]^{3/2} - 4z(1-z^2)   for z<=z_0
T(z) = 4z*(17z^2-1)                       for z>=z_0

First branch strictly decreasing: T_1'(z) = -18z/sqrt(2(1-3z^2)) - 4 + 12z^2 < 0
Second branch strictly increasing: T_2'(z) = 204z^2 - 4 > 0 (z>=z_0)

Global minimum: tau_0 = T(z_0) = 24/(11*sqrt(11)).

In particular, clipping uses only positive tau. This rules out another
possible hidden factor of 2.

### 3. A genuine one-dimensional formula

Parameterize positive tau by S: tau(S) = 4*S*(S^2-1), 1<=S<=S_c := 2/sqrt(3).

Let S_0 be the unique root of 4*S_0*(S_0^2-1) = 24/(11*sqrt(11)), numerically
S_0 = 1.073848577374706486632589232516379...

For S in [S_0, S_c], define z_L(S) <= z_0 <= z_R(S) by:

4*(S^3 - S + z_L - z_L^3) = [2*(1-3*z_L^2)]^{3/2}
S^3 - S = 17*z_R^3 - z_R

(monotonicity specifies unique real roots). At S=S_0: z_L(S_0)=z_R(S_0)=z_0.
At S=S_c, the left endpoint is z_- = x*/sqrt(3*x*^2+8), x*=-b*, so the
stated irreducible cubic for b* is indeed present in the geometry.

Define W(S) := 4*S*(3*S^2-1)*(4-3*S^2)^{3/2}. This is exactly
Lambda(tau(S)) * dtau/dS.

Elementary boundary terms: let h(z)=1-3z^2, and

A_1(z) = z/(256*h(z)^4) + 7z/(1536*h(z)^3) + 35z/(6144*h(z)^2)
         + 35z/(4096*h(z)) + (35*sqrt(3)/4096) * artanh(sqrt(3)*z)

so that A_1'(z) = 1/[2(1-3z^2)]^5 = [2*(1-3z^2)]^{-5}.

Also A_2(z) = -1/(9*4^10*z^9), A_2'(z) = (4z)^{-10}.

The only remaining object is an explicit incomplete-beta expression for
Integral_u^v [4*(S^3-S+z-z^3)]^{-10/3} dz.

#### Finite incomplete-beta expression

Set D=sqrt(4-3S^2), alpha=(-S+D)/2, beta=(-S-D)/2, A=S-alpha=(3S-D)/2,
B=S-beta=(3S+D)/2. Then

4*(S^3-S+z-z^3) = 4*(S-z)*(z-alpha)*(z-beta)

Cross-ratio: t_S(z) = [A*(z-beta)] / [B*(z-alpha)]. For alpha<z<S,
0<t_S(z)<1.

For 0<p<q<1, Delta B_{p,q}(a,b) := B_q(a,b) - B_p(a,b) (incomplete beta,
analytically continued; real and unambiguous since interval stays strictly
inside (0,1)).

Define

E(S;u,v) := 1/[4^{10/3} * (A*B*D)^{17/3}] *
    Sum_{j=0}^{8} C(8,j) * B^{8-j} * (-A)^j *
      DeltaB_{t_S(u),t_S(v)}(j - 7/3, -7/3)

This follows from the exact Mobius identities:

z-alpha = tAD/(B-At),  z-beta = BD/(B-At),  S-z = AB(1-t)/(B-At)

and dz = [ABD/(B-At)^2] dt, giving

Integral [4*(S^3-S+z-z^3)]^{-10/3} dz
  = 1/[4^{10/3}*(ABD)^{17/3}] * Integral (B-At)^8 * t^{-10/3} * (1-t)^{-10/3} dt

and expansion of (B-At)^8 gives the finite beta sum.

Therefore the promised one-dimensional formula is:

C_w = (8/5) * Integral_{S_0}^{2/sqrt3} W(S) *
        [ A_1(z_0) - A_1(z_L(S)) + A_2(z_R(S)) - A_2(z_0)
          - E(S; z_L(S), z_R(S)) ] dS            ... (1)

The endpoint S=2/sqrt3 is understood by continuity; the apparent
singularities in the beta representation cancel, while W(S)->0.

Equation (1) has only one actual integration variable. All remaining
quantities are algebraic functions, elementary functions, and standard
incomplete beta functions.

For the value quoted in the question, replace the prefactor 8/5 by 16/5.

### 4. Numerical verification

Evaluated the original written integral two structurally different ways:

- Smooth two-dimensional (z,theta) quadrature, using tau = tau_c*cos(3*theta):
  0.0003188371055935459681254677662200140081082098070346034310693693217345083581792342263...
- One-dimensional formula (1), using the finite incomplete-beta expression:
  same first 75 significant digits.

Smooth independent parametrization uses S = (2/sqrt3)*cos(theta),
tau = tau_c*cos(3*theta), and

Lambda(tau)*|dtau| = (128/3) * cos(theta) * sin^4(theta) * (4*cos^2(theta)-1) dtheta

Finally: 0.000637674211187091936250935532440028016216419.../2 =
0.0003188371055935459681254677662200140081082095..., matching the
displayed integral.

### 5. A rigorous elementary-integrability obstruction

The non-elementary part is not an artifact of the beta notation.

For fixed S in (S_0, 2/sqrt3), consider P_S(z) = 4*(S^3-S+z-z^3). The
algebraic curve w^3 = P_S(z) has three distinct branch points. The same
Mobius transformation used above sends it to y^3 = t*(1-t). This is a
genus-one curve: the degree-three map to the t-sphere is totally ramified
at 0,1,infinity, so Riemann-Hurwitz gives g=1.

More strongly, Hermite reduction gives:

Integral (1-rho*t)^8 * t^{-10/3} * (1-t)^{-10/3} dt
  = d[ R_rho(t) * t^{-7/3} * (1-t)^{-7/3} ] + gamma(rho) * t^{-1/3} * (1-t)^{-1/3} dt   ... (2)

where rho = B/A in (0,1), R_rho(t) is the unique polynomial of degree at
most 7 satisfying

t*(1-t)*R_rho'(t) + (7/3)*(2t-1)*R_rho(t) + gamma(rho)*t^3*(1-t)^3 = (1-rho*t)^8

and direct coefficient comparison gives

gamma(rho) = -(10/7) * (rho^2-rho+1) *
             (11*rho^6 - 33*rho^5 + 12*rho^4 + 31*rho^3 + 12*rho^2 - 33*rho + 11)

This coefficient never vanishes for 0<rho<1. For example, the palindromic
sextic equals rho^3 * (11*u^3 - 33*u^2 - 21*u + 97), u = rho + 1/rho >= 2,
and the cubic in u has positive minimum 54 - (11/108)*sqrt(22) > 0.

Thus the incomplete beta term B_t(2/3,2/3) = Integral t^{-1/3}*(1-t)^{-1/3} dt
is unavoidable.

Direct Liouville proof that this differential is not elementary: on
y^3 = t*(1-t), the differential omega = dt/y has one double pole at the
unique point at infinity and has zero residues everywhere. Rosenlicht's
algebraic form of Liouville's theorem says an algebraic differential with
an elementary primitive must be an exact differential plus a sum of
logarithmic differentials.

Because omega has zero residues, the logarithmic part must vanish after
choosing the constants to be Q-linearly independent. Hence elementary
integrability would require omega = dg for a meromorphic function g. But
then g would have exactly one simple pole at infinity. A genus-one curve
admits no nonconstant meromorphic function with a single simple pole: by
Riemann-Roch, l(P)=1 for a degree-one divisor P. This is a contradiction.

Therefore: Integral P_S(z)^{-10/3} dz is non-elementary for every relevant
generic S.

Did you know? The obstruction already occurs on genus one -- the smallest
possible positive genus -- not on a complicated high-genus curve.

### 6. What this does and does not prove

The exact outcome is:

- The stated target is twice the stated integral.
- The written integral has the exact one-dimensional representation (1).
- One of the remaining algebraic integrations is provably non-elementary.
- The natural transcendental object is an elliptic Abelian integral,
  specifically an incomplete beta function on y^3 = t*(1-t).

This does not prove that the final definite number cannot accidentally
collapse to a combination of elementary constants, elliptic periods, or
other specially chosen constants. Such a claim is not mathematically
well-posed until "reasonable terms" is defined as a precise field or
algebra of constants. The reduction does show why the previous elementary
PSLQ basis was structurally too narrow: the intrinsic object is an
incomplete elliptic period evaluated at moving algebraic endpoints, and the
right endpoint itself lies on the nonsingular plane cubic
S^3 - S = 17*z^3 - z.

Thus the remaining constant is naturally an iterated elliptic period,
rather than an elementary-logarithmic period.
