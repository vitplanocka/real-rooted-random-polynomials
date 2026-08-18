# Literature Review — Real-Rooted Random Polynomials

*Compiled 2026-08-17 from a parallel 8-agent literature sweep (7 research angles +
completeness critic; ~614 web/tool queries) plus a targeted prior-art search on the
constants derived in this project. Raw structured findings:
`results/literature_sweep_raw.json`.*

## 1. Novelty status of our theorems

**Theorem 1 (383/4860 + ln3/48): never stated or published as this probability
anywhere findable — but with two real prior-art caveats.**
**Theorem 2 (1/2880): likely new, no caveats found.**
**Theorem 3 (641/2430 − ln3/24): the value is not new — it is the dxdy.ru
thread's candidate — but the derivation, its independent verification, and the
refutation of a conflicting value this project itself had produced, are new.
See the dedicated subsection below.**

Negative evidence (both the 8-agent sweep and the targeted constants search):

- Math.SE and MathOverflow's own search engines return **zero threads** on the monic
  case ("We couldn't find anything" for `"x^3+ax^2+bx+c" probability real roots`);
  full-site MSE searches for `383/4860`, `0.10169`, `1/2880` empty.
- **OEIS queried directly**: digit search 1,0,1,6,9,4,3,4,0,3,7,6,0,5 → "the terms
  do not match anything in the table". DuckDuckGo `"383/4860"`: explicit
  "No results found".
- The published exact literature stops at **degree 2** (see §3); the references of
  the 2021/2023 quadratic papers contain no cubic work and do not cite Li.
- The sweep's critic **independently re-derived the same closed form** during the
  search and re-verified it with independent code: fresh 2×10⁸ MC on the raw
  discriminant (−0.35σ) and P_unit = 1/2880 confirmed by a 4×10⁸ MC (−0.05σ).

**Caveat A — dxdy.ru forum thread (June 2026, AI-derived, unrefereed).**
Thread https://dxdy.ru/topic162889.html (started 2026-06-06; found only via a
2026-06-10 answer to MSE 1745310). Post p1725667 (user tolstopuz, 2026-06-08;
re-derived 2026-08-13 by an explicitly AI-generated "GPT-5.6" proof) computes the
NON-monic cubic probability via a ratio-density decomposition whose core
intermediate is **V₀ = 766/1215 + ln(3)/6** — "the volume of the region where
|e₁|,|e₂|,|e₃| ≤ 1 and the roots are real" for t³−e₁t²+e₂t−e₃. That is exactly
8 × our P_sym. The thread **never divides by 8, never states 0.101694…, and never
interprets V₀ as the monic probability**; it is not indexed by any search engine
(searches for `766/1215`, `641/2430`, `383/4860` return nothing). So the volume
identity has informally existed since 2026-06-08; the probability statement and an
independent verified proof are ours. The thread's headline result is a closed-form
candidate for the NON-monic cubic, **I = 641/2430 − ln(3)/24 ≈ 0.2180105** — which
this project confirmed exactly, by an independent derivation, on 2026-08-17
(Theorem 3; see immediately below).

**Theorem 3, resolved 2026-08-17.** The candidate above conflicted with this
project's own literature-sweep quadrature (0.217993225 ± 5e-8) by 1.7e-5 — far
outside both claimed error bars. A dedicated investigation (full record:
`VERDICT.md`, `PROGRESS.md`) settled it decisively: **the dxdy candidate is
correct**, via a derivation that recognizes the discriminant region as a
homogeneous cone, applies the divergence theorem to reduce the 4D volume to a
sum over the cube's 8 faces (Euler's identity kills the lateral-boundary term),
and uses central + reversal symmetry to collapse that to Theorem 1 plus one new
3D volume S_b = 1454/405 − (5/6)ln3, elementary once the leading coefficient is
integrated out first. Verified: sympy exact match; an independent numerical
route sharing no step with the derivation, agreeing to 19 significant digits;
blind PSLQ recovery of S_b from its 22-digit numeric value; 4×10¹⁰-sample Monte
Carlo (−0.73σ). **The sweep's 0.217993225 is refuted**, wrong by +1.7271e-5
(~345× its claimed error bar); a genuine attempt to reconstruct the specific
failure mode was unsuccessful (a naive reconstruction of its recorded method
lands within 9e-10 of the truth, not at 0.217993225) — recorded honestly in
`VERDICT.md` rather than papered over. Two real numerical hazards of this
integrand family were identified along the way (a √a endpoint singularity at
vanishing leading coefficient, and float64 losing clipping breakpoints near
it) — real, but insufficient on their own to explain the sweep's error.

**Caveat B — Li (1988), now much sharper.** Hung C. Li, "The exact proability
[sic] that the roots of quadratic, cubic, and quartic equations are all real if
the equation coefficients are random", *Comm. Statist. Theory Methods*
17(2):395–409 (1988), DOI 10.1080/03610928808829630, Zbl 0641.60075, MR 89j:60069.
The **full MR review was recovered** (reviewer G. Samal; archive.org item
`sim_mathematical-reviews_1989-10_89j`, pp. 5639–5640): Li obtains "an expression
for the exact probability" for the random cubic **x³ + 3ax² + 3bx + 2c = 0** with
case (a): a, b, c uniform on [−h,h], [−k,k], [−l,l]. **At h = k = 1/3, l = 1/2
this is exactly our Theorem 1 model** (3a, 3b, 2c iid U[−1,1]). So Li claims an
exact expression for a parametric family containing our case; whether his
expression is correct and reduces to 383/4860 + ln(3)/48 is unverifiable without
the paper (paywalled; 2 citers ever, neither quotes a value; MR review quotes no
formulas). Earlier reading via Limmer 1999 ("non-uniform distributions") was too
optimistic. For **Theorem 2**: Li's cubic special cases are all *symmetric*
intervals — the one-sided [0,1] cube is **not** among them, so 1/2880 stays
likely-new regardless.

Recommended claim language until an ILL check of Li (1988):

> "To our knowledge the probability 383/4860 + ln(3)/48 has not been previously
> published. The equivalent volume appears, unnormalized and uninterpreted, in an
> informal AI-derived forum derivation of the non-monic case (dxdy.ru, June 2026).
> Li (1988) derived an exact expression for a parametric family of random cubics
> containing this model as a special case; his paper is effectively unobtainable
> and no value from it has ever been reproduced. The U[0,1] value 1/2880 appears
> to be new."

Remaining recovery route for Li: interlibrary loan / T&F purchase of the article
itself (the MR review, zbMATH entry, and both citing works are now exhausted).

## 2. Exact anchors — confirmed with primary sources

| result | value | primary source |
|---|---|---|
| 2×2 matrix, entries U[−1,1]: P(real eigenvalues) | 49/72 | Hetzel–Liew–Morrison, *Amer. Math. Monthly* 114 (2007) 491–499 — **read in full**; Thm 3.1 + Remark 3.2(a); also quoted by Martin–Wong arXiv:0808.1922 |
| n×n Gaussian: P(all eigenvalues real) | 2^(−n(n−1)/4) | Edelman, *J. Multivariate Anal.* 60 (1997) 203–232 — preprint read in full |
| full quadratic, iid U(0,1): P(real roots) | (5+6ln2)/36 ≈ 0.2544134190 | derivation verified; decimal traces to J. D'Aurizio (Math.SE), cited by Haldar–Chakraborty 2021 (DOI 10.26855/jamc.2021.03.006) |
| full quadratic, iid U(−θ,θ) | 41/72 + ln2/12 ≈ 0.6272 | Limmer 1999 (OSU thesis, pp. 19–21, primary derivation); Haldar–Chakraborty 2021 abstract ("62.7%") |
| depressed cubic (p,q) ~ U[−1,1]²: P(3 real) | 2√3/45 = 0.076980 | **folklore** — no published source or named originator found despite exhaustive search; independently verified (exact + MC) by two sweep agents and this project |
| Kostlan (elliptic) ensemble, n=3: P(all real) | (√3−1)/2 ≈ 0.36603 | MSE 1745310 (exact, ensemble-specific); sweep MC 0.36606 ± 0.00015 agrees |

Adjacent quadratic literature (all degree-2 only): Boucher, *Math. Gazette* 105
(2021) 410–415 (paywalled); Haldar–Chakraborty, *J. Appl. Math. Comput.* 5(1)
(2021); JISPS 2023 (DOI 10.1007/s41096-023-00149-6, U(α,β) generalization,
paywalled).

## 3. State of the art by degree (uniform-type coefficients)

- **Degree 2**: exact, published (§2).
- **Degree 3, monic on cube**: **this project** (383/4860 + ln3/48 and 1/2880) —
  previously nothing, not even a numeric.
- **Degree 3, non-monic** ax³+bx²+cx+d iid U[−1,1]: **SOLVED** — Theorem 3,
  **P = 641/2430 − ln(3)/24 = 0.21801049620261477109…**, proved 2026-08-17 via
  a cone/divergence-theorem reduction to Theorem 1 plus one new 3D volume (see
  THEOREMS.md, VERDICT.md). This is the value the dxdy.ru thread (June 2026)
  had already guessed; the derivation and its independent 19-digit numerical
  confirmation are new. Published numerics were wrong (0.2219 Purdue 2012 at
  132σ; 0.21829 MSE 1745310 at 9σ) — and so, it turned out, was this project's
  own literature-sweep quadrature (0.217993225 ± 5e-8, refuted by +1.7271e-5,
  ~345× its claimed error bar; post-mortem in VERDICT.md).
- **Degree 3, Gaussian**: non-monic N(0,1): 0.246373 ± 0.000134 (sweep MC;
  Limmer 1999 gives 0.246380 by quadrature — consistent; notably NOT 1/4).
  Monic N(0,1): **0.169962 ± 4.2e-5 (our MC)** — nobody has this.
- **Degree 4**: only Li 1988 (unrecovered) claims exact values. Sign
  characterization (Δ>0 ∧ P<0 ∧ D<0 for 4 real roots) confirmed via Wikipedia
  "Quartic function" + empirical validation. Sweep MC values (2×10⁸ each):
  non-monic U(−1,1)⁵: 0.0388489 ± 2.7e-5; N(0,1)⁵: 0.0519824 ± 3.1e-5;
  U(0,1)⁵: 0.0003177 ± 2.5e-6; monic N(0,1)⁴: 0.0217464 ± 2.0e-5;
  monic U(−1,1)⁴: 0.0054562 ± 1.0e-5 (our engine: 0.0054749 ± 9.0e-6, ~1.4σ,
  consistent). Methodological precedent for rigorous bounds:
  Bhargava–Cremona–Fisher (arXiv:2004.12085) certified a quartic sign-condition
  volume to width 1.7e-4 by interval subdivision.
- **Degree 3 lattice analog**: Yatsyna–Žmija (arXiv:2509.14501, 2025) count monic
  integer cubics with all-positive real roots: #P₃⁺(A) = A⁵/480 + O(A³) — their
  leading constant 1/480 is exactly our Theorem 2 inner integrand a⁵/480. Strong
  independent corroboration of the geometry (they count lattice points in the same
  region; they do not state the volume/probability).
- **Degree n asymptotics**: P(no real root) for Kac polynomials decays as
  n^(−3/4) — the persistence exponent is EXACTLY b = 3/4 (Poplavskyi–Schehr, PRL
  121:150601, 2018, via truncated real orthogonal ensemble; earlier DPSZ 2002:
  b = 0.76 ± 0.03, rigorous 0.4 ≤ b ≤ 2). P(all n roots real) is governed by
  speed-n² large deviations (Zeitouni–Zelditch arXiv:0904.4271; Butez EJP 2016);
  no closed-form rate constant known for Kac/uniform — genuinely open.

## 4. The parent matrix problem (bridge kept warm)

- The canonical question is **MSE 3770846** (Exodd, 2020-07-27), score 153,
  **zero answers** as of 2026-08-17. All partial results live in comments.
- leonbloy's simulated values (U[0,1] entries): n=3: 0.708, n=4: 0.346, n=5: 0.117,
  n=6: 0.028 (our engine: 0.70755 ± 1.4e-4 at n=3, consistent).
- **The striking empirical pattern** (leonbloy, comment score 42; also MO 372115):
  P_n(uniform[0,1]) ≈ Q_(n−1) where Q_n = 2^(−n(n−1)/4) is Edelman's Gaussian
  probability: 0.708 vs 0.70711; 0.346 vs 0.35355; 0.117 vs 0.125; 0.028 vs
  0.03125. Unexplained; no theorem. (A U[0,1] matrix = (all-ones matrix)/2 +
  uniform-centered noise — the rank-one shift plausibly "uses up" one dimension;
  nobody has made this precise.)
- Universality literature (Tao–Vu real eigenvalues etc.) covers expected COUNTS,
  not the all-real probability. Stanford UQ Project catalogs the n≥3 uniform case
  as unsolved (question 260).

## 5. Methods toolbox (for the harder open targets)

- **Moment-SOS volume hierarchies**: Henrion–Lasserre–Savorgnan, SIAM Review 51(4)
  (2009); convergence ≥ O(1/log log d) (Korda–Henrion arXiv:1612.04146); Stokes
  constraints eliminate the Gibbs phenomenon (Tacchi–Lasserre–Henrion
  arXiv:2009.12139, DCG 2023); sparsity exploitation (arXiv:1902.02976). Software:
  GloptiPoly 3, SumOfSquares.jl, TSSOS.
- **CAD / exact integration**: Mathematica `CylindricalDecomposition` +
  `Integrate` over `ImplicitRegion` can do exact discriminant-region volumes;
  QEPCAD B decomposes but does not integrate. Direct methodological template:
  Dahlqvist–Bandukara–Omidvari, "Exact Evaluation of Probabilistic Programs with
  CAD" (arXiv:2606.24514, 2026).
- **Certified interval subdivision**: Bhargava–Cremona–Fisher's recursive
  subdivision (above) is the model for rigorous quartic bounds; Arb/python-flint
  or IntervalArithmetic.jl for implementation.
- **Constant recognition**: mpmath.identify / PSLQ — worked here (the quadrature
  hitting the "upper bound" to 16 digits was the tell that clipping never occurs).

## 6. Errata to the research memo (better-research-targets doc)

1. Depressed-cubic decimal: 2√3/45 = **0.076980**, not 0.0684267 (closed form was
   right). Origin of 0.0684 unknown.
2. "Monic cubic simulated ≈0.08–0.09": wrong; true value 0.101694… (our Theorem 1).
3. "Persistence exponent ≈0.7639 with no closed form": outdated/garbled — the
   exact value **b = 3/4** was proven by Poplavskyi–Schehr (2018). The memo's
   "θ(2) ≈ 0.1875" is exactly 3/16.
4. The memo's implied reliability of published cubic numerics: both published
   non-monic values (0.2219, 0.21829) are wrong.

## 7. Ranked next targets

*(The non-monic cubic — formerly item 1 here — was settled 2026-08-17: Theorem 3,
P = 641/2430 − ln(3)/24, proved via a cone/divergence-theorem reduction. See §1
and §3 above, and THEOREMS.md / VERDICT.md for the full derivation.)*

1. **Li (1988) retrieval** (ILL / T&F): now the decisive remaining novelty
   document — its cubic family x³+3ax²+3bx+2c with symmetric uniform
   coefficients contains our Theorem 1 model at h=k=1/3, l=1/2; possibly also
   hands us the quartic answer.
2. **Monic quartic U[−1,1]⁴** (0.005475 ± 9e-6): **correction, 2026-08-18** —
   the cone/divergence-theorem trick does *not* apply directly here as
   previously suggested. It needs homogeneity across *all* coefficients
   scaled together, including the leading one; fixing the leading coefficient
   at 1 (the monic case) breaks that. The quartic discriminant is homogeneous
   of degree 6 in the *five* coefficients a,b,c,d,e, so the trick correctly
   targets the *non-monic* quartic (2×5=10 faces, not 2×4=8) — and even there
   one of the resulting face volumes *is* the monic quartic probability, so
   that route needs this problem solved first as an input, not the other way
   around. Attack the monic case directly instead, by genuine generalization
   of the Theorem 1/2 band method (complicated by a quartic's derivative
   being itself a cubic, with up to three real critical points rather than
   one band); if that doesn't reduce cleanly, Bhargava-style certified
   interval bounds. **Active investigation**: see `../open-problems/`.
3. **Monic cubic Gaussian** (0.169962 ± 4.2e-5): different geometry (no cube), needs
   Gaussian measure of the band — 2D integral of Φ-differences; PSLQ candidates
   after high-precision quadrature. **Active investigation**: see
   `../open-problems/` — a root-space reparametrization already reaches 12
   digits (0.169929382623…), pending constant recognition.
4. **Write-up**: three theorems (two genuinely new values, one new proof of a
   forum-guessed value that retracts a wrong published-here quadrature) plus the
   folklore-status depressed anchor make a self-contained note (arXiv math.PR);
   include the Yatsyna–Žmija 1/480 connection and the cone-reduction technique,
   which looks reusable beyond this specific family.
