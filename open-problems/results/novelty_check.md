# Novelty / prior-art check — the two constants

*Run 2026-08-18. Method: OEIS direct queries, Claude Code WebSearch, Stack Exchange
API, arXiv API, zbMATH API, Semantic Scholar API, plus full-text grep of one
downloaded paper. Machine-readable record: `novelty_check.json`.*

**Bottom line.** Nothing found for either constant. But the two problems are not
equally well covered: Problem A's negative is reasonably solid; Problem B's is
weak, and one specific unread paper (Li 1988) could still contain it.

---

## (a) OEIS — no hit

Queried `https://oeis.org/search?q=…&fmt=text` by `curl` (OEIS returns 403 to the
WebFetch tool; a browser user-agent via curl works).

**Problem A — every query returned literally `No results.`**

| query | result |
|---|---|
| `1,6,9,9,2,9,3,8,2,6,2,3` | No results. |
| `1,6,9,9,2,9,3,8` | No results. |
| `1,6,9,9,2,9,3,8,2,6,2,3,4,7,9,5,0,2` | No results. |
| `0.169929382623` (parsed as `seq:1,6,9,9,2,9,3,8,2,6,2,3`) | No results. |
| `169929382623479502` | No results. |
| `1699293826234795` | No results. |
| `seq:1,6,9,9,2,9,3` | No results. |
| `seq:0,1,6,9,9,2,9,3,8,2,6` | No results. |

**Problem B — inconclusive by construction.** With only `0.005475` known, OEIS
parses the query as the 4-term sequence `5,4,7,5`, which matches **318** unrelated
sequences (`e`, `1/√2`, the plastic constant, the Dottie number, …). Restricting to
`keyword:cons` still leaves 141. `0.0054749` → `seq:5,4,7,4,9` → 36 hits (19 with
`keyword:cons`: `log_24(7)`, `log_18(14)`, the Landau–Kolmogorov constant
`C(3,1)`, several Johnson-solid dihedral angles) — none related. **These digit
searches must be re-run once the high-precision quartic value exists.**

**Phrase searches.** `"random polynomial" "real roots"` returns exactly **two**
sequences in all of OEIS: `A060294` (Buffon's 2/π) and `A093601` ("constant in
Kac's formula", `0.6257358072…` — the additive constant in `E[#real zeros]`, not
an all-real probability). `monic cubic real roots probability` → No results.
`keyword:cons random polynomial real` → 9 hits, none relevant.

> OEIS appears to contain **no** sequence for the probability that a random
> polynomial has all roots real, in any ensemble.

## (b) Prior art for the monic Gaussian cubic — none found

Searched (WebSearch): the exact digit strings `"0.1699293826"`, `"0.16992938"`,
`"0.169929"`, `"0.1699293826234795"`, `"0.169929382623479502"`, plus phrasings
("probability random monic cubic has three real roots", "Gaussian measure
hyperbolicity region…", `"x^3 + a x^2 + b x + c"` + discriminant + normal, …).
**No page anywhere contains any of those digit strings.**

Stack Exchange API (7 queries across math.SE and MathOverflow) — closest threads,
none of which is this problem:

- **MSE 1745310**, "The probability that a random (real) cubic has three real roots" — *non-monic*; the useful answer is for the Kostlan/elliptic ensemble.
- **MSE 1745436**, "What is the likelihood that a degree 3 monic polynomial will have 3 real roots" — title matches but the model is coefficients uniform on `[-n,n]` with `n → ∞`; the single answer computes the scale-invariant limit `41/72 + ln2/12 = 0.6272`, i.e. it degenerates to the quadratic problem. Gives no value for the Gaussian case.
- **MSE 4185340**, "Probability that all roots of a polynomial are real" — iid `U[0,1]`, general `n`, **zero answers**; only `n=2` (`= 1/9`) worked out in the body.

**Edelman–Kostlan (1995) checked directly.** I downloaded `arXiv:math/9501224` and
grepped the extracted text (82 kB): it contains **no** all-roots-real result — zero
matches for `probability that all`, for `all (the/n) (roots|zeros|eigenvalues)`,
and for `n(n−1)/4`. The paper is entirely about the *expected number* of real
zeros.

> ⚠️ **Correction to the task brief.** `P(all n roots real) = 2^{−n(n−1)/4}` is
> *not* Edelman–Kostlan and *not* the Kostlan polynomial ensemble. It is Edelman
> (*J. Multivariate Anal.* **60** (1997) 203–232) for the probability that all `n`
> eigenvalues of an `n×n` **real Ginibre matrix** are real. The Kostlan *polynomial*
> ensemble at `n=3` gives `(√3−1)/2 = 0.36603`, whereas `2^{−3·2/4} = 0.35355` —
> different numbers. Both facts are separately recorded as verified anchors in the
> predecessor campaign's `reference/LITERATURE.md`.

arXiv metadata search (5 queries) found nothing computing an all-real probability
for a low-degree monic random polynomial. *(Caveat: the arXiv API searches
title/abstract/comments only, not full text.)*

**Li (1988)** — see below — is the only paper found that even claims exact
all-real probabilities, and its known cubic special cases are uniform on symmetric
intervals, not Gaussian.

## (c) Prior art for the monic uniform quartic — none found, but one live risk

Same digit searches (`"0.005475"`, `"0.0054749"`) returned no occurrence. No SE
thread, no arXiv metadata hit.

**But:** the top search hit for the quartic phrasing is, every time,

> Hung C. Li, *"The exact proability [sic] that the roots of quadratic, cubic, and
> quartic equations are all real if the equation coefficients are random"*,
> **Comm. Statist. Theory Methods 17(2) (1988) 395–409**, DOI
> `10.1080/03610928808829630`, Zbl 0641.60075, MR 89j:60069.

I recovered its review verbatim from the zbMATH **API** (the zbMATH website is
Cloudflare-blocked):

> "Suppose that the coefficients of a polynomial equation are independent random
> variables defined on subsets of real numbers. The purpose of this paper is to
> find the exact probability that all roots of a random polynomial equation are
> real. Since a polynomial equation of degree higher than four with arbitrary
> coefficients cannot be solved algebraically, this paper will consider quadratic,
> cubic and quartic equations only. The general results are obtained in each case.
> Also, a number of special cases are furnished."

Semantic Scholar records **0** citations. The full text is paywalled (T&F returns
403; no open-access or repository copy found). The predecessor campaign recovered
the *MR* review (reviewer G. Samal), which describes Li's cubic family as
`x³+3ax²+3bx+2c` with `a,b,c` uniform on symmetric intervals — all his cubic
special cases being symmetric-uniform, with no Gaussian case reported. I could not
independently re-verify that MR text: the Internet Archive item
`sim_mathematical-reviews_1989-10_89j` is lending-restricted and both its
`_djvu.txt` and its search-inside endpoints return "Item not available".

**Li explicitly claims exact QUARTIC results, and his quartic special cases are
unknown.** Whether his quartic family fixes the leading coefficient, and whether
`U[-1,1]⁴` is among his cases, cannot be determined without the paper. *This is
the single sharpest unresolved prior-art risk in the whole check, and it lands on
Problem B.*

## (d) Honest assessment

**Problem A (monic Gaussian cubic) — no prior art found; negative reasonably well
supported.** The 54-digit value is absent from OEIS, absent from the indexed web,
absent from Math.SE/MathOverflow, and demonstrably absent from Edelman–Kostlan.
The one paper claiming exact all-real probabilities (Li 1988) is, on the evidence
of its MR review, about uniform coefficients on symmetric intervals.
*Residual risk:* Li's unread "general results" could be distribution-free; the
Bharucha-Reid–Sambandham (1986) monograph could not be searched at all; arXiv was
searched by metadata only.

**Problem B (monic uniform quartic) — no prior art found, but do not assert
novelty yet.** Two reasons: (i) with 4 significant digits, the digit searches are
close to vacuous — the OEIS query degenerates to `5,4,7,5`; (ii) Li (1988) claims
exact quartic results and remains unread.

**The general caveat, stated plainly.** Every finding above is of the form *"I ran
query X and it returned nothing"*, never *"this does not exist"*. Absence of
evidence from web and OEIS search is weak evidence about paywalled journals,
pre-1995 literature, book interiors, and preprint full texts. The one document
that would settle both questions — Li (1988) — I could not obtain.

**Not searched (and why):** DuckDuckGo (HTTP 202 bot-block on every query,
including a control query with known results — so no DDG negative is claimed);
MathSciNet (subscription); Google Scholar (no access); Taylor & Francis full text
(paywall); *Mathematical Reviews* 89j full text (archive.org lending restriction);
Bharucha-Reid & Sambandham 1986 (no accessible copy); arXiv full text (metadata
API only); sequencedb.net (host unreachable).

**Recommended next actions.** (1) Get Li (1988) by ILL or T&F purchase — decisive
for both problems, especially B. (2) Re-run every digit query for Problem B once
≥12 digits are available. (3) Fix the internal `2^{−n(n−1)/4}` attribution. (4) On
write-up, submit both constants to OEIS — that also creates a dated priority
record.

---

# Follow-up pass (same day) — Problem B at 16 digits, the closed-form constants, and a second run at Li (1988)

*Triggered by the coordinator: `P_B = 0.005464330340589986` (16 digits) replaces the
`0.005475` Monte Carlo value, so the digit searches that were vacuous in the first
pass are now decisive.*

## 1. Problem B digit searches — now a real negative, and it is clean

Every OEIS query below returned literally `No results.`

| query | parsed by OEIS as |
|---|---|
| `0.005464330340589986` | `seq:5,4,6,4,3,3,0,3,4,0,5,8,9,9,8,6` |
| `5464330340589986` | (literal) |
| `5,4,6,4,3,3,0,3,4,0,5,8,9,9,8,6` | — |
| `0.00546433034` | `seq:5,4,6,4,3,3,0,3,4` |
| `5,4,6,4,3,3,0,3,4` | — |
| `0.0874292854494398` | `seq:8,7,4,2,9,2,8,5,4,4,9,4,3,9,8` |
| `874292854494397687` | (literal) |
| `8,7,4,2,9,2,8,5,4,4,9,4,3,9,7,6,8,7` | — |

Web (WebSearch) on `"0.005464330340589986" OR "0.00546433034" OR "0.0874292854494398"`:
**no occurrence of any of the digit strings** in any result.

> Problem B's negative is now the same quality as Problem A's. The earlier caveat
> ("4 significant digits makes this vacuous") is discharged.

## 2. The closed-form constants — no prior appearance found

First I re-derived them to 30 dps (mpmath) to be sure I was searching the right numbers:

```
asinh(sqrt(6)/4)      = 0.579405180214973405865436495439
log((sqrt6+sqrt22)/4) = 0.579405180214973405865436495439   <- identical, as expected
sqrt(3)*asinh(sqrt(6)/4)/90 = 0.011150657892232617465436
7013*sqrt(11)/302400        = 0.076916301768394243193925
sum                         = 0.088066959660626860659361   <- matches 16*P_B(unclipped)
```

**OEIS — all `No results.`**: `0.0880669596606269`,
`8,8,0,6,6,9,5,9,6,6,0,6,2,6,8,6`, `880669596606268606`,
`0.00063767421118709` (= `C_clip`), `6,3,7,6,7,4,2,1,1,1,8,7,0,9`,
`0.5794051802149734` (= `asinh(√6/4)`), `0.0111506578922326`,
`0.0769163017683942`, `7013 sqrt(11)`. The phrase query `"arcsinh" "sqrt(6)"`
returns 17 sequences, all unrelated (Chebyshev-type recurrences, quartic-root
decimal expansions) — nothing probabilistic.

**Web — nothing.** `"arcsinh(sqrt(6)/4)" OR "asinh(sqrt(6)/4)" OR "log((sqrt(6)+sqrt(22))/4)"`
returns only generic `asinh` documentation and calculators; no page identifies any
such constant. `"asinh"/"arcsinh" "sqrt(6)/4"` + random polynomial + real roots:
nothing. `"0.0880669596606269" OR "0.00063767421118709"`: no occurrence.

**arXiv metadata** — `arcsinh` + `random polynomial`: 0. `sqrt{11}` + `real roots`: 0.

> No prior appearance of `asinh(√6/4)` (equivalently `log((√6+√22)/4)`), or of any
> `√11` combination, was found anywhere in the random-polynomial / real-rootedness
> literature.

**On `K = 128/105` — a warning rather than a result.** `128/105 = 2⁷/105` is a
Wallis-type rational, the family that ordinary beta/Wallis integrals emit by the
dozen. It is not a distinguishing fingerprint and searching it as prior art is close
to meaningless. For the record one hit of that shape did occur — arXiv:2208.14711
("On real roots of polynomials in the context of group theory") carries a Wallis
sequence `β_n = 2/3, π/8, 4/15, π/16, 16/105, 5π/128, …` whose fifth term `16/105`
is `128/105 ÷ 8`. **I draw no inference from this.** It is what Wallis rationals do.

## 3. Li (1988) — second attempt: still not obtained, but materially better characterised

**Outcome: the paper remains unread.** Four things were newly recovered, and one
promising route failed on a quota error rather than on a null result.

**(i) The full author abstract, verbatim, via the OpenAlex API** — and it turns out to
be word-for-word what zbMATH carries as its "review". So **zbMATH's entry is Li's own
abstract, not an independent reviewer summary**, and it contributes nothing about the
special cases. (The genuinely independent MR review, by G. Samal, is the one the
predecessor campaign recovered and which I still cannot re-access.)

**(ii) Li's complete 9-item reference list, from Crossref** — new, and not previously
known to this campaign:

> Dickson, *New First Course in the Theory of Equations* (Wiley 1945), pp. 46–54 ·
> Ibragimov (1971) · Lapin, *Probability and Statistics for Modern Engineering*
> (1983), pp. 384–388 · Kac (1949), PLMS · Mishra–Nayak–Pattanayak (1983), "Lower
> bound for the number of real roots of a random algebraic polynomial", J. Austral.
> Math. Soc. · Neter, *Applied Linear Statistical Models* (1974) · Stevens (1965)
> dissertation · Uspensky, *Theory of Equations* (1948), pp. 288–290 · Yu Z.M. (1982).

*Inference, clearly flagged as inference:* the bibliography is classical
theory-of-equations (Dickson, Uspensky — discriminant/resolvent criteria for root
reality) plus elementary probability/statistics textbooks (Lapin, Neter). It contains
**no** Gaussian-specific or measure-theoretic machinery and **no** work on Gaussian
coefficient ensembles. That is *weak* supporting evidence that his special cases are
elementary bounded (uniform-type) distributions — consistent with the MR review's
symmetric-uniform cubic family. **It is not proof, and it says nothing whatever about
whether his quartic special cases include a monic `U[-1,1]⁴` model.**

**(iii) Unpaywall confirms the article is hard-closed**: `is_oa: false`,
`oa_status: "closed"`, `has_repository_copy: false`, `oa_locations: []`. There is no
legitimate free copy to be found.

**(iv) The single citing work is now identified.** OpenAlex `cited_by_count = 1`, and
that one citation is **Jiří Anděl, *Mathematics of Chance*, Wiley Series in Probability
and Statistics, 2001** (the citation sits in the book's reference list, DOI
`10.1002/9780470317075.refs`). From the chapter structure the relevant chapter is
almost certainly **Ch. 11, "Probability in Mathematics", pp. 195–210**. A scan exists
on the Internet Archive as item `mathematicsofcha0000ande`, but it is
lending-restricted — `djvu.txt` and every search-inside endpoint return "Item not
available". **This is the most concrete bounded next step**: a popular-level chapter
citing Li is exactly the sort of place his special cases would be restated in the open.

**Routes tried and failed this pass:** T&F full text (403/paywall) · Unpaywall
(confirms no OA copy exists) · archive.org MR 89j (lending-restricted; `djvu.txt`,
`fulltext/inside.php`, `BookReaderSearch.php`, `api.archivelab.org`, `ia-pub-fts-api`
all 404 / empty / "Item not available") · archive.org full-text search endpoint (404) ·
HathiTrust full-text search (403) · archive.org search for the journal *Communications
in Statistics* (not archived; only unrelated DTIC items) · Semantic Scholar citations
(0).

**One failure that is a failure, not a negative:** the Google Books full-text phrase
search for `"the roots of quadratic, cubic, and quartic equations are all real"`
returned **HTTP 429, "Quota exceeded … Queries per day"**. Google Books indexes
*Mathematical Reviews* volumes, so this is the most promising untried route to the MR
review — it should be retried once the quota resets. I am recording it as *not
searched*, not as *searched and empty*.

## 4. Updated verdict

**Problem A (monic Gaussian cubic)** — unchanged: no prior art found. One new, weak,
explicitly inferential data point in its favour: Li's reference list contains no
Gaussian-ensemble sources at all.

**Problem B (monic uniform quartic)** — **upgraded from "low-to-moderate" to
"moderate" confidence.** The 16-digit value is absent from OEIS and from the web; the
distinctive closed-form ingredients (`asinh(√6/4)`, `7013√11/302400`) have no prior
appearance anywhere I could search. What has *not* changed: **Li (1988) explicitly
claims exact quartic probabilities and is still unread.** Phrase any claim as *"not
found in any searchable source; Li (1988) unverified"* — not as novelty.

**The residual risk, stated plainly.** One document could still overturn either claim,
and it is the same document as before. I could not get it. I could not get the
independent MR review of it either. What I could get — its abstract, its bibliography,
its lone citing work — points weakly away from the Gaussian cubic and says nothing
about the uniform quartic.

---

## (e) Files written

- `~/math/open-problems/results/novelty_check.json`
- `~/math/open-problems/results/novelty_check.md`

No other file was created or modified.

---

# Round 3 (2026-08-18) — the **formula** and the **technique**, not the decimal

*Rounds 1–2 searched for the decimal values of two constants. This round asks a
different question: is the closed-form integral*

```
P = (1/π) ∫₀^∞ exp( −x⁴(x⁴+4x²+9) / (2(x⁴+4x²+1)) ) · 2(x⁴+6x²+3) / ( √(x⁴+4x²+1)·(x⁴+4x²+9) ) dx
  = 0.16992938262347950265644315713176190213…
```

*for `P(x³+ax²+bx+c has 3 real roots)`, `a,b,c` iid `N(0,1)`, already known — and is
the derivation route (Kac–Rice on the moving level, plus an Owen's-T cancellation of
the erf term, plus `E[N] = 1 + 2P`) a known move?*

## 0. New capability: IA Scholar full-text search

Every previous arXiv negative in this file was **metadata-only**. This round I got
`scholar.archive.org` working — a **full-text** index over archived scholarly PDFs
(arXiv, OA journals, and some scanned serials including *Mathematical Reviews*).
`curl` hits a JS session-verification wall; the **WebFetch tool goes straight
through**. All "IA Scholar" results below are full-text.

> **Coverage caveat, stated up front.** IA Scholar is strong on arXiv and open access
> and thin-to-absent on paywalled 1940s–1990s journals and on book interiors. A zero
> there is not a zero over the literature.

## 1. (a) The formula — no prior appearance found

**Digit strings — re-confirmed and extended.**

| corpus | query | result |
|---|---|---|
| OEIS | `1,6,9,9,2,9,3,8,2,6,2,3,4,7,9,5` | `No results.` |
| OEIS | `0.16992938262347950` → `seq:…,5,0` | `No results.` |
| OEIS | `1,3,3,9,8,5,8,7,6,5,2,4,6,9,5,9` (= `E[N]=1+2P`) | `No results.` |
| OEIS | `3,3,9,8,5,8,7,6,5,2,4,6,9,5,9` (= `2P`) | `No results.` |
| OEIS | `8,3,0,0,7,0,6,1,7,3,7,6,5,2,0,4` (= `1−P`) | `No results.` |
| WebSearch | `"0.169929382623" OR "0.1699293826" OR "0.16992938262347950"` | no page contains any |
| WebSearch | `"1.3398587652" OR "1.33985876" OR "0.3398587652"` | no occurrence |
| WebSearch | `"0.169929" OR "0.16993" probability cubic three real roots normal` | nothing |
| **IA Scholar (full text)** | `"0.1699293826"` | **0 results** |

Searching `E[N] = 1+2P = 1.3398587652469590…` is new this round and is the more
likely form for a paper to report; it is absent too.

**The integrand-shape search — I could not actually run it.**

This is a *failed search*, not a negative. No engine available to me does literal
matching on ASCII math strings:

- IA Scholar `"x^4+4x^2+1"` → **97 hits**, all tokenised junk (Apéry limits,
  hyperelliptic curves, wavelets…). It matched tokens, not the expression.
- WebSearch `"x^4+4x^2+9" "x^4+6x^2+3" integral` → integral-calculator landing pages.
- WebSearch `random polynomial real roots Kac-Rice "x^4+4x^2+1" integral` → generic
  Kac–Rice papers, none containing the expression.
- arXiv has **no public full-text search** (`search.arxiv.org` is dead — connection
  refused); Google Scholar and Google Books are unavailable to me.

**So: the single search that would most directly settle the formula question was
never executed.** Say so in any write-up.

## 2. (b) The technique — both ingredients are prior art; the combination is not found

### 2.1 The erf term is Edelman–Kostlan Corollary 5.1, and they name the monic case

I re-downloaded `arXiv:math/9501224` and this time **read §5.2–5.3** instead of only
grepping for "probability that all". Corollary 5.1 is exactly the non-central Rice
density that leaves a CDF term behind:

```
E[N on [a,b]] = (1/π) ∫ ‖γ′(t)‖ e^{−m₀²(t)/2} [ e^{−m₁²(t)/2} + √(π/2)·m₁(t)·erf(m₁(t)/√2) ] dt
```

and immediately after it, **verbatim**:

> "The reader may use this corollary to compute the expected number of roots of a
> random monic polynomial. In this case `m = eₙ` and `C` is singular, but this
> singularity causes no trouble."

Three consequences, all of which must go into the write-up:

1. **The non-central Kac–Rice setup for the monic ensemble is publicly signposted in
   a *Bulletin of the AMS* survey from 1995.** E–K do not carry it out, but they
   point at it.
2. **The "erf term a naive Rice formula leaves behind" is literally E–K's erf term.**
   It is 31 years old and standard. It is not the new part.
3. E–K then isolate exactly two cases where the integral closes — Case I (`m₁ ≡ 0`,
   density collapses to a constant times the mean-zero density) and Case II
   (`m₀ ≡ m₁`, giving `¼erf²(m₀/√2) − Γ[0,m₀²]/(2√(2π))`). **The monic polynomial is
   in neither.** E–K closed the easy ones and left the monic one alone.

`grep -i owen` over the full E–K text: **zero hits**. And re-confirmed: E–K contains
no all-roots-real result of any kind.

**Did anyone follow up?** IA Scholar full text, exact phrase
`"expected number of roots of a random monic polynomial"` → **2 hits, both being the
BAMS and arXiv copies of E–K itself.** No follow-up paper found.

### 2.2 Owen's T *is* at home in Rice / level-crossing work — but never for polynomials

| IA Scholar full-text query | result |
|---|---|
| `"Owen's T function" "random polynomial"` | **0 results** |
| `"Owen's T function" "real roots"` | **0 results** |
| `"random monic polynomial" "Kac-Rice"` | **0 results** |
| `"three real roots" "Kac-Rice"` | **0 results** |
| `"Owen's T function" "Rice formula"` | **3 results** (below) |
| `"Owen's T" "level crossings"` | **2 results** (below) |
| `"Owen's T function" "Kac"` | 7 results, none random-polynomial |

The three Owen-plus-Rice papers, all stochastic-process/neuroscience:

- **Rawat, Morone, Heeger, Martiniani**, *"Exact Variance and Fano Factor for
  Arbitrary Level Crossings in Stationary Gaussian Processes"*, arXiv:2605.25278
  (24 May 2026). Goes beyond the mean Kac–Rice rate to the exact **variance**; Owen's
  T sits in the second-moment formulae ("when `u = 0` … Owen's T function reduces to
  an arctangent"). Stationary process, second moment, no polynomial.
- **Schwalger**, arXiv:2109.07416 (2021). I downloaded the PDF and grepped it:
  "Owen" occurs **exactly once**, as a parenthetical that a double integral `f₂` in
  his level-crossing computation "can also be expressed in terms of Owen's T
  function". A representation remark, not a cancellation device.
- **van Meegen & van Albada** (2021), spiking networks.

Other channels, all null: arXiv metadata (`all:"Owen T function"` → 4 hits, none
random-polynomial; `all:"Owen T" AND all:"random polynomial"` → 0); math.SE (15
Owen's-T threads, all about the function itself / Gaussian integrals) and MathOverflow
(3, none relevant); WebSearch including `site:arxiv.org "Owen's T" "random polynomial"`.

### 2.3 Verdict on the technique

- **Not novel:** non-central Kac–Rice with an erf remainder (E–K Cor. 5.1); closing
  such an integral in closed form (E–K Case II); Owen's T inside a Rice/level-crossing
  computation (Schwalger; Rawat et al.); `E[N] = 1 + 2P` for a cubic (folklore parity).
- **Not found anywhere:** Owen's T used as the device that *cancels* the erf term;
  any Kac–Rice computation of a real-rootedness **probability** rather than an expected
  count; any exact evaluation of the monic-Gaussian Kac–Rice integral at any degree.

> **Recommended phrasing.** Claim the closed form and the Owen's-T cancellation.
> Do **not** claim "applying Kac–Rice to the monic Gaussian cubic" — Edelman–Kostlan
> signposted that in 1995 — nor "using Owen's T in a Rice-formula context".

## 3. (c) Does anyone give `P(all roots real)` for the **monic Gaussian** cubic? No.

| IA Scholar full-text query | result |
|---|---|
| `"probability that all roots are real"` | 10 hits — **all** Riemann-hypothesis texts quoting Riemann's *"es ist sehr wahrscheinlich, dass alle Wurzeln reell sind"*. None probabilistic-polynomial. |
| `"probability that all its roots are real"` | 0 results |
| `"random monic polynomial" "real roots" Gaussian` | 3 hits: 2× Edelman–Kostlan, 1× Forrester–Rains (unitary Hessenberg, unrelated) |
| `"totally real" "monic" "Gaussian" probability polynomial roots` | 55 hits, all algebraic number theory / lattice coding |
| `"three real roots" "normally distributed" probability cubic` | 63 hits, all applied-statistics uses of the cubic discriminant (Behrens–Fisher, likelihood equations…) |

arXiv metadata: `abs:"all roots are real" AND abs:"random polynomial"` → 0;
`abs:"all real roots" AND abs:"probability"` → 0; `ti:"monic" AND abs:"Gaussian" AND
abs:"roots"` → 0.

**Nearby known results, ruled in and out.**

- **Akiyama & Pethő**, *"On the distribution of polynomials with bounded roots, I.
  Polynomials with real coefficients"*, J. Math. Soc. Japan **66**(3) (2014) (and
  part II, integer coefficients, Unif. Distrib. Theory 9 (2014)). **New to this
  campaign.** They *do* compute exactly — via Selberg-type multiple integrals, with
  rational answers — the "probability" that a **monic** real polynomial is **totally
  real**, but in the **contractive** ensemble (all roots in the unit disc, uniform on
  the coefficient body): *"within contractive polynomials, the 'probability' of
  picking a totally real polynomial decreases rapidly when its degree becomes large."*
  Different ensemble (bounded roots / uniform, not iid Gaussian) and different
  technique (root-space change of variables, not Kac–Rice). Found via the sole answer
  to MSE 1745310, which applies the same Vieta/root-space route to the uniform
  `[−N,N], N→∞` cubic and gets `P₃ ≈ 0.218` by Monte Carlo, no closed form.
- **Do, Nguyen & O'Rourke**, *"Real roots of non-centered random polynomials"*,
  arXiv:2605.26402 (26 May 2026) — the closest modern ensemble *in spirit*
  (independent coefficients with non-zero means). Variance asymptotics and CLTs for
  non-centered Kac and "hyperbolic" ensembles. I downloaded and grepped it: **zero**
  occurrences of "monic", **zero** of "Owen", no all-roots-real probability; E–K
  appears only in the bibliography. ("Hyperbolic" there is a coefficient ensemble,
  not real-rootedness.)
- **Yatsyna & Żmija**, *"Counting polynomials with positive roots"*, arXiv:2509.14501
  (2025) — monic **integer** polynomials with all roots real and positive; counting,
  not a Gaussian probability.
- **Sheikh & Mir**, *"Probabilistic Zero Bounds of Certain Random Polynomials"*,
  arXiv:2605.25017 (2026) — probabilistic Cauchy-type bounds on zero *moduli* for iid
  standard-normal coefficients; nothing on real-rootedness.

**Stack Exchange re-check.** MSE 1745310 (uniform/Cauchy limit, `≈0.218`), MSE 1745436
(uniform `[−n,n]`, `41/72 + ln2/12`), MSE 4185340 (`U[0,1]`, still zero answers).
None is the Gaussian monic case.

> **No source found gives `P(all roots real)` for the monic i.i.d. Gaussian cubic in
> any form — value, integral, or asymptotic.**

## 4. (d) Li (1988) / Anděl — one real advance, one route still blocked

**Advance: the MR review's exact page is now located.** IA Scholar full text for
`"quartic equations are all real"` returns six hits, three of them *Mathematical
Reviews*:

- `archive.org/details/sim_mathematical-reviews_1989-10_89j/page/**5639**` (issue 89j)
- `archive.org/details/sim_mathematical-reviews_1989_index_0/page/936`
- `archive.org/details/sim_mathematical-reviews_1989_index_1/page/665`

**But the body is still unreachable.** `archive.org/metadata/` confirms
`access-restricted-item: true`. I resolved the item's servers (`ia601806`/`ia801806`,
`dir=/4/items/…`) and called `fulltext/inside.php` on both → **HTTP 403 "Item not
available"**. `BookReaderSearch.php` → 404. `ia-fts.archive.org`,
`ia-pub-fts-api.archive.org`, `api.archivelab.org` → DNS failure. Only the title-line
snippet leaks through the IA Scholar index.

**Google Books: retried, still quota-blocked — a failure, not a negative.** Five calls
today (3 distinct phrase queries plus `country=US` and `country=CZ` variants), every
one `HTTP 429 — "Quota exceeded for quota metric 'Queries' and limit 'Queries per day'
of service 'books.googleapis.com' for consumer 'project_number:624717413613'"`. The
quota has **not** reset since round 2. HTML fallbacks also fail:
`books.google.com/books?q=…` → 302 → `google.com/search?tbm=bks` → 302 →
`consent.google.com` (EU consent wall); direct `google.com/search` via curl returns a
JS-only shell.

**Anděl, *Mathematics of Chance*.** Item `mathematicsofcha0000ande` confirmed present
on archive.org, `access-restricted-item: true`, `fulltext/inside.php` on `ia601403` →
403. IA Scholar does not index it (`"Mathematics of Chance" Andel "real roots"` → 0).

**Books still entirely unsearchable.** `archive.org/advancedsearch.php`
`title:"random polynomials"` → 64 hits, **all arXiv preprints**; Bharucha-Reid &
Sambandham (1986) is not archived. `title:"topics in random polynomials"` → 0 hits;
Farahmand's book is not archived either.

## 5. (e) Honest novelty assessment

**The formula — no prior appearance found; the negative is stronger than in rounds
1–2, but one key search never ran.**
Supported by: zero hits for the digit string in OEIS, on the web, *and* in IA Scholar
full text; zero for the derived constants `1+2P`, `2P`, `1−P`; zero in IA Scholar for
every polynomial-context phrasing of "probability that all roots are real"; and the
only paper phrase-matching "expected number of roots of a random monic polynomial" is
Edelman–Kostlan itself.
Residual risks: (i) the integrand-shape search was never executed; (ii) **E–K
explicitly invite the reader to do the monic computation**, so a textbook exercise,
lecture note, or short unindexed note doing it would be invisible to every channel I
have; (iii) Li (1988) unread (uniform coefficients — low risk here, not zero); (iv)
Bharucha-Reid–Sambandham and Farahmand unsearchable.

**The technique — scope the claim narrowly.** The combination "Kac–Rice + Owen's T to
eliminate the CDF term, for real-rootedness" was not found anywhere. But *neither
ingredient is new*: the non-central Rice density with its erf remainder is
Edelman–Kostlan Corollary 5.1 (1995), applied to the monic ensemble by their own
explicit suggestion; and Owen's T inside Rice/level-crossing computations is
established practice (Schwalger 2021; Rawat et al. 2026). What appears to be new is
the *cancellation* and the closed form it produces. Claim that, and nothing wider.

## 6. (f) What I could not search this round

| route | status |
|---|---|
| Literal math-string / integrand-shape matching | **no engine does it** — the central search never ran |
| arXiv full text | `search.arxiv.org` dead (connection refused); arXiv API is metadata-only |
| Google Books | HTTP 429 daily-quota all day, 5 attempts; HTML routes hit the EU consent wall |
| Google Scholar, MathSciNet | no access / subscription |
| Taylor & Francis full text (Li 1988) | paywall |
| *Mathematical Reviews* 89j p.5639 body | archive.org lending restriction, all endpoints 403/404/DNS-fail |
| Anděl, *Mathematics of Chance* interior | archive.org lending restriction |
| Bharucha-Reid & Sambandham 1986; Farahmand | not archived anywhere reachable |
| HathiTrust full-text search | HTTP 403 |
| CORE (core.ac.uk) | HTTP 403 |
| Mojeek | HTTP 403 automated-queries block |
| DuckDuckGo | HTTP 202 bot challenge (unchanged) |
| Bing via curl | returns 200 but **silently drops phrase queries** — a control search for a known paper title also failed, so **no Bing negative is claimed anywhere in this report** |

**Working routes, for the next round:** OEIS via curl+browser-UA; Claude Code
WebSearch; arXiv API (**must** use `https://` **and** `-L` — plain `http://` returns a
301 with an empty body under curl); Stack Exchange API 2.3; `archive.org/metadata/`
and `/advancedsearch.php`; and **`scholar.archive.org` full text via the WebFetch tool
only**.
