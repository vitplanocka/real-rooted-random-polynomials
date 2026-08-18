# Literature / novelty check — P = 719/2880 − ln(2)/3

*Searched 2026-08-18, by me, for this project specifically. The sibling project's
`LITERATURE.md` covers the three symmetric-interval cells; this file covers only the
new one-sided constant.*

## Verdict

**No prior appearance of 719/2880 − ln(2)/3 (or of S = 479/960 − (2/3)ln 2) was
found.** Three caveats below are real and are not resolved by these searches.

## What was searched, and what came back

### 1. The exact constants

| query | where | result |
|---|---|---|
| `"719/2880"` | general web search | only phone numbers / area code 719 / unrelated |
| `"719/2880"`, `"0.0186037"`, `"479/960"` | math.stackexchange full-text **body** search (StackExchange API) | **0 hits each** |
| same three | mathoverflow full-text body search | **0 hits each** |
| `"1/2880"` (control) | math.stackexchange body search | 5 hits — so the index does match literal fractions; the zeros above are meaningful |
| digits of P `1,8,6,0,3,7,1,7,5,9,1,1,2,9` | OEIS | "No results" |
| digits of S `3,6,8,6,0,2,1,2,9,6,0,0,3,6` | OEIS | "No results" |
| digits of Theorem 3's value, and of the **published** quadratic constant (5+6ln2)/36 (controls) | OEIS | **also "No results"** |

The OEIS negative is therefore **weak evidence**: OEIS does not carry these
random-polynomial probabilities at all, not even ones that are in print. The
StackExchange negative is stronger, because the control query works.

### 2. The problem, by description

Searches for the random cubic with uniform coefficients on the unit interval
return (a) homework pages (Wyzant), (b) the general random-polynomial literature
(expected number of real roots, Kac/Edelman/Tao–Vu-style asymptotics, polynomial
growth of coefficients), none of which computes an exact one-sided uniform cubic
probability. arXiv abstract searches (`"random cubic"+"real roots"`,
`"three real roots"+probability`, `"real-rooted"+"random polynomial"+uniform`)
returned nothing on point. `arXiv:2509.14501` "Counting polynomials with positive
roots" sounds close but is about **monic integer** polynomials of fixed trace —
a lattice-counting problem, not this probability.

### 3. The one prior claim of exact random-cubic results — Li (1988)

Hung C. Li, *The exact probability that the roots of quadratic, cubic, and quartic
equations are all real if the equation coefficients are random*, Comm. Statist.
Theory Methods 17(2):395–409, DOI 10.1080/03610928808829630.

* Semantic Scholar has the record but the **abstract is elided by the publisher**,
  and it lists **citationCount 0**.
* tandfonline returns HTTP 403 to automated fetches, so I could not read the
  abstract or the paper.
* The only substantive evidence about its content remains the **MR review**
  (reviewer G. Samal) recovered by the sibling project, which states that Li's
  cubic is `x³ + 3ax² + 3bx + 2c` with a, b, c uniform on the **symmetric**
  intervals `[−h,h]`, `[−k,k]`, `[−l,l]`. The one-sided cube is not among his
  cases.

**UNVERIFIED (inherited, unchanged):** Li's paper itself is still unread.

### 4. The dxdy.ru thread (the only known informal prior work)

`https://dxdy.ru/topic162889.html` (June 2026), whose headline result is the
**symmetric** non-monic value 641/2430 − ln3/24. I fetched both the normal and the
`view=print` version. The forum renders every formula as an image, so a text search
of the page finds none of the constants — I can confirm the thread exists and is
about the symmetric problem, but **I cannot rule out a one-sided remark inside an
image** by this method. The sibling project read this thread in detail and recorded
only symmetric-case content.

### 5. The canonical Math.SE thread

`math.stackexchange.com/questions/1745310` "The probability that a random (real)
cubic has three real roots", read in full via the API: the question fixes
coefficients uniform on `[−R,R]` and takes `R → ∞`; its single answer (score 2)
develops the Vieta/roots-parameterisation approach and quotes `41/72 + ln2/12` for
the symmetric quadratic. **No one-sided case anywhere in the thread.**

## Limitations of this search (stated plainly)

1. **Li (1988) is still unread.** Everything about it rests on the MR review.
   Resolving this needs interlibrary loan or a purchase.
2. **No true full-text search of the journal literature** was possible — no
   Google Scholar / JSTOR / Zentralblatt full-text access from here. The
   StackExchange API and OEIS were the only genuine full-text indexes queried.
3. **DuckDuckGo blocked automated queries** (bot challenge), so the only general
   web index used was the one behind the built-in search tool.
4. **The dxdy formulas are images**, so that thread was checked structurally, not
   textually.

## Suggested claim language

> To our knowledge the value 719/2880 − ln 2/3 has not appeared previously. The
> only prior work claiming exact probabilities for random cubics, Li (1988),
> treats symmetric coefficient intervals, and its cubic special cases do not
> include the one-sided cube; that paper is effectively unobtainable and no value
> from it has ever been reproduced. Searches of MathOverflow, Math.StackExchange,
> OEIS and arXiv for the constant and for the problem return nothing.
