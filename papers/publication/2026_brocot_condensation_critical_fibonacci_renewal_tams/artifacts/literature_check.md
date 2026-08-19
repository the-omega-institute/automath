# Literature check

## Citation scope

The article cites twelve sources, all carried unchanged from the bibliography
of the source manuscript: ArmendarizLoulakis2011, Berstel2001, Carlitz1968,
Dushistova2007, Feller1971, Liehl1983, MoshchevitinZhigljavsky2004,
OmeyVanGulck2015, Panov1982, Stufler2020, Weinstein2016, and Zeckendorf1972.
No bibliographic item was added. The development pass makes the locations of
the renewal and stable-law inputs precise, so those locations were checked
against the named sources as recorded below.

The title and authors of the companion manuscript were checked against its
local `main.tex`; the companion is identified in prose rather than entered as
a published bibliographic item.

## Critical Gibbs geometry and modern Fibonacci-partition literature

Two bibliographic items were added to place the critical Gibbs theorem
against the modern literature.

- Crossref returned DOI `10.1016/j.jnt.2021.02.010`, the title *On Fibonacci
  partitions*, lead author Sam Chow, journal *Journal of Number Theory*,
  volume 225 (2021), and pages 310--326. These data match the new
  `ChowSlattery2021` entry.
- The official arXiv record `2311.06006` returned the title *The Dynamics of
  the Fibonacci Partition Function*, lead and sole author Tom Kempton, and
  submission date 10 November 2023. These data match the new `Kempton2023`
  entry.
- Crossref returned DOI `10.1016/j.jnt.2023.11.004`, the title *On the
  variance of the Fibonacci partition function*, lead author Sam Chow,
  journal *Journal of Number Theory*, volume 257 (2024), and pages 341--353.
  These data match the new `ChowJones2024` entry.
- The official arXiv record `2309.12724` returned the title *A note on the
  power sums of the number of Fibonacci partitions* and lead and sole author
  Carlo Sanna. These data match the new `Sanna2025` entry; the published
  journal data were checked against the article PDF.

The novelty search used Crossref and the official arXiv API with combinations
of "Fibonacci partition", "Gibbs", "renewal", "stable", "generator", and
"negative moment". The full texts of Weinstein's *Notes on Fibonacci
Partitions* (arXiv:math/0307150), Chow--Slattery (arXiv:2009.08222),
Chow--Jones (arXiv:2308.15415), Kempton (arXiv:2311.06006), and Sanna
(arXiv:2309.12724) were inspected. Weinstein proves the deterministic
free-monoid and orbit classification used here. The later papers concern
exact formulas, mean values, positive power sums, variance, or local
dynamics. None studies inverse-power Gibbs sampling, the macroscopic
generator cost, or stable fluctuations of the number of Weinstein letters.
Crossref searches for renewal-count and renewal-bridge limits returned only
general renewal-process results; the theorem in this article is instead an
arithmetic ensemble limit obtained from the exact Weinstein orbit count.

## Second-order lattice renewal input

Entry: OmeyVanGulck2015, DOI 10.1016/j.spl.2015.05.002.

- Crossref returned the title *Intuitive approximations in discrete renewal
  theory, Part 1: Regularly varying case* and lead author Edward Omey. These
  match the bibliography.
- Semantic Scholar returned the same title, authors E. Omey and S. Van Gulck,
  and the KU Leuven repository record as the open-access location.
- The KU Leuven OAI record
  `oai:lirias2repo.kuleuven.be:123456789/504142` returned the published PDF
  and the same title and authors. The PDF was checked directly.
- The asymptotic used in the paper is the first displayed assertion in
  Section 3.2, immediately following equation (8): for a tail regularly
  varying with index `-alpha`, `alpha > 1`, the renewal mass minus `1/mu` is
  asymptotic to the equilibrium tail divided by `mu`, equivalently to
  `n Fbar(n) / (mu^2 (alpha - 1))`. That assertion is unnumbered in the
  published article, so the manuscript cites its exact section and position
  rather than inventing a theorem number.

## Stable domain-of-attraction input

Entry: Feller1971, *An Introduction to Probability Theory and Its
Applications*, volume II, second edition, Wiley, 1971.

- Open Library work `OL35392227W`, edition `OL27252013M`, returned the title,
  author William Feller, publisher John Wiley & Sons, publication year 1971,
  and edition statement "2nd ed." These match the bibliography.
- The cited criterion is Chapter XVII, Section 5, Theorem 2, the stable
  domain-of-attraction criterion. The manuscript specializes it to positive
  random variables and also proves the needed characteristic-exponent
  convergence from the tail measures, so the normalization, tail balance,
  centering, and Levy measure are all written out in the paper's notation.

## Carried checks

The DOI, title, and lead-author checks recorded for the other carried entries
remain applicable. In particular, the Dushistova title and lead author match
DOI 10.1070/SM2007v198n05ABEH003854, and the Weinstein title and lead author
match DOI 10.1080/10586458.2015.1118416 and arXiv math/0307150.

## Sharp total-variation context rate

The quantitative context theorem was checked against the three closest
sources and against the adjacent manuscripts in the repository.

- The official arXiv record 0912.1516 returned *Conditional Distribution of
  Heavy Tailed Random Variables on Large Deviations of their Sum*, with lead
  author Ines Armendariz.  Its Theorems 1 and 2 give qualitative
  total-variation convergence under product-form subexponential hypotheses;
  they do not give a first-order total-variation constant.
- The official arXiv record 1610.01401 returned *Unlabelled Gibbs
  partitions*, with sole author Benedikt Stufler.  Its small-fragment theorem
  is likewise qualitative and concerns Gibbs partitions with generating
  function product structure.
- Crossref and MathNet returned Dushistova's title *Partitioning of the
  interval [0,1] induced by the Brocot sequences*, lead author Anna A.
  Dushistova, and DOI 10.1070/SM2007v198n05ABEH003854.  The English article
  was inspected directly.  Theorem 3 is a scalar asymptotic expansion for the
  fixed-digit-sum inverse-continuant sum.  It contains no context
  distribution or total-variation assertion.

Searches of Crossref and the official arXiv API combined “Stern--Brocot,”
“Brocot,” “continuant,” “one big jump,” “context,” and “total variation.”
The exact arXiv searches for “Stern--Brocot” with “total variation” and for
“continued fraction” with “one big jump” returned no records.  No located
work states an \(n^{-1}\) context-law rate or its first-order constant for
denominator-weighted Brocot layers.

The repository search covered manuscripts mentioning continued fractions,
renewal theory, Fibonacci layers, or Gibbs laws.  In particular,
2026_finite_window_zeckendorf_thermodynamics_jnt uses the present Brocot
paper only as context and explicitly states that none of its total-variation
results enters that manuscript.  The other matching manuscripts concern
finite-window Zeckendorf spectra, Parry cylinder laws, renewal experiments,
normalization arithmetic, or Fibonacci apparition fibers; none contains a
Brocot context-rate theorem.

---

# Priority check on the correction itself, 2026-08-19

The sharpest claim in this manuscript is that a published constant is wrong: Dushistova's
Lemma 7 gives the leading coefficient as `R_s + 2R_s^2` where this paper gives `2R_s^2`. Two
separate questions follow, and only one of them had been asked before today. The arithmetic
was checked in `verify_dushistova_coefficient.py` and the mechanism in
`verify_dushistova_mechanism.py`. What had not been checked is whether somebody has already
published the correction, which would remove the manuscript's headline entirely.

## The cited source is real

Verified against Crossref by DOI rather than by title match. Author Anna A. Dushistova, title
"Partitioning of the interval [0,1] induced by the Brocot sequences", Sbornik: Mathematics,
volume 198, number 5, pages 661-690, 2007, DOI 10.1070/SM2007v198n05ABEH003854. Every field
agrees with the entry in `references.bib`. This matters because a fabricated citation has
survived several referee rounds in this project before.

The manuscript also localises the error rather than gesturing at it: Lemma 7, pages 668-669,
the loss of the restriction u > 1, with a term counted twice rather than once. That is a
falsifiable diagnosis, which is the right form for a claim of this kind.

## No published correction found, and the search had a working control

Crossref, queried for the surrounding field rather than for the phrase, returned Dushistova
2007 itself among the hits, together with Kessebohmer-Stratmann on Stern-Brocot multifractal
analysis, Reutenauer's Stern-Brocot chapter, and several continuant papers. The source paper
appearing in its own field query is the positive control: the index holds this literature.
Nothing in the results is a correction, an erratum, or a restatement of the coefficient.

## What could NOT be established, and why the silence there means nothing

The natural instrument is the citation graph: read everything that cites Dushistova 2007 and
look for the correction. Semantic Scholar returns "no citations found" for the DOI. That is
not evidence. A control shows the record exists there (paper id 0241224f..., correct title,
journal and pages) but reports `citationCount: 0` for an eighteen-year-old Sbornik paper and
mis-tags its field of study as Physics. The citation edges for this entry are simply absent,
so the query cannot see a correction even if one exists. Recorded as a limit of the check,
not as a result.

## Standing conclusion

No published correction of Dushistova's coefficient was found in an index demonstrably
covering the field, and the citation-graph route is unavailable. That is the strongest
statement the reachable channels support. It does not close the question, and a referee drawn
from this community remains the real test.

## Addendum, same day: the second citation-graph route is also unavailable

Semantic Scholar was recorded above as holding the Dushistova record with no citation edges.
OpenAlex was tried as an independent citation source. It returns an empty result for the
Dushistova query - and also for a control query naming Sanna's 2025 Discrete Analysis paper,
which is certainly indexed there. A channel that returns nothing for a paper known to be
present is not reporting absence; it is not answering. No inference is drawn from either
result.

So both citation-graph routes are closed. The standing conclusion is unchanged: no published
correction was found via Crossref, whose control passed, and the question of whether one
exists cannot be settled with the channels currently reachable.

---

# Numerical status of the coefficient claim, 2026-08-19

Three scripts in this directory bear on the paper's sharpest claim, that the leading constant
is b_C = 2(zeta(s-1)/zeta(s))^2 = 8 at the critical point. None of them supports it at
reachable sizes, and two of them predate my auditing.

    verify_dushistova_coefficient.py   n^s Z_n rises to 15.05 at n=22, increments shrinking
                                       (0.44 ... 0.13); Richardson descends 19.91 -> 17.81;
                                       both head toward roughly 15.5-16
    verify_critical_tail_constant.py   "measured level is roughly 13.9 and still rising ->
                                       ratio to 8 is 1.733"; A+B/d fit gives 16.89,
                                       A+B/sqrt(d) fit gives 20.38
    verify_condensed_split.py          d=10,15,20,25: condensed part 5.06, 6.37, 8.17, 8.66 --
                                       it has PASSED 8 and is still rising; the "rest", which
                                       the referee's account needs to vanish, sits at
                                       3.35, 5.22, 5.05, 5.20 and is not decaying

The last one matters most. verify_condensed_split.py was written to test the referee's
explanation of the discrepancy: that the condensed part converges to 8 while the remainder is
merely slow to vanish. Its own output refutes that explanation on both halves.

## What is and is not established

Established: three independent computations fail to reproduce 8, the measured levels cluster
around 14 to 17, and the residual term required to vanish does not.

NOT established: that 8 is wrong. The two extrapolation fits disagree with each other, 16.89
against 20.38, which means the convergence rate is not identified; with an unidentified rate no
limit can be read off. A factor of two here was raised and retracted at t398 precisely because
an increasing sequence was extrapolated before its maximum, and that retraction stands.

## A correction to my own audit

At t456 I ran all 33 artifact scripts and recorded 30 as OK on the basis of exit codes. Two of
those thirty - verify_critical_tail_constant.py and verify_condensed_split.py - exit 0 while
printing evidence against the manuscript. Exit code measures whether a script crashed, not
whether it agrees with the paper. Any future sweep must read the output, not the status.

## Action, and it is not a writing task

This is the paper's headline and it must be settled before submission. The route is to push d
and n far enough to identify the convergence rate, or to locate a normalisation discrepancy
between the scripts and the manuscript's definition of Z_n. The definition was checked today
against sec_introduction.tex - Q_n is the set of canonical fractions of digit sum n, and the
scripts sum exactly those, last digit >= 2 - so no discrepancy was found there.

## Correction to the two entries above, same day

The section "Numerical status of the coefficient claim" and its predecessor overstated the
problem, and the correction belongs next to them rather than in a commit message.

verify_dushistova_mechanism.py, which sits in this directory and which I ran and logged as
passing without reading, states in its own docstring:

    The limit itself resists brute force: n^s Z_n rises to about 15.28, turns over near
    n = 27, and at n = 29 has only begun to descend, so finite data cannot separate 2R^2
    from anything else. That was established, and an earlier extrapolation of mine through
    the turning point was withdrawn.

So the sequence is known to PEAK near n = 27 and descend. Every measurement I assembled - my
own walk to n = 24, the tail-constant script to d = 25, the condensed split to d = 25 - lies
before that turning point. Reporting that they "cluster around 14 to 17 and are still rising"
described the pre-peak regime and carried no information about the limit. The observation that
the condensed part "has passed 8 and is still rising" is the same error: it is rising because
nothing has turned over yet.

The mechanism is separately checked and it holds. The paper attributes Dushistova's extra R_s
to losing the restriction u > 1, which double-counts the empty left context.
verify_dushistova_mechanism.py confirms the arithmetic is exactly self-consistent: endpoints
supply 2R under the corrected constant against 3R under the printed one, a difference of
R_s = 2.0, matching 10 - 8 precisely.

What survives from those entries:

  - verify_dushistova_coefficient.py really was emitting "the data favour: Dushistova" with
    exit 1. That is a live hazard whatever the mathematics, and replacing it with an explicit
    NOT DISCRIMINATING report was right. The sibling docstring now independently justifies
    that wording.
  - The exit-code point stands: I logged 30 of 33 scripts OK without reading their output, and
    two of them print material that needs reading. This episode is a second instance of the
    same failure - I ran verify_dushistova_mechanism.py, saw exit 0, and did not read the
    docstring that answered the question I then spent three ticks on.

What does not survive: the framing that brocot's headline is numerically unsupported. It is
unsettled at reachable n, which the paper's own artifacts already said, and the error mechanism
it claims is verified.

---

# Oracle on the convergence rate, 2026-08-19: constant confirmed, one formula inconsistent

Transcript at artifacts/oracle_sprint_BROCOT_RATE_r1.md, task 8500d3e7. It confirms the
paper's constant and supplies a full singular expansion:

    n^s Z_n(s) = 2 R_s^2 + A_s/n + B_s n^(1-s) + O(n^(-2)),   rate n^(-1),
    A_s = 2 s R_s (1 + 2 mu_s - R_s),  mu_s = sum_{m>=2} Z_m(s)/m,
    B_s = 4 R_s^3 Gamma(1-s)^2 / Gamma(2-2s).

So C = 2 R_s^2 = 8 at sigma_0, and the paper's headline constant is supported.

## What checks out

B_s, exactly. Evaluating the closed form independently gives -44.58169885 against the
transcript's -44.5817.

It also passes the structural test set at t470. That test said any answer offering a single
correction exponent could not produce a turnover and should be challenged. This answer supplies
two corrections of opposite sign, and goes further, stating plainly that they predict the
eventual turnover but NOT its location near n = 27, which it attributes to still-large
O(n^(-2)) and preasymptotic terms. That is the honest form of the answer.

## What does not check out

A_s. Evaluating the stated formula with mu_s computed from my own Z_m for m = 2..25 gives

    mu_s = 0.2199,   A_s = 2 s R_s (1 + 2 mu_s - R_s) = -5.553,

against the transcript's numerical A_s = 215.3798. Wrong sign and two orders of magnitude. The
sum defining mu_s converges quickly, since Z_m ~ 8 m^(-s) makes the terms of order m^(-3.48),
so the truncation at m = 25 is not the explanation; reproducing 215.38 would need mu_s = 11.36.

The transcript's NUMERICAL value is the one consistent with the data: 8 + 215.3798/n +
B_s n^(1-s) gives 16.23 at n = 25 against an observed 15.26, whereas A_s = -5.553 would give
about 7.4, which is impossible since the observed values exceed 15.

So the formula for A_s and the transcript's own number for A_s disagree, and the number is the
defensible one. Either mu_s means something other than what is written, or the closed form is
wrong. This must be resolved before any of it is used in the manuscript.

## Fit against the computed table

Using the transcript's constants, the predicted minus observed difference runs 13.42, 11.50,
9.83, 8.39, 7.13, 6.03, 5.07, 4.22, 3.49, 2.84, 2.28, 1.78, 1.35, 0.98 at n = 12..25. It is
large but shrinking monotonically and steadily, which is what one expects if the expansion is
correct and the neglected terms are still significant at these n. That is consistent with the
transcript's own caveat, and it means the expansion cannot be confirmed or refuted from data
below the turnover.

---

# RESOLVED, 2026-08-19: the headline constant is 8, confirmed independently

The question open since t456 is settled. Using the resolvent recurrence, implemented by me from
the transcript's formulas and validated against my exact-integer table (agreement to 1e-14 for
n = 12..23, and inside the table's own truncation bounds at 24 and 25), Z_n was computed to
n = 1000:

    n =   27    15.27604810      the pre-asymptotic maximum
    n =   29    15.22533147      past it, descending
    n =  100    10.58439943
    n =  500     8.44585557
    n = 1000     8.21863327

All five reproduce the transcript's independently stated values to between 1e-12 and 1e-13.
The sequence descends steadily toward 8.

So C = 2 R_s^2 = 8 at sigma_0. The manuscript's constant is correct and the published value
R_s + 2R_s^2 = 10 is not, which is what the paper claims. This is now confirmed by computation
rather than argued from a mechanism.

## The 14-to-17 readings were entirely pre-asymptotic

Every measurement gathered at t456 and t457 sat below n = 27. The maximum there is 15.276 and
the descent to 8 takes until roughly n = 1000. Nothing in that range bore on the limit, which
is what verify_dushistova_mechanism.py had already said and what I failed to read.

## The A_s coefficient, stated honestly

n(n^s Z_n - 8) runs 268.24, 258.44, 236.74, 228.97, 222.93, 220.44, 218.63 at
n = 50, 100, 200, 300, 500, 700, 1000. It decreases monotonically and my n = 1000 value
reproduces the transcript's own 218.633 exactly, so the trend is consistent with the claimed
A_s = 215.3798.

It is not pinned. Subtracting the stated B_s n^(1-s) term to accelerate convergence moved the
sequence the WRONG way, to 220.27 at n = 1000 rather than closer to 215.38. That may be a sign
convention on my side or a further term, and I am recording it rather than presenting the
corrected column as confirmation. The constant C = 8 does not depend on it.

## What this changes

brocot's headline is no longer an open item. The remaining entries for this paper are the
reproducibility statement, the two working-directory bugs, and the venue decision -- all
mechanical or editorial.
