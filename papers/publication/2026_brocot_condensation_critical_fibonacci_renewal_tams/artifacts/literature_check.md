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
