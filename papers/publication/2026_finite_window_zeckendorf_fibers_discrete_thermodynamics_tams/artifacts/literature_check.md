# Literature Check: Real-Tilt Pressure and Large Deviations

Date of search: 2026-08-02 (Asia/Singapore).

## Search protocol

The arXiv Atom API (`https://export.arxiv.org/api/query`) was queried directly.
Bibliographic metadata and DOI records were checked against arXiv metadata,
OpenAlex, publisher DOI records, and the manuscript's existing references. A
Crossref REST query was also attempted; the endpoint returned HTTP 429 during
this search, so no claim below depends on an unavailable Crossref response.

The principal arXiv queries and results were as follows.

1. `all:"Fibonacci partition"` returned 12 records. The directly relevant
   records were Kempton, *The Dynamics of the Fibonacci Partition Function*,
   arXiv:2311.06006; Sanna, *A note on the power sums of the number of
   Fibonacci partitions*, arXiv:2309.12724; Chow--Jones, *On the variance of
   the Fibonacci partition function*, arXiv:2308.15415; Chow--Slattery, *On
   Fibonacci partitions*, arXiv:2009.08222; and Weinstein, *Notes on Fibonacci
   Partitions*, arXiv:math/0307150.
2. `all:"Fibonacci partition" AND (all:pressure OR all:"large deviation")`
   returned 0 records.
3. `all:"Fibonacci partition function" AND (all:moment OR
   all:thermodynamic)` returned 0 records.
4. `all:"Thermodynamic formalism for countable Markov shifts"` returned four
   later records using Sarig's formalism, including Iommi--Yayama,
   arXiv:1106.0720, DOI 10.1088/0951-7715/25/1/165. The original Sarig papers
   are publisher-indexed rather than arXiv-indexed.
5. `au:Sarig AND all:"phase transitions"` returned 0 records. The original
   published phase-transition paper was separately verified by DOI.
6. `all:"Gartner-Ellis" AND all:"large deviations"` returned seven later
   applications/generalizations; the original Gartner and Ellis articles were
   separately verified by DOI.
7. `all:"Ruelle-Perron-Frobenius" AND all:analytic` returned Giulietti et al.,
   *The calculus of thermodynamical formalism*, arXiv:1508.01297, as a modern
   compact-state comparator.

These searches do not constitute an exhaustive mathematical-novelty proof.
They establish only that no arXiv record located by the stated direct queries
claims the present finite-window real-tilt pressure theorem or LDP.

## Exact references and use

- D. Ruelle, *Thermodynamic Formalism*, 2nd ed., Cambridge University Press,
  2004, DOI 10.1017/CBO9780511617546. This is cited for the classical compact,
  spectral-gap Ruelle--Perron--Frobenius paradigm. Its hypotheses are not
  asserted for the present multiplicity cocycle.
- O. M. Sarig, "Thermodynamic formalism for countable Markov shifts,"
  *Ergodic Theory Dynam. Systems* 19 (1999), 1565--1593,
  DOI 10.1017/S0143385799146820. This is cited for the countable-state
  recurrence/RPF framework.
- O. M. Sarig, "Phase transitions for countable Markov shifts,"
  *Comm. Math. Phys.* 217 (2001), 555--577,
  DOI 10.1007/s002200100367. This is cited to distinguish countable-state
  phase-transition behavior from globally analytic compact-state pressure.
- J. Gartner, "On large deviations from the invariant measure,"
  *Theory Probab. Appl.* 22 (1977), 24--39, DOI 10.1137/1122003; and
  R. S. Ellis, "Large deviations for a general class of random vectors,"
  *Ann. Probab.* 12 (1984), 1--12, DOI 10.1214/aop/1176993370. These are the
  original large-deviation references behind the Gartner--Ellis theorem.
- A. Dembo and O. Zeitouni, *Large Deviations Techniques and Applications*,
  2nd ed., Springer, 2010, DOI 10.1007/978-3-642-03311-7, Theorem 2.3.6. This
  is the precise modern theorem invoked for the conditional full LDP.
- C. Sanna, "A note on the power sums of the number of Fibonacci partitions,"
  *Discrete Analysis* 2025:2, DOI 10.19086/da.137601,
  arXiv:2309.12724. Sanna proves integer-power asymptotics and the integer
  zero-temperature limit; no noninteger pressure regularity is claimed there.
- F. V. Weinstein, "Notes on Fibonacci partitions," *Experimental
  Mathematics* 25 (2016), 482--499,
  DOI 10.1080/10586458.2015.1118416, arXiv:math/0307150. The manuscript uses
  Weinstein's Theorems 3.8, 5.1, and 10.3 for the generating-orbit level
  decomposition and the exact Dirichlet series
  `1 + sum Psi(k) k^{-s} = (2 - zeta(s-1)/zeta(s))^{-1}`. The published proof
  is cited, not reproduced.
- T. Kempton, "The Dynamics of the Fibonacci Partition Function,"
  arXiv:2311.06006. This provides a matrix-cocycle/irrational-rotation
  description of local Fibonacci-partition dynamics, but does not establish
  the finite-window real-moment pressure or its large deviations.

## Novelty conclusion and obstruction

The requested theorem, namely a finite all-real pressure that is real analytic
and strictly convex on the whole real line, is false. Weinstein's published
level-set orbit decomposition implies an exact frozen phase. If

`zeta(sigma_0 - 1) / zeta(sigma_0) = 2`, with
`sigma_0 = 2.478750785733960...`, then the manuscript proves

`P(t) = 0` for every `t <= -sigma_0`.

Since `P(0) = log(phi)`, analytic continuation from the frozen open half-line
would give a contradiction. This also excludes strict convexity on all of the
real line. The new, fully proved contribution is the transfer of Weinstein's
level-orbit Dirichlet structure through the paper's exact two-layer fiber
identity to obtain this finite-window freezing theorem, including the critical
endpoint. No located reference states this finite-window consequence.

At the date of this first audit, the residual open interface was existence for
every t in (-sigma_0, infinity), differentiability at -sigma_0, and analytic
positive curvature within the open positive-pressure phase. The later
weighted-renewal proof in the manuscript closes that interface; the updated
source audit and the missing denominator-layer estimate are recorded below.

# Tier-up prior-art audit (2026-08-08)

The audit used the arXiv API, Crossref, Google Scholar, Semantic Scholar's
citation graph, and zbMATH Open. MathSciNet itself was not accessible without
an authenticated subscription. Search strings included combinations of
"Fibonacci partitions", "fixed multiplier", "prime exponent vector",
"ordered factorizations", "multivariate local limit", "multiplicative
renewal", and "Stern-Brocot denominator pressure".

Weinstein's paper was checked from the full arXiv text, not just metadata.
Its Proposition 3.3 and Theorems 3.8, 5.1, and 10.3 supply the free generator
monoid, multiplier multiplicativity, orbit decomposition and layer
stabilization, and the Dirichlet generating series. The manuscript already
cited Weinstein, but the introduction now states this ownership in one
explicit sentence and says that none of those mechanisms is claimed here.
Semantic Scholar returned six citing works; Google Scholar returned seven.
The visible citation chain consists of Chow--Slattery, Chow--Jones, Shallit,
Sanna, Kempton, and related Fibonacci-partition papers. No item in that chain
states the finite-window weighted-cost renewal or active-window arithmetic
asymptotics.

The pressure audit found that Kessebohmer--Stratmann Theorem 1.1 proves the
logarithmic Stern--Brocot pressure law, while Fiala--Kleban--Oezluek Section
IV, equations (23), (26), and (28), gives the Perron--Frobenius layer
asymptotic for 0 < s < 2. Those locations did not by themselves justify the
manuscript's former generic all-s < 2 attribution. The manuscript now
contains a separate lemma: it maps the positive range to those exact
equations and proves s <= 0 directly by a bridged matrix
quasi-multiplicativity argument.

For a fixed prime set S, Weinstein's free monoid gives the exact rational
generating function

    1 / (2 - product_{p in S} (1-z_p)/(1-p z_p)).

The applicable standard coefficient result is the smooth-point theory of
R. Pemantle and M. C. Wilson, "Asymptotics of Multivariate Sequences",
J. Combin. Theory Ser. A 97 (2002), 129--161,
doi:10.1006/jcta.2001.3201. The ordered-factorization comparison literature
also includes Y.-K. Lau, "Local Distribution of Ordered Factorizations of
Integers", J. Number Theory 91 (2001), 312--317,
doi:10.1006/jnth.2001.2687, and H.-K. Hwang and S. Janson, "A Central Limit
Theorem for Random Ordered Factorizations of Integers", Electron. J. Probab.
16 (2011), doi:10.1214/EJP.v16-858. Those two papers concern averaged random
ordered factorizations, not the present exact fixed-prime exponent vectors.

Consequently the proposed m^{-(|S|-1)/2} exponent-ray asymptotic in the
inactive-cost interior is a standard smooth-point multivariate rational
coefficient theorem, followed by the same cost-law transfer used for the
dyadic ray. This is an easy ACSV/renewal corollary, not a tier-raising new
mechanism, and it has not been added as a theorem. A materially stronger
nearby target would describe the active finite-window cost boundary and its
critical crossover. That requires a sharp joint local theorem for the prime
exponent vector and continued-fraction cost; no such input was located in the
searched literature, and it is not available from the manuscript's current
arguments.
