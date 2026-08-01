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

The residual open interface is existence for every
`t in (-sigma_0, infinity)`, differentiability at `-sigma_0`, and analytic
positive curvature within the open positive-pressure phase. Consequently the
full LDP remains conditional on this corrected residual hypothesis. The paper
does not claim that general Ruelle or Sarig theory verifies the required
operator hypotheses for this cocycle.
