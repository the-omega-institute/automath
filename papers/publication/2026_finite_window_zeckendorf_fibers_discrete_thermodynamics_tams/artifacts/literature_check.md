# Literature Check: Real-Tilt Pressure and Large Deviations

Date of search: 2026-08-02 (Asia/Singapore).

## Named-problem and standard-object audit (2026-08-14)

The search was repeated against primary texts and four bibliographic
services.  The arXiv Atom query 'all:"Fibonacci partition"' returned twelve
records.  Crossref DOI records and zbMATH Open confirmed the publication
metadata below.  Semantic Scholar's DOI endpoint returned Weinstein's
six-item citation graph and the five-item citation graph of Chow--Slattery;
its free-text endpoint and a later request for the 2022 paper returned HTTP
429.  Exact-phrase arXiv and Crossref searches, the available citation
graphs, and full-text checks of the later Fibonacci-partition papers located
no resolution of the following three problems.  This is evidence of current
status, not a claim of exhaustive priority.

1. F. V. Weinstein, *Notes on Fibonacci Partitions*, Experimental
   Mathematics 25 (2016), 482--499,
   doi:10.1080/10586458.2015.1118416, p. 18:
   **"How to describe the set of F-primitive numbers?"**

   The paper's weighted-generator renewal
   (prop:weighted-generator-renewal) and Tauberian law
   (thm:psi-tauberian) enumerate Weinstein generators by multiplier and
   cost.  They do not decide whether the *minimal integer* at a fixed
   multiplier is f-simple.  The missing step is an order-sensitive
   comparison excluding every non-simple orbit representative below the
   least simple representative.

2. Weinstein, ibid., Conjecture 9.1, pp. 19--20:
   **"Then \(C_i\) coincides with the convex hull of the set of points
   \((c,F(c))\)"** for the explicitly defined sets \(B_1(i)\), and also
   \(B_2(i)\) in even layers.

   The interval identity (thm:fiber-partition-interval) canonically
   recovers every value of the standard function \(R=F\) on these layers,
   and thm:unconditional-extremal-fibers proves the top horizontal support
   value and all its maximizers.  The conjecture requires every supporting
   slope.  What is missing is a uniform supporting-line inequality for all
   partition values, not another maximum computation.

3. F. V. Weinstein, *On a theorem of J. Shallit concerning Fibonacci
   partitions*, Communications in Mathematics 30 (2022), 203--207,
   doi:10.46298/cm.10769, Conjecture 3.3, p. 207:
   **"\(r_3^{(a,i,b)}(n)-r_3^{(a,j,b)}(n)\le1\) for any
   \(i,j\in\{0,1,2\}\). Moreover, [the product of the three pairwise
   differences] \(=0\)."**

   The coefficient-spectrum identity in thm:affine-transfer starts from
   the same truncated product, and a part-count mark replaces it by
   \(\prod_{r=a}^b(1+u z^{f_r})\).  The present Fourier formulas act on the
   value coordinate only.  The missing input is a roots-of-unity
   cancellation theorem at \(u^3=1\), uniform in \(a,b,n\); no such estimate
   follows from the unmarked renewal.

### Closed false lead

Chow--Slattery, *On Fibonacci partitions*, J. Number Theory 225 (2021),
310--326, Conjecture 1.4, asked whether
**"\(B(H)\to B\) \((H\to\infty)\)"**.  This is not still open.  Zhou,
*On the Representation Functions of Certain Numeration Systems*,
arXiv:2305.00792, Corollary 1.5, explicitly states that its Fibonacci
specialization solves Conjecture 1.4 and the first three problems on
Chow--Slattery p. 315.  It is therefore excluded from the candidate list.

### A/B/C/D decision

- **(A):** The three live problems are genuine, but the manuscript lacks the
  order-sensitive minimum comparison, all-slope support inequalities, and
  roots-of-unity cancellation they respectively require.
- **(B):** The exact identity
  \(d_m(x)=R(\chi_m(x))\) maps the bespoke fibers bijectively to two standard
  Fibonacci layers.  More strongly, the already proved generator renewal has
  exact one-layer weights \(2,1\).  This route is selected.
- **(C):** The main pressure and LDP are already unconditional.  The local
  prime-support theorem stops at an active-cutoff stable/semistable renewal
  input; the dyadic infinite-variance and no-positive-exponential-moment
  calculation shows that this is a real obstruction, not a removable
  Gaussian hypothesis.
- **(D):** The largest-fiber formulas, freezing boundary, critical constants,
  and LDP exponent are already sharp.  The compact-operator obstruction has
  no plausible converse without specifying an operator class beyond the
  hypotheses it rules out.

The selected theorem is now thm:standard-fibonacci-thermodynamics: all-real
pressure, frozen unnormalized limit, critical \(2m/\mu_C\) law, critical
Gibbs coexistence, and a full LDP for \(m^{-1}\log R(n)\) under the uniform
law on one standard Fibonacci layer.  Its LDP lower bound uses one-layer
orbit weights directly; it is not inferred from a two-layer mixture.

## Active-cutoff joint-renewal audit (2026-08-10)

The tier-up target was searched before the proof attempt in all four required
services.  The arXiv Atom API returned the known Fibonacci-partition chain for
`all:"Fibonacci partition"`; the combined query with `"local limit"`
returned zero records.  `all:"ordered factorizations"` returned Hwang--Janson
(arXiv:0902.3419) and later factorisatio-numerorum papers, while
`all:"renewal reward" AND all:"local limit"` returned zero records and the
semistable/local-limit query returned only the general strong-renewal paper
arXiv:2005.11121.

Crossref identified the nearest coefficient and factorization results as
Pemantle--Wilson, doi:10.1006/jcta.2001.3201; Lau,
doi:10.1006/jnth.2001.2687; and Hwang--Janson,
doi:10.1214/EJP.v16-858.  Its heavy-tail search also located Mineka's general
stable local limit theorem, doi:10.1214/aop/1176996764.  Semantic Scholar's
free-text endpoint returned HTTP 429 on repeated queries, but its DOI endpoint
successfully confirmed Pemantle--Wilson and its citation graph.  zbMATH Open,
after the required terms-of-use handshake, returned Zbl 1763798
(Pemantle--Wilson), Zbl 1731886 (Lau), and Zbl 3462906 (Mineka).  No located
record combines fixed prime-exponent conditioning, continued-fraction cost,
and a uniform lattice local theorem at a moving cutoff.

The proof attempt reaches the exact formal identity
`1/(1-A_P(z,u))` for the joint exponent--cost counts and the rational
specialization `1/(2-product_i (1-z_i)/(1-p_i z_i))` at `u=1`.  It fails at
local inversion in the cost coordinate.  On the dyadic ray the letter
`1/2^a` has probability `3^{-a}` and cost `2^{a+1}-1`, so the cost has
infinite second moment and no positive exponential moment.  Thus neither a
Gaussian local theorem nor a two-sided Cramer tilt applies through
`j=m+O(1)`.  The missing input is a multivariate exponent-conditioned lattice
stable or semistable local-renewal theorem with the arithmetic boundary
weights `4,3,1`; the manuscript now records this interface without claiming
the requested sharp asymptotic.

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

# Deep-exploration audit: critical finite-window scaling (2026-08-08)

The new search queried the arXiv Atom API for `"Fibonacci partition"`
combined separately with `critical`, `Gibbs`, `pressure`, `large deviation`,
and `renewal`; every combined query returned zero records. The broad query
returned the known Weinstein, Sanna, Kempton, Chow--Slattery, and
Chow--Jones records. Crossref confirmed Weinstein
(DOI 10.1080/10586458.2015.1118416), Sarig's two pressure papers
(DOIs 10.1017/S0143385799146820 and 10.1007/s002200100367), Pemantle--Wilson
(DOI 10.1006/jcta.2001.3201), Lau
(DOI 10.1006/jnth.2001.2687), and Hwang--Janson
(DOI 10.1214/EJP.v16-858). zbMATH Open searches for `Fibonacci partition`,
`ordered factorizations`, `renewal reward theorem`, and `multivariate
rational coefficient` found the expected adjacent subjects but no
finite-window critical Gibbs theorem. The Semantic Scholar endpoint returned
HTTP 429 throughout this pass; its same-day citation-graph audit recorded
above had already found only the known Weinstein citation chain. Thus no
novelty claim depends on the unavailable Semantic Scholar response.

Candidates were scored on a ten-point scale as follows.

1. Exact critical finite-size and uniform coexistence law: reach 10,
   novelty 8, value 9. Nearest inputs are Feller's arithmetic renewal theorem
   and Sarig's general phase-transition framework; neither treats Fibonacci
   partition fibers or the four-branch finite-window transfer. This is the
   theorem added in the present round.
2. Active prime-ray crossover with a joint exponent--cost local theorem:
   reach 3, novelty 9, value 10. The heavy letters `1/q` force an infinite
   second cost moment, so a Gaussian crossover is false; a heavy-tail or
   semistable local theorem is missing. Tsirelson (arXiv:1207.1290) and Chi
   (arXiv:0707.4596) are only general renewal-reward comparators.
3. Divergence of active-side pressure curvature at the freezing point:
   reach 10, novelty 7, value 7. The derivative formula and the letters
   `1/q` prove it directly. Sarig is the nearest qualitative comparator, but
   this is less informative than the full finite-window Gibbs limit.
4. Fixed finite-prime-support exponent-ray asymptotics in the inactive
   region: reach 8, novelty 4, value 5. Pemantle--Wilson smooth-point ACSV is
   the decisive existing theorem; Lau and Hwang--Janson treat averaged ordered
   factorizations. This remains a standard corollary rather than a new
   mechanism.
5. Exact prime-power quenched speed for every prime: reach 9, novelty 6,
   value 6. Weinstein's free-monoid formula and the manuscript's dyadic
   renewal proof nearly give it verbatim; the gain over the dyadic theorem is
   mainly parameter coverage.
6. Sharpness of the stabilization threshold `m >= 2k`: reach 10, novelty 6,
   value 5. Weinstein's orbit formulas and the extremal letter `1/k` give the
   converse, but the result is chiefly exact bookkeeping.
7. Classification of the second or fixed top multiplicity rank: reach 3,
   novelty 8, value 8. Kocabova--Masakova--Pelantova is the nearest extremal
   work. The interval transfer reduces the question but supplies no new
   classification of those partition levels.
