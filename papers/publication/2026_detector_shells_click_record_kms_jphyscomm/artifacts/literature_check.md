# Literature check: killed-reset D-MAP identifiability

Checked 2026-08-02 against the arXiv Atom API and Crossref. The search was
performed before theorem promotion. It is a reproducible boundary check, not
a claim that an API query can prove absence from the entire literature.

## arXiv API queries

Endpoint: `https://export.arxiv.org/api/query`.

| Search query | API total | Relevant result |
|---|---:|---|
| `ti:"On non-uniqueness of representations of phase-type distributions"` | 0 | The 1989 paper predates arXiv. |
| `ti:"Nonidentifiability of the two-state Markovian arrival process"` | 0 | The 2010 paper has no arXiv record returned. |
| `ti:"New results about weakly equivalent MAP2 and MAP3 processes"` | 0 | The 2012 paper has no arXiv record returned. |
| `ti:"On identifiability and order of continuous-time aggregated Markov chains"` | 0 | The 1996 paper predates arXiv. |
| `all:"killed-reset" AND all:identifiability` | 0 | No exact killed-reset identifiability result found. |
| `all:"killed reset" AND all:"Markovian arrival"` | 0 | No result found. |
| `all:hypoexponential AND all:identifiability` | 0 | No result found under this terminology. |
| `all:"serial phase-type" AND all:identifiability` | 0 | No result found under this terminology. |
| `all:"Coxian phase-type" AND all:"non-uniqueness"` | 1 | Rizk--Burke--Walsh, arXiv:1901.03849v2. |
| `all:"time-to-event" AND all:"Markov chain" AND all:identifying` | 5 | Radulescu et al., arXiv:2311.03593v2, is directly relevant. |
| `all:"phase-type" AND all:identifiability` | 20 | Included arXiv:1901.03849v2 and arXiv:2311.03593v2; the other returned entries did not state the killed-reset orbit criterion or the pure serial collision result. |
| `all:Prony AND all:Hankel AND all:identifiability` | 1 | arXiv:2605.15917v1, a higher-Prony moment paper, not a D-MAP/phase-type identifiability theorem. |
| `all:"Prony's method" AND all:Hankel` | 2 | Included Kunis--Roemer--von der Ohe, arXiv:1907.01547v2. |

Exact API title queries for the four older papers returned zero results. The
absence of arXiv identifiers for those works is therefore recorded explicitly
rather than inventing identifiers.

## Exact citations used

- C. A. O'Cinneide, "On non-uniqueness of representations of phase-type
  distributions," *Communications in Statistics. Stochastic Models* **5**(2),
  247--259 (1989), DOI: `10.1080/15326348908807108`. Crossref confirms that
  `...07107`, which appeared in the previous manuscript, belongs to a different
  article. No arXiv ID was returned.
- T. Ryden, "On identifiability and order of continuous-time aggregated Markov
  chains, Markov-modulated Poisson processes, and phase-type distributions,"
  *Journal of Applied Probability* **33**(3), 640--653 (1996), DOI:
  `10.2307/3215346`. No arXiv ID was returned.
- P. Ramirez-Cobo, R. E. Lillo, and M. P. Wiper, "Nonidentifiability of the
  Two-State Markovian Arrival Process," *Journal of Applied Probability*
  **47**(3), 630--649 (2010), DOI: `10.1239/jap/1285335400`. No arXiv ID was
  returned.
- P. Ramirez-Cobo and R. E. Lillo, "New Results About Weakly Equivalent MAP 2
  and MAP 3 Processes," *Methodology and Computing in Applied Probability*
  **14**(3), 421--444 (2012), DOI: `10.1007/s11009-011-9227-x`. No arXiv ID
  was returned.
- M. Bladt and B. F. Nielsen, *Matrix-Exponential Distributions in Applied
  Probability*, Springer (2017), DOI: `10.1007/978-1-4939-7049-0`. No arXiv
  ID was located.
- J. Rizk, K. Burke, and C. Walsh, "On the Non-uniqueness of Representations
  of Coxian Phase-Type Distributions" (2019), arXiv:`1901.03849v2`. No DOI is
  present in the arXiv metadata.
- O. Radulescu, D. Grigoriev, M. Seiss, M. Douaihy, M. Lagha, and E. Bertrand,
  "Identifying Markov Chain Models from Time-to-Event Data: An Algebraic
  Approach," *Bulletin of Mathematical Biology* **87**(1), article 11 (2025),
  DOI: `10.1007/s11538-024-01385-y`, arXiv:`2311.03593v2`.
- S. Kunis, T. Roemer, and U. von der Ohe, "Learning algebraic decompositions
  using Prony structures," *Advances in Applied Mathematics* **118**, 102044
  (2020), DOI: `10.1016/j.aam.2020.102044`, arXiv:`1907.01547v2`.

## Novelty boundary

The minimal-realization similarity statement and the existence of multiple
Markovian phase-type/MAP representatives are established theory and are cited
as such. The manuscript does not claim to rediscover their proofs. The exact
orbit--cone fibre criterion is a specialization of that theory to
deterministic-reset D-MAPs and gives a sharp necessary-and-sufficient boundary
for any declared subclass and structural quotient. The substantive
model-specific conclusion is that
the pure serial subclass is a transversal of those visible fibres at the level
of the unordered rate multiset for every positive rate vector: repeated
sampled poles retain their algebraic multiplicities through the confluent
Hankel recurrence. Thus pole collision causes singular local coordinates and
poor conditioning, but not loss of population identifiability. Coxian models
with early absorption and general phase-type graphs remain outside this pure
serial claim and can be nonunique, consistently with arXiv:1901.03849 and the
classical literature.

No arXiv result returned by the stated searches asserts this exact
deterministic-reset orbit-fibre formulation together with the all-collision
pure-serial corollary. This supports a narrowly stated novelty claim; it does
not support a claim of a new general phase-type realization theorem.

## A8 follow-up boundary check

Checked 2026-08-03 before promoting the A8 results. Direct Atom API requests
to https://export.arxiv.org/api/query were made for:

- all:"logarithmic divided difference" AND all:"Markovian arrival";
- all:hypoexponential AND all:"sampling interval";
- all:"hidden eigenvalue" AND all:"Markovian arrival".

Initial requests returned HTTP 429, including delayed retries.  A final
identified retry on 2026-08-03 returned HTTP 200 and
`opensearch:totalResults=0` for each of the three queries.  The same three
exact combinations were also cross-checked through the standard arXiv search
interface, which returned no results. Crossref and
OpenAlex bibliographic searches for "sampled-counter D-MAP physical image,"
"hypoexponential discretization sampling bias," and "hidden eigenvalue
Markovian arrival sharp bound" returned no matching theorem; their leading
results were unrelated uses of the component terms. The broader successful
Atom API searches dated 2026-08-02 above already cover discrete MAP canonical
forms, phase-type identifiability, and the killed-reset terminology.

The Lambert-W inversion and branch asymptotics are not new. The standard
source is R. M. Corless, G. H. Gonnet, D. E. G. Hare, D. J. Jeffrey, and
D. E. Knuth, "On the Lambert W function," *Advances in Computational
Mathematics* **5**, 329--359 (1996), DOI 10.1007/BF02124750. The manuscript's
implicit exact-one-dependence branch is already sufficient; any explicit
Lambert-W rewrite must be cited as imported special-function calculus.

On this search boundary, no source was found for the model-specific exact
three-inclusion logarithmic-divided-difference image equation, the sharp
sampled-counter hidden-mode range, or the displayed small-sampling-interval
cycle bias. These results are promoted only in their narrow model-specific
forms. The general minimal-realization orbit theorem, Lambert-W theory,
metric-projection limits, and confluent Prony collision theory remain cited
background rather than new contributions.

## A8-r2 joint image-test boundary check

Checked 2026-08-03 through the live arXiv Atom API before integrating the
joint image test. The initial identified requests received HTTP 429 responses;
identified curl retries then returned HTTP 200. The following model-specific
queries all returned opensearch:totalResults=0:

- all:"sampled-counter" AND all:"physical image";
- all:"discrete Markovian arrival" AND all:"boundary test";
- all:"renewal binary" AND all:"model specification";
- all:"three inclusion" AND all:"Markovian arrival";
- all:"cone Wald" AND all:"local power";
- all:"Markovian arrival process" AND all:"goodness of fit".

A broader API query,
all:"Markovian arrival process" AND all:inference, returned one result,
arXiv:2401.14561v1, “Fitting procedure for the two-state Batch Markov
modulated Poisson process.” It does not state a three-inclusion physical-image
test, the analytic discriminant constraint used here, or the local-power
formula.

The general constrained-inference ground is already published. Exact-title
API queries returned:

- Fang and Seo, “A Projection Framework for Testing Shape Restrictions That
  Form Convex Cones,” arXiv:1910.07689v4, published in *Econometrica* 89(5),
  2439--2458 (2021), DOI 10.3982/ECTA17764;
- Fang and Santos, “Inference on Directionally Differentiable Functions,”
  arXiv:1404.3763v2, published in *Review of Economic Studies* 86(1),
  377--412 (2019), DOI 10.1093/restud/rdy049.

The older foundational sources have no arXiv record returned by exact-title
queries: Chernoff (1954), DOI 10.1214/aoms/1177728725; Shapiro (1987), DOI
10.1090/S0002-9939-1987-0866441-7; and Andrews (2001), DOI
10.1111/1468-0262.00210. Crossref and OpenAlex searches for
“sampled-counter D-MAP physical image,” “discrete Markovian arrival boundary
Wald test,” and “renewal binary model specification test” returned no
model-specific theorem matching the proposed construction.

Accordingly, the manuscript attributes cone projection, chi-bar-square
limits, boundary calibration, and general LAN machinery to the standard
literature. The only novelty claimed is the sampled-counter specialization:
the root-free analytic constraint map, its rank and regenerative covariance
nondegeneracy, compact-uniform studentization, and its explicit local-power
coordinates.

## A8-r3 complete-law and realization check

Checked 2026-08-07 through the live arXiv Atom API and Crossref before theorem
integration. The arXiv query
`all:"distributional distance" AND all:"time series"` returned six records,
including Ryabko, arXiv:1107.4165v2, and Ryabko--Ryabko,
arXiv:0804.0510v4. The author query
`au:Ryabko AND (all:"hypothesis testing" OR all:"distributional distance")`
returned five records, including arXiv:0905.4937v4, arXiv:1107.4165v2, and
arXiv:0804.0510v4. These papers establish distributional-distance testing and
the stationary-ergodic scope limitations; neither the metric nor the general
ergodic consistency principle is claimed here as new.

The following model-specific arXiv API queries each returned zero results:

- `all:"sampled-counter" AND all:"full law"`;
- `all:"Markov gaps" AND all:"local power"`;
- `all:"renewal process" AND all:"orthogonal score"`;
- `all:"distributional distance" AND all:"local power"`;
- `all:"three-inclusion" AND all:"goodness-of-fit"`.

Crossref searches for the same combinations returned no matching
sampled-counter theorem. They did recover the direct goodness-of-fit
comparators: Agustin--Pena, "A basis approach to goodness-of-fit testing in
recurrent event models," *Journal of Statistical Planning and Inference*
**133**(2), 285--303 (2005), DOI `10.1016/j.jspi.2004.03.022`; and
Titman--Sharples, "A general goodness-of-fit test for Markov and hidden Markov
models," *Statistics in Medicine* **27**(12), 2177--2195 (2008), DOI
`10.1002/sim.3033`. The distributional-distance citation used in the article
is Ryabko--Ryabko, *IEEE Transactions on Information Theory* **56**(3),
1430--1435 (2010), DOI `10.1109/TIT.2009.2039169`; the composite stationary
testing citation is Ryabko, *Statistics* **48**(1), 121--128 (2014), DOI
`10.1080/02331888.2012.719511`.

For the higher-state transfer-map claim, the arXiv query
`all:"minimal realization" AND (all:"transfer function" OR
all:"similarity orbit")` returned four modern records but no reason to treat
the differential quotient as new. Crossref recovered the classical moduli
source M. Hazewinkel, "Moduli and canonical forms for linear dynamical systems
II: The topological case," *Mathematical Systems Theory* **10**, 363--385
(1976), DOI `10.1007/BF01683285`, as well as the established canonical-form
and identifiability literature. Together with Kalman's minimal-realization
uniqueness and Telek--Horvath's minimal MAP formulation, this places the
kernel/rank statement in standard minimal SISO realization quotient geometry.
The Fisher nullspace equality is the corresponding likelihood consequence:
directions tangent to a minimal realization similarity orbit leave every gap
mass, hence the visible likelihood, unchanged. It is therefore not promoted as
a manuscript theorem.

No source returned by the stated arXiv and Crossref searches combines the
sampled-counter complete-word guard with the bounded adjacent-gap score, the
exactly three-inclusion-preserving Markov-gap alternative, and its explicit
calendar-time local power. The integrated novelty claim is restricted to that
combination; general distributional-distance testing, recurrent-event/HMM
goodness-of-fit methodology, LAN, and Gaussian-shift optimality remain cited
background.

## A8-r4 Markov--Palm tangent and omnibus check

Checked 2026-08-07 through the live arXiv Atom API and Crossref. The
model-specific arXiv queries `all:"three inclusion" AND all:omnibus` and
`all:"fixed marginal" AND all:"Markov gap"` each returned zero results. The
broader query `all:"sampled-counter"` returned two lexical false positives,
arXiv:2503.11227v2 and arXiv:2210.14086v3; neither concerns detector gaps,
Palm laws, D-MAPs, or the tangent-space problem. Two additional exact queries
were rate-limited by the API. Crossref searches for "sampled-counter tangent
space", "Markov-Palm effective information", "three inclusion omnibus", and
"fixed marginal Markov gap" returned no model-specific theorem matching the
proposed construction.

The general methodological ground is published and is not claimed here:

- Brock--Kshirsagar, "A chi-square goodness-of-fit test for Markov renewal
  processes," *Annals of the Institute of Statistical Mathematics* **25**,
  643--654 (1973), DOI `10.1007/BF02479406`;
- Skaug--Tjostheim, "A nonparametric test of serial independence based on the
  empirical distribution function," *Biometrika* **80**(3), 591--602 (1993),
  DOI `10.1093/biomet/80.3.591`;
- Ghoudi--Kulperger--Remillard, "A nonparametric test of serial independence
  for time series and residuals," *Journal of Multivariate Analysis* **79**(2),
  191--218 (2001), DOI `10.1006/jmva.2000.1967`;
- Dedecker--Merlevede, "The conditional central limit theorem in Hilbert
  spaces," *Stochastic Processes and their Applications* **108**(2), 229--262
  (2003), DOI `10.1016/S0304-4149(03)00115-7`;
- Ingster--Suslina, *Nonparametric Goodness-of-Fit Testing Under Gaussian
  Models*, Springer (2003), DOI `10.1007/978-0-387-21580-8`.

Accordingly, Hilbert-space central limits, generic serial-independence basis
tests, Rademacher-mixture lower bounds, and finite- or growing-dimensional
Gaussian-sequence minimax envelopes remain attributed background. The
model-specific novelty is restricted to the sampled-counter constraint
`q(0,0)=0`, the resulting Markov--Palm information projection, and the
exchange-local calibration of the weighted interaction statistic. The
oracle's stronger assertion of LAN uniformity on every norm-compact subset of
the full tangent space was not integrated: its direction-dependent truncation
does not provide a common chart or a uniform likelihood remainder, and norm
compactness alone does not make the isonormal limit tight on the index set.
The assertion that finite gap mean alone controls every stationary-record
endpoint likelihood was likewise not integrated; LAN is restricted to the
explicit uniformly close realizing paths or to paths carrying an explicit
endpoint-negligibility hypothesis. Absence from these searches is a bounded
novelty check, not proof of universal absence from the literature.

## A8-r5 growing-layer and ellipsoid boundary check

Checked 2026-08-07 through the live arXiv Atom API, Crossref, and OpenAlex.
The model-specific arXiv queries `all:"sampled-counter" AND
all:"Markov-Palm"` and `all:"weighted Helmert" AND all:"Gaussian
approximation"` each returned `opensearch:totalResults=0`.  The query
`all:"Yurinskii coupling" AND all:martingale` returned one record,
arXiv:2210.00362v4, Cattaneo--Masini--Underwood, "Yurinskii's Coupling for
Martingales."  Crossref identifies the published article by DOI
`10.1214/25-AOS2538`.  Its Corollary 2.2 is used only as the general coupling
input; the equal-rate Helmert moment calculation, calendar stopping transfer,
exchange-local covariance control, and rare-tail obstruction are the
sampled-counter specialization established here.

The broader arXiv query `all:"Gaussian sequence" AND all:ellipsoid AND
all:minimax` returned eight records, including arXiv:2002.07623v1,
arXiv:1503.08562v2, and arXiv:1406.5387v4.  Crossref and OpenAlex confirmed
Ingster--Suslina, *Nonparametric Goodness-of-Fit Testing Under Gaussian
Models* (2003), DOI `10.1007/978-0-387-21580-8`.  Crossref also confirmed van
der Vaart--Wellner, *Weak Convergence and Empirical Processes*, DOI
`10.1007/978-1-4757-2545-2`, and Bogachev, *Gaussian Measures*, DOI
`10.1090/surv/062`.  Accordingly, compact diagonal ellipsoids, pre-Gaussian
criteria, and Gaussian-sequence minimax envelopes are treated as published
background.  No minimax result was integrated because the proposed tangent
ellipsoid does not specify a uniform chart of probability laws, and the
oracle supplied neither a positivity-compatible global alternative class nor
a transfer theorem and matching lower bound for one.

## A8-r7 initial exchange-point coupling check (corrected below)

Checked 2026-08-08 through the live arXiv Atom API, Crossref, OpenAlex, and
the published sources used in the proof. The following arXiv API queries
returned `opensearch:totalResults=0`:

- `all:"weighted Helmert" AND all:"Gaussian coupling"`;
- `all:"weighted Helmert" AND all:"Gaussian approximation"`;
- `all:"one-dependent" AND all:"Yurinskii"`;
- `all:"Helmert" AND all:"strong approximation"`.

The broad query `all:"Yurinskii coupling"` returned arXiv:2210.00362v4 and
one application paper, but no overlapping-Helmert or sampled-counter theorem.
Crossref searches for "weighted Helmert Gaussian coupling", "overlapping
pair one-dependent Gaussian approximation Yurinskii", and "Helmert strong
approximation growing dimension" returned no theorem matching the
single-connecting-edge block construction. These negative searches are a
bounded novelty check and do not prove universal absence.

The two general probabilistic inputs are published and are cited rather than
claimed as new. Pinelis, "Optimum Bounds for the Distributions of Martingales
in Banach Spaces", *Annals of Probability* **22**(4), 1679--1706 (1994), DOI
`10.1214/aop/1176988477`, supplies the Hilbert-space
Rosenthal--Burkholder moment bound. Cattaneo--Masini--Underwood,
"Yurinskii's Coupling for Martingales", *Annals of Statistics* (2025), DOI
`10.1214/25-AOS2538`, arXiv:`2210.00362v4`, Corollary 2.3, records the
independent-vector Euclidean Yurinskii coupling and attributes its classical
form to Pollard and Le Cam.

The initial audit incorrectly promoted the block argument to sharp sufficiency.
The independent reassessment below retracts that conclusion. Direct
substitution still gives the corrected critical constant: under
`2*x_0*J_N=log(n_N)+2*log(log(n_N))-c+o(1)`, the limit is
`exp(c)/4`, not `4*exp(c)`.

## Independent prior-art and proof reassessment, 2026-08-08

This reassessment used the arXiv Atom API, Crossref, Google Scholar, the zbMATH
Open API as a MathSciNet-style index, Semantic Scholar's reference graph, and
the complete published/arXiv text and bibliography of
Cattaneo--Masini--Underwood (CMU). The arXiv query `all:"Yurinskii coupling"`
returned arXiv:2210.00362v4 and one application paper. The earlier exact
Helmert/one-dependent API queries listed above returned zero results; later API
retries were throttled and are not used as negative evidence. Crossref
confirmed DOI `10.1214/25-AOS2538`, *Annals of Statistics* **53**(5) (2025),
and returned no matching weighted-Helmert renewal theorem. A Google Scholar
query for `"weighted Helmert" "Gaussian coupling"` returned only unrelated
Gauss--Helmert engineering papers; exact follow-ups triggered Scholar's
captcha, so Scholar is recorded as searched but is not used to claim absence.
The zbMATH query for Yurinskii martingale coupling returned CMU; its
phase-type-identifiability query recovered Ryden's classical identifiability
paper and related phase-type work, but no deterministic-reset refinement.

CMU's own reference graph identifies the relevant general predecessors:
Yurinskii (1978), Le Cam (1988), Pollard (2002), Zaitsev (1987),
Dudley--Philipp (1983), Dehling (1983), Belloni--Oliveira (2018), Li--Liao
(2020), and Berthet--Mason (2006). These sources contain the general coupling,
strong-approximation, or dependent-vector machinery. They do not make the
sampled-counter Helmert calculation a new coupling method.

Most importantly, CMU Corollary 2.3 does not follow from the manuscript's old
quantity `beta_N -> 0`. For Euclidean norm it uses
`phi_2(d)^2 = 2d`, and its `beta_{2,2}` includes both the block third moments
and the Gaussian comparison third moments. The block calculation gives

`beta_{2,2} <= C{sqrt(L)d^(3/2)/sqrt(n) + 1/(sqrt(n)S_J)}`,

so the cited corollary requires `d beta_{2,2} -> 0`. The rare-cell term is
therefore `d/(sqrt(n)S_J)`, not merely `1/(sqrt(n)S_J)`. The proposition has
been weakened accordingly: `n S_J^2 -> infinity` is necessary,
`d/(sqrt(n)S_J) -> 0` is sufficient, and the resulting
`4 log log n` second-order window is an explicit open interface.

The requested compact-class extension is not valid from the pointwise tail
display alone. Compactness of parameter labels does not make the `o(1)`
uniform or control `g_j/S_j`: a family can move a finite near-plateau to layer
`j=m`, while every fixed law eventually has the same geometric-polynomial
tail. Adding a uniform tail-ratio remainder, uniform atom-to-tail bounds, and
compact bounds on `(c,a,x)` makes the CMU verification uniform under the same
stronger sufficient condition; that is a direct application, not a tier-raising
theorem. The coupling line is therefore not extended. The manuscript is
positioned instead around its killed-reset D-MAP visible quotient and
similarity-fibre structure, while acknowledging that minimal-realization and
confluent-Prony inputs are established theory.
