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
