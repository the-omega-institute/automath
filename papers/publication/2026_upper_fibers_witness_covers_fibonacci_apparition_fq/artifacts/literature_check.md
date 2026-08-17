# Literature and Novelty Check

Checked 2026-08-02. The searches below used the public arXiv Atom API
(`export.arxiv.org/api/query`), not a secondary search index. DOI metadata was
cross-checked against the Crossref REST API (`api.crossref.org/works`). An
absence from these searches is evidence about the queried corpus, not a proof
of global priority.

## arXiv API Queries

The API was queried for `"rank of apparition"`, `"order of appearance" AND
Fibonacci`, `"primitive divisor" AND Lucas`, `Erdos-Wintner`, `"average
order" AND Fibonacci`, `"witness cover" AND Fibonacci`, and `Fibonacci AND
apparition AND fiber`, with up to 100 records per query. A subsequent `id_list`
query confirmed the metadata of the specific records cited below.

- Rank/order of appearance: arXiv:2309.14501, *Dynamics of the Fibonacci
  Order of Appearance Map* (published DOI
  `10.1080/00150517.2025.2515497`); arXiv:1606.01715, Stroiński, *On
  Dirichlet Products Evaluated at Fibonacci Numbers*; arXiv:1511.09038,
  Silverman, *Divisor Divisibility Sequences on Tori*. These concern dynamics,
  contraction/counting identities, or general divisibility sequences. None
  states an order theorem for the minimal elements of an apparition fiber.
- Primitive divisors: arXiv:1201.6659 (DOI
  `10.1090/S0025-5718-1995-1284673-6`), arXiv:1211.3107 (DOI
  `10.5802/jtnb.168`), and arXiv:1211.3108 (DOI
  `10.1017/S0305004197002223`) are Voutier's papers on primitive divisors of
  Lucas and Lehmer sequences. The definitive uniform theorem used here is
  Bilu--Hanrot--Voutier, DOI `10.1515/crll.2001.080`; the API returned no
  exact arXiv record for that article.
- Erdős--Wintner: arXiv:2009.05435, *Effective Erdős-Wintner theorems for
  digital expansions*, and arXiv:2512.20882, *Erdős-Wintner theorem for
  linear recurrent bases*. These are digital/numeration analogues, not
  results on prime-factor multiplicities of Fibonacci numbers.
- Novelty phrases: the API returned no entries for `"witness cover" AND
  Fibonacci` or for `Fibonacci AND apparition AND fiber`. It also returned no
  paper giving an asymptotic, normal order, or limiting law for the present
  quantity `#M_n`.

## Exact Classical Citations

- Wall, *Fibonacci Series Modulo m*, DOI
  `10.1080/00029890.1960.11989541`; Vinson, *The Relation of the Period Modulo
  m to the Rank of Apparition of m in the Fibonacci Sequence*, DOI
  `10.1080/00150517.1963.12431578`.
- Carmichael, *On the Numerical Factors of the Arithmetic Forms
  alpha^n +/- beta^n*, DOI `10.2307/1967797` and continuation DOI
  `10.2307/1967798`; Yabuta, *A Simple Proof of Carmichael's Theorem on
  Primitive Divisors*, DOI `10.1080/00150517.2001.12428701`;
  Bilu--Hanrot--Voutier, DOI `10.1515/crll.2001.080`.
- Fulton--Morris, *On Arithmetical Functions Related to the Fibonacci
  Numbers*, DOI `10.4064/aa-16-2-105-110`; Lengyel, *The Order of the
  Fibonacci and Lucas Numbers*, DOI `10.1080/00150517.1995.12429139`.
- Luca--Pomerance, *On the Local Behavior of the Order of Appearance in the
  Fibonacci Sequence*, DOI `10.1142/S1793042114500079`; Cameron et al.,
  *On the Properties of Fibotomic Polynomials*, DOI
  `10.1016/j.aam.2022.102344`.
- Hardy--Ramanujan, *The Normal Number of Prime Factors of a Number n*,
  *Quarterly Journal of Pure and Applied Mathematics* 48 (1917), 76--92
  (no DOI located); Turán, *On a Theorem of Hardy and Ramanujan*, DOI
  `10.1112/jlms/s1-9.4.274`.
- Erdős--Wintner, *Additive Arithmetical Functions and Statistical
  Independence*, DOI `10.2307/2371326`. The theorem concerns limiting
  distributions of additive functions. The function `log #M_n` is not
  additive, so Erdős--Wintner cannot close the present interface without a
  separate theorem controlling primitive-rank windows.

## Novelty Boundary and Residual Interface

The new order statement is combinatorial-arithmetic: after grouping atomic
prime powers by their essential/full support pair, the witness-cover private
coordinates give the exact entropy constant `log(2)/4`. Unconditionally,

`log #M_n >= (log(2)/4) omega(n)^2 + O(1)` as `omega(n) -> infinity`,

and the matching upper bound differs only by
`omega(n) log R(n)`, where `R(n)` is the maximum cardinality of one atomic
rank window. Consequently the paper proves the exact normal and mean orders
under explicitly stated normal-density and mean rank-window sparsity
hypotheses. No located paper contains this witness-cover entropy theorem.

The remaining arithmetic statement, `log R(n)=o(omega(n))` for almost all
`n` (or its mean analogue), is not a consequence of Carmichael/BHV, the
prime-power lifting formulas, Hardy--Ramanujan, Turán, Erdős--Wintner, RH, or
ERH as presently known. Carmichael/BHV supplies at least one primitive prime
in each nonexceptional rank; it gives no upper distribution law for the number
of primitive primes in the rank windows. The manuscript therefore labels
this precise multiplicity assertion as an open interface and does not present
it as proved.

## Follow-up Check for the Fibotomic Rank-Entropy Bound

Checked 2026-08-03. The arXiv Atom API was queried for fibotomic, rank of
apparition AND Fibonacci, order of appearance AND Fibonacci, primitive prime
divisors AND Fibonacci, number of primitive divisors AND Fibonacci, prime
factors AND fibotomic, and primitive part AND Fibonacci. Crossref and OpenAlex
were queried independently for the corresponding bibliographic phrases. No
returned record states the pointwise estimate
\[
 a(d)\leq\left(\frac{\log\varphi}{2}+o(1)\right)
 \frac{\phi_{\rm E}(d)}{\log d},
\]
the fibotomic entropy inequality from which it follows, the induced bound for
the visible maximum \(A^*(n)\), or either weighted estimate for
\(\sum\omega(n)\log A^*(n)\).

The full texts of arXiv:2009.03345 and arXiv:1606.01715 were checked.
Byer--Dvorachek--Eckard--Harrington--Wise--Wong prove the fibotomic
polynomial factorization used as an input, but do not derive an exact-rank
prime-count entropy bound. Stroiński's Theorem 7 proves only the already-cited
cumulative estimate
\[
 \limsup_{x\to\infty}\frac{\log x}{x^2}
 \#\{p:\alpha(p)\leq x\}
 \leq\frac{3\log\varphi}{2\pi^2}.
\]
That cumulative conclusion remains attributed to Stroiński and is not claimed
as a new theorem here.

Jarden's original one-page article was retrieved from the Fibonacci Quarterly
archive and read in full. Its exact metadata are D. Jarden, *Any Lucas Number
\(L_{5p}\), for Any Prime \(p>5\), Has at Least Two Distinct Primitive Prime
Divisors*, *The Fibonacci Quarterly* 6 (1968), no. 6, 407, DOI
10.1080/00150517.1968.12431197. The paper supplies the two primitive Lucas
prime divisors; the present manuscript separately proves that each has
Fibonacci rank \(10p\) before using it in the weighted lower bound.

The absence of a match in these searches is not a proof of global priority.
It is the stated evidence for the novelty classification used in this
revision.

## Independent Recheck for the Weighted Visible-Maximum Target

Checked 2026-08-08. This recheck queried the arXiv Atom API (up to 100
records per query), Crossref, Google Scholar, and zbMATH Open, and inspected
the full text and reference list of arXiv:1606.01715 together with Crossref's
46-item reference list for Bilu--Hanrot--Voutier. Searches covered Fibonacci
rank/order of appearance, primitive-divisor counts and average orders,
fibotomic prime factors, and exact-rank multiplicities.

The reference-chain check found an important predecessor to state explicitly.
Kiss, *Primitive Divisors of Lucas Numbers* (1988), proves an asymptotic for
the accumulated logarithmic mass of primitive parts and deduces the cumulative
`x^2/log x` upper-bound scale for the number of distinct primitive primes.
Stroinski's Theorem 7 gives the explicit limsup constant on that scale. A
second Kiss paper (1990) averages reciprocal sums of primitive divisors; it is
not an average theorem for their number. The manuscript now credits this
boundary explicitly.

Source-access note (2026-08-15): the full text of Kiss's 1988 chapter was not
obtained. The Springer DOI page exposed only the opening of the abstract and
the chapter PDF required access; Google Books exposed a searchable scan but
restricted the page images. The scan's searchable OCR identifies the relevant
result as Theorem 2 and verifies its hypotheses: a nondegenerate Lucas
sequence, a real parameter `0 < lambda < 1`, and sufficiently large `x`. It
defines the set of indices `n <= x` for which `R_n` has a primitive prime-power
factor exceeding `n^(2-lambda)` and gives a positive linear lower bound for
that set. The following page explicitly says that the result does not decide
whether the prime bases or the exponents are large. The comparison in Remark
6.7 uses only these verifiable publisher and searchable-scan data; it does not
present the chapter as having been read in full or use the OCR-obscured exact
density constant.

Bilu--Hanrot--Voutier proves existence for all Lucas and Lehmer indices above
30 and classifies the defective cases below 31. In the present Fibonacci
argument it supplies existence of one exact-rank prime at the required
nonexceptional indices. It supplies no upper distribution law for
`a(d) = #Pi_alpha(d)`.

No located source proves, or readily implies,
`sum_{n<=x} omega(n) log A*(n) = O(x (log log x)^2)`. In particular, Kiss and
Stroinski control cumulative counts or logarithmic mass, Sanna counts primes
whose rank is divisible by a fixed integer rather than primes of one exact
rank, and modern large-primitive-divisor results control the size of at least
one primitive divisor rather than the multiplicity of an exact-rank class.
The missing input is an unconditional upper-distribution estimate for
`log #Pi_alpha(d)` along divisor maxima; the primitive-part size and
congruence restrictions alone do not provide it.

## Deep Exploration Check: Exact Support Spectra

Checked 2026-08-08. Fresh queries were sent to the arXiv Atom API, Crossref,
Semantic Scholar, and zbMATH Open for Fibonacci ranks of apparition, minimal
generators, minimal covers, connected hypergraphs, split graphs, primitive
divisors, and strong divisibility sequences. Semantic Scholar's keyword-search
endpoint returned HTTP 429 from the shared address, so the three nearest known
papers were checked there by DOI instead. The API identified Hearne--Wagner,
*Minimal Covers of Finite Sets* (1973), Bilu--Hanrot--Voutier, *Existence of
Primitive Divisors of Lucas and Lehmer Numbers* (2001), and Renault, *The
Period, Rank, and Order of the $(a,b)$-Fibonacci Sequence Mod $m$* (2013).

The nearest combinatorial papers are Hearne--Wagner's enumeration of minimal
covers, Royle's correspondence with split graphs, and the later split-graph
asymptotics of Bender--Richmond--Wormald and Troyka. The nearest arithmetic
papers are Fulton--Morris and Lengyel on prime-power ranks, Bilu--Hanrot--
Voutier on defective primitive-divisor indices, and Renault on the lcm rank
identity for generalized Fibonacci sequences. The searches found no paper
combining those inputs to classify the support sizes of minimal elements in a
fixed Fibonacci apparition fiber, no extremal atomic-product formula, and no
connected endpoint dichotomy involving the oriented defective rank $6$.

Six candidates were compared on a five-point scale `(reach, novelty, value)`:

- exact total/connected support spectra and the extremal slice: `(5,4,5)`;
- exact realization criteria for covers meeting the even exceptional supports:
  `(3,4,4)`;
- support-refined polynomial connected-factorization identities: `(5,2,2)`;
- transfer of the full witness-cover package to general Lucas sequences:
  `(3,3,4)`;
- complete connected four-coordinate kernel classification: `(2,4,4)`;
- unconditional resolution of the rank-window sparsity alternatives:
  `(1,5,5)`.

The first candidate was selected. The third is a routine grading of the
existing partition formula; the fourth needs a recurrence-specific atomic and
defective-index analysis; the fifth is the manuscript's explicit high-support
open project; and the sixth still needs arithmetic dispersion unavailable in
the cited literature. The second remains plausible but requires a separate
coprime slot classification for covers using ranks $2$, $6$, and $12$.

## Tier-up Recheck: Exact-rank Fiber Multiplicity

Checked 2026-08-10 before the present proof attempt. The arXiv Atom API was
queried for rank/order of appearance together with Fibonacci and for primitive
divisors of Lucas sequences. Crossref was queried independently for exact-rank,
primitive-divisor multiplicity, and average-order phrases. Semantic Scholar's
keyword endpoint again returned HTTP 429, so Bilu--Hanrot--Voutier and the
nearest DOI-bearing records were resolved through the paper-by-DOI endpoint.
The zbMATH Open syntax search covered titles, abstracts, and reviews containing
Fibonacci/Lucas, rank of apparition, primitive divisors, and average order.
The API terms were accepted in the session before querying its document
endpoint.

The closest overlooked paper is P. Kiss, *On rank of apparition of primes in
Lucas sequences*, Publ. Math. Debrecen 36 (1989), 147--151, DOI
10.5486/pmd.1989.36.1-4.17. Its reviewed results bound averages of
$r(p)/p$, including sums over primes with $r(p)\le x$; they do not bound the
cardinality of a growing exact fiber
$a(d)=\#\{p:\alpha(p)=d\}$. Kiss's 1988 primitive-divisor paper and 1990
prime-power paper are also adjacent, but address primitive parts, large
primitive factors, or reciprocal sums rather than upper distribution of
$a(d)$.

No returned record states an almost-all estimate for the weighted minimal-cover
partition function
\[
 \sum_{\mathcal C}\prod_{S\in\mathcal C}a(n_S)
\]
on odd $n$, or an estimate implying that its logarithmic excess over the
unweighted cover count is $o((\log\log n)^2)$. This weighted rank-pure estimate
is a necessary positive-density interface in the manuscript. It is not
sufficient: ladder atoms can occur even at odd squarefree indices, as
$\alpha(13)=7$ and $\alpha(13^2)=91$ show. The previous maximum-window
condition $\log R(n)=o(\omega(n))$ remains sufficient but is not presented as
necessary. Database non-detection is not a proof of priority.

## Large Primitive Divisor / Fibonacci-Wieferich Alternative

Checked 2026-08-15 before adding the theorem. The audit tested the pointwise
statement

`no Fibonacci-Wieferich prime => P_prim(F_n) >= n^(2-o(1))`

and the equivalent alternative saying that every sufficiently large rank has
either a primitive divisor at least `n^(2-epsilon)` or a repeated primitive
divisor at that exact rank. Searches covered arXiv, Crossref, Semantic Scholar,
and zbMATH Open under the vocabularies primitive divisor, primitive part,
characteristic part, greatest/largest primitive factor, Wall--Sun--Sun,
Fibonacci-Wieferich, and Wieferich-type Lucas divisor. The relevant primary
texts and citation chains were then checked.

- Hong, *On big primitive divisors of Fibonacci numbers*, arXiv:2312.04354v2,
  DOI `10.1007/s11139-025-01068-9`, proves the explicit fixed-linear-exclusion
  theorem: for every fixed positive integer `kappa`, sufficiently large `F_n`
  has a primitive divisor outside `n+-1,...,kappa*n+-1`, hence at least
  `(kappa+1)n-1`. It contains no Wall--Sun--Sun, Fibonacci-Wieferich, or
  repeated-primitive-factor alternative.
- Stewart, *On divisors of Lucas and Lehmer numbers*, arXiv:1008.1274, DOI
  `10.1007/s11511-013-0105-y`, was read together with its account and reference
  chain for Stewart's 1977 paper and the 1981 and 1983 continuations. Its
  unconditional greatest-prime-factor theorem has size
  `n*exp(log(n)/(104*loglog(n)))`; the earlier Stewart papers supply primitive
  existence, multiplicity, or growing-prime-factor estimates. No inspected
  theorem or recorded corollary links the absence of exceptional rank lifting
  to a pointwise exponent `2-o(1)`.
- Granville, *Primitive prime factors in second-order linear recurrence
  sequences*, arXiv:1212.6306, DOI `10.4064/aa155-4-7`, was checked in full,
  including the source of Corollaries 3 and 4. Those corollaries give the
  classical primitive-part input used here: characteristic primes occur in the
  Lucas cyclotomic factor with their full exponents, and the remaining factor
  is at most one prime dividing the index (apart from the excluded indices 6
  and 12). Granville studies odd primitive multiplicity and explicitly leaves
  the Fibonacci parity case open; he does not state the present size/lifting
  alternative.
- Klaska, *Donald Dines Wall's Conjecture*, DOI
  `10.1080/00150517.2018.12427720`, was read in full, along with the later
  Wall-conjecture discussion in Trojovska, DOI `10.3390/math8050773`. These
  survey the equivalent exceptional-lifting criteria, computational searches,
  and applications to perfect powers and Fermat's Last Theorem. Neither
  records a conditional near-quadratic largest primitive divisor.

The audit found one close predecessor that must be distinguished explicitly.
P. Kiss, *Wieferich-type prime divisors of Lucas numbers*, *Matematikai Lapok*
34 (1987), 93--98, proves that if the greatest primitive divisor of a Lucas
term is below `n^(1+delta)` for almost all indices, for a fixed
`0 < delta < 1`, then a positive-density set of indices has a term divisible
by a Wieferich-type prime. This is a global almost-all implication; the
Wieferich-type divisor need not be primitive at the displayed index. It gives
neither an every-large-index alternative nor the contrapositive
`P_prim(F_n) >= n^(2-o(1))` under the nonexistence of Fibonacci-Wieferich
primes.

Verdict: no checked source records the proposed pointwise alternative or its
conditional `n^(2-o(1))` corollary. The theorem survives this literature audit.
This negative result is evidence from the stated corpora and primary citation
chains, not a proof of global priority; the Kiss theorem is cited in the
manuscript as the closest located precursor.

## Squarefree Minimal-Fiber Criterion

Checked 2026-08-17 before adding the theorem. The proposed statement was the
equivalence between the absence of nonsquarefree elements of `M_n` and the
three explicit ladder exclusions

`6 does not divide n`, `nu_5(n) <= 1`, and
`alpha(p) does not divide n/p^nu_p(n)` for `p | n`, `p not in {2,5}`,

together with the assertion that every failure already produces a
nonsquarefree minimal preimage with at most two prime factors.

The arXiv Atom API was queried for the exact phrase combinations `minimal
squarefree preimages` and Fibonacci, `rank of apparition` and squarefree,
`order of appearance` and squarefree, `minimal multiplicative covers` and
Fibonacci, and Fibonacci/apparition/fiber. No record was returned. Crossref
queries used the additional vocabularies preimage, inverse image, minimal
elements, fiber, squarefree prime powers, and order of appearance. The nearest
returned works were the following:

- H. Williams, *The Rank of Apparition of a Generalized Fibonacci Sequence*,
  DOI `10.1080/00150517.1975.12430643`;
- P. Kiss and B. M. Phong, *On the Connection Between the Rank of Apparition
  of a Prime p in Fibonacci Sequence and the Fibonacci Primitive Roots*, DOI
  `10.1080/00150517.1977.12430420`;
- C. G. Wagner, *Minimal Multiplicative Covers of an Integer*, DOI
  `10.1016/0012-365X(78)90175-9`;
- the order-of-appearance papers of D. Marques, beginning with *Fixed Points
  of the Order of Appearance in the Fibonacci Sequence*, DOI
  `10.1080/00150517.2012.12427984`; and
- M. Fitzgibbons, M. Javaheri, S. J. Miller, and A. Verga, *Dynamics of the
  Fibonacci Order of Appearance Map*, DOI
  `10.1080/00150517.2025.2515497`.

Crossref and Semantic Scholar paper-by-DOI responses agreed on the titles and
lead authors of the Williams, Kiss, Wagner, and Fitzgibbons records. The
available Kiss abstract concerns congruence conditions for the rank of one
prime. Wagner treats abstract minimal multiplicative covers. The Fitzgibbons
paper and its open problems concern iteration, fixed-point order, and
relatively prime inverse families; its full text had already been checked for
the inverse-dynamics audit above. None of these sources states a criterion for
squarefreeness of every divisibility-minimal element in one exact apparition
fiber. Crossref returned no work whose title or indexed metadata concerned
such minimal fibers.

OpenAlex and the Semantic Scholar keyword endpoint returned HTTP 429 throughout
this check. The zbMATH query syntax attempted in the same session returned HTTP
422. These service failures are not counted as negative search results. The
earlier audits in this file had already searched those indexes and the primary
reference chains for the witness-cover classification, prime-power lifting,
and exact support spectra; no predecessor for the present criterion was found
there. No checked source records either the equivalence or its support-two
rigidity conclusion. This is a bounded priority check, not a proof that no
unindexed result exists.

## Bibliographic Integrity Audit

Checked 2026-08-15. This section is appended to, and does not replace, the
earlier novelty searches and sourcing-gap records above. In particular, the
existing full-text access notes for the Mignotte material and for Kiss's 1988
chapter remain part of this record.

### Scope and method

The live `references_local.bib` contained 49 entries before correction. The
ignored stale source snapshot `tmp/build_A7_r3_src/references_local.bib`
contained 37 entries, all of whose keys also occurred in the live file. Thus
the inventory contained 86 physical entry copies and 49 unique entries. There
was no current `submission_bundle` or other bibliography file. The stale
snapshot was included in the inventory and then removed with the other stale
scratch material after its one citation to the fabricated entry was reviewed.

All 32 entries that already carried a DOI were resolved directly through the
Crossref `/works/{doi}` endpoint. Each returned HTTP 200. The returned title
and lead author are recorded below; resolution alone was not treated as
confirmation. The 17 entries without a DOI were searched by exact title and
author in Crossref and, where useful, checked against arXiv, the official
Fibonacci Quarterly or Acta Arithmetica archive, the Journal of Integer
Sequences full text, Open Library, ORCID, or the relevant publisher record.

Status vocabulary follows the requested three-way classification. The deleted
Sanna item is classified as `unverified` and additionally marked as
demonstrably fabricated; deletion is an action, not a fourth verification
class.

### Per-entry verification table

Abbreviations: `CR` = Crossref, `S2` = Semantic Scholar, `OA` = OpenAlex,
`FQ` = official Fibonacci Quarterly scan, `AA` = official Acta Arithmetica
record, and `JIS` = official Journal of Integer Sequences full text.

| Key | DOI in entry | Verification result (returned title and lead author, or exact-title result) | Classification / action |
|---|---|---|---|
| `Wall1960FibonacciModm` | `10.1080/00029890.1960.11989541` | CR: *Fibonacci Series Modulo m*, D. D. Wall; S2 paper-by-DOI agreed. | confirmed |
| `Vinson1963RankApparition` | `10.1080/00150517.1963.12431578` | CR: *The Relation of the Period Modulo m to the Rank of Apparition of m in the Fibonacci Sequence*, John Vinson, pp. 37--46. The 10-page FQ scan begins at p. 37 and ends at p. 46. | confirmed after metadata correction: pages `37--45` -> `37--46` |
| `Yabuta2001PrimitiveDivisorFibonacci` | `10.1080/00150517.2001.12428701` | CR: *A Simple Proof of Carmichael's Theorem on Primitive Divisors*, Minoru Yabuta. The FQ scan prints the same title and Minoru Yabuta. | confirmed after metadata correction: author `Yutaka Yabuta` -> `Minoru Yabuta`; title *A simple proof of Carmichael's primitive divisor theorem for the Fibonacci sequence* -> *A simple proof of Carmichael's theorem on primitive divisors* |
| `BiluHanrotVoutier2001PrimitiveDivisorsLucas` | `10.1515/crll.2001.080` | CR: *Existence of primitive divisors of Lucas and Lehmer numbers*, Y. Bilu. The CR schema stores 2001 as volume and 539 as issue; the conventional journal citation uses 539 as the journal number, so no change was made. | confirmed |
| `BugeaudLucaMignotteSiksek2005FewPrimeDivisors` | `10.3792/pjaa.81.17` | CR: *On Fibonacci numbers with few prime divisors*, Yann Bugeaud; Project Euclid journal/volume/issue data agree. | confirmed |
| `Lengyel1995OrderFibonacciLucas` | `10.1080/00150517.1995.12429139` | CR: *The Order of the Fibonacci and Lucas Numbers*, T. Lengyel. | confirmed |
| `SunSun1992FibonacciFLT` | none | Exact-title CR result and AA record: DOI `10.4064/aa-60-4-371-388`, *Fibonacci numbers and Fermat's last theorem*, sole author Zhi-Wei Sun, 60(4), 371--388. | confirmed after metadata correction: authors `Zhi-Hong Sun and Zhi-Wei Sun` -> `Zhi-Wei Sun` |
| `FultonMorris1969ArithmeticalFunctions` | `10.4064/aa-16-2-105-110` | CR and AA: *On arithmetical functions related to the Fibonacci numbers*, John Fulton and William Morris, 16(2), 105--110. | confirmed after metadata correction: `W. Fulton and J. Morris` -> `John Fulton and William Morris` |
| `Sperner1928Subsets` | none | Exact-title CR result: DOI `10.1007/bf01171114`, *Ein Satz uber Untermengen einer endlichen Menge*, Emanuel Sperner, 27(1), 544--548 (the index supplies the umlaut in *uber*). | confirmed |
| `Wigert1907Divisors` | none | Exact-title/author CR search returned other Wigert papers (1916, 1924, 1927), not this item; OA was unavailable, S2 was rate-limited, zbMATH failed, and the LIBRIS endpoint was unreachable. | unverified; retained unchanged |
| `HardyRamanujan1917NormalPrimeFactors` | none | Exact-title/Hardy CR search returned unrelated works; OA was unavailable, S2 was rate-limited, and zbMATH failed. The existing audit above records the standard 48 (1917), 76--92 citation, but the intended independent index redundancy was not obtained in this run. | unverified; retained unchanged |
| `Turan1934HardyRamanujan` | `10.1112/jlms/s1-9.4.274` | CR: *On a Theorem of Hardy and Ramanujan*, Paul Turan, 1934, s1-9(4), 274--276. | confirmed |
| `ErdosWintner1939Additive` | `10.2307/2371326` | CR: *Additive Arithmetical Functions and Statistical Independence*, Paul Erdos; S2 paper-by-DOI agreed on title, lead author, and year. | confirmed |
| `Stroinski2016AlphaContraction` | none | arXiv `1606.01715`: *On Dirichlet Products Evaluated at Fibonacci Numbers*, Uwe Stroinski, submitted 2016-06-06; the locally retained full-text extract agrees. | confirmed |
| `Trojovska2020PeriodicPoints` | `10.3390/math8050773` | CR: *On Periodic Points of the Order of Appearance in the Fibonacci Sequence*, Eva Trojovska, 2020, 8(5), article 773. | confirmed |
| `LucaPomerance2014LocalBehavior` | `10.1142/S1793042114500079` | CR: *On the local behavior of the order of appearance in the Fibonacci sequence*, Florian Luca; S2 paper-by-DOI agreed. | confirmed |
| `FitzGibbonsJavaheriMillerVerga2025Dynamics` | `10.1080/00150517.2025.2515497` | CR: *Dynamics of the Fibonacci Order of Appearance Map*, Molly Fitzgibbons, 2025. | confirmed |
| `CameronCountsLundMillerPiechnikWong2022Fibotomic` | `10.1016/j.aam.2022.102344` | CR: *On the properties of fibotomic polynomials*, Cameron Byer, 2022, volume 138, article 102344; the existing full-text extract agrees. | confirmed |
| `Jarden1968LucasTwoPrimitive` | `10.1080/00150517.1968.12431197` | CR: *Any Lucas Number L5p, for any Prime p > 5, Has at Least Two Distinct Primitive Prime Divisors*, Dov Jarden; the FQ full text previously checked above agrees. | confirmed |
| `Carmichael1913PrimitiveDivisors` | `10.2307/1967797` | CR: *On the Numerical Factors of the Arithmetic Forms alpha^n +/- beta^n*, R. D. Carmichael, 1913, 15(1/4), starting p. 30. | confirmed |
| `Halton1966DivisibilityFibonacci` | none | Exact-title CR result: DOI `10.1080/00150517.1966.12431357`, *On the Divisibility Properties of Fibonacci Numbers*, John H. Halton, 4(3), 217--240. | confirmed |
| `Sanna2016LucasSequences` | none | Exact title + Carlo Sanna returned no CR or arXiv record; it is absent from Sanna's ORCID and 2015--2020 CR portfolio. The claimed IJNT 15(2) pages 233--243 fall inside the indexed Matsuda article at 213--250. The nearest real Sanna/Lucas item is the unrelated *The p-Adic Valuation of Lucas Sequences*, FQ 54(2) (2016), 118--124, DOI `10.1080/00150517.2016.12427821`. OA was unavailable, S2 returned 429, and zbMATH failed. | unverified; demonstrably fabricated and deleted |
| `Sanna2022RankDivisibility` | `10.1142/S1793042122501093` | CR: *On the divisibility of the rank of appearance of a Lucas sequence*, Carlo Sanna, 2022, 18(10), 2145--2156. | confirmed |
| `Sanna2024IndexAppearance` | `10.1007/s11139-023-00811-4` | CR: *On the index of appearance of a Lucas sequence*, Carlo Sanna, 2024, 63(4), 1199--1223. | confirmed |
| `CeraDaConceicao2026PrimeDensities` | none | arXiv `2604.20014`: *Explicit Prime Densities for the Rank of Appearance in Lucas Sequences*, Joaquim Cera Da Conceicao, submitted 2026-04-21. | confirmed |
| `Marques2012OrderAppearance` | none | Exact-title CR result: DOI `10.1080/00150517.2012.12427984`, *Fixed Points of the Order of Appearance in the Fibonacci Sequence*, Diego Marques, 50(4), 346--351; the Luca--Tron reference list independently gives 346--351. | confirmed after metadata correction: pages `346--352` -> `346--351` |
| `LucaTron2015SelfFibonacciDivisors` | `10.1007/978-1-4939-3201-6_6` | CR: *The Distribution of Self-Fibonacci Divisors*, Florian Luca, 2015, pp. 149--158. | confirmed |
| `Renault2013PeriodRankOrder` | `10.4169/math.mag.86.5.372` | CR: *The Period, Rank, and Order of the (a,b)-Fibonacci Sequence Mod m*, Marc Renault, 2013, 86(5), 372--380. | confirmed |
| `MedinaRowland2015PRegularity` | `10.1080/00150517.2015.12428269` | CR: *p-Regularity of the p-Adic Valuation of the Fibonacci Sequence*, Luis A. Medina, 2015, 53(3), 265--271. | confirmed |
| `Kiss1988PrimitiveDivisors` | `10.1007/978-94-015-7801-1_4` | CR: *Primitive Divisors of Lucas Numbers*, Peter Kiss, 1988, pp. 29--38. The separate full-text access limitation recorded above remains in force. | confirmed |
| `Kiss1989RankApparition` | `10.5486/pmd.1989.36.1-4.17` | CR: *On rank of apparition of primes in Lucas sequences*, Peter Kiss, volume 36(1--4), 147--151. CR reports the 2022 retroactive online registration date; the original issue and DOI identify the 1989 publication, so the bibliography year was retained. | confirmed |
| `Granville2012PrimitivePrimeFactors` | `10.4064/aa155-4-7` | CR: *Primitive prime factors in second-order linear recurrence sequences*, Andrew Granville, 2012, 155(4), 431--452. | confirmed |
| `Kiss1987WieferichLucas` | none | Exact-title/author CR search returned Kiss's 1988 chapter as the nearest item, not this article. The REAL-J archive presented an automated-access challenge, MATARKA returned no article hit, OA was unavailable, S2 was rate-limited, and zbMATH failed. | unverified; retained unchanged |
| `Stewart2013DivisorsLucasLehmer` | `10.1007/s11511-013-0105-y` | CR: *On divisors of Lucas and Lehmer numbers*, Cameron L. Stewart, 2013, 211(2), 291--314. | confirmed |
| `Klaska2018WallConjecture` | `10.1080/00150517.2018.12427720` | CR: *Donald Dines Wall's Conjecture*, Jiri Klaska, 2018, 56(1), 43--51; the locally retained full text agrees. | confirmed |
| `Hong2025BigPrimitiveDivisors` | `10.1007/s11139-025-01068-9` | CR: *On big primitive divisors of Fibonacci numbers*, Haojie Hong, 2025, 67(1), article 20. | confirmed |
| `BrillhartMontgomerySilverman1988Tables` | `10.1090/S0025-5718-1988-0917832-6` | CR: *Tables of Fibonacci and Lucas factorizations*, John Brillhart, 1988, 50(181), 251--260. | confirmed |
| `LovaszPlummer1986MatchingTheory` | none | Open Library exact query: *Matching Theory*, Lovasz and Plummer, first published 1986; title/authors/year agree. Publisher/series data did not receive a second independent API check because the other indexes were unavailable. | confirmed |
| `Stanley2012EnumerativeCombinatoricsI` | none | CR exact-title search returned Richard P. Stanley's Cambridge *Enumerative Combinatorics* records, including the Cambridge DOI `10.1017/CBO9781139058520`; title, author, publisher, series, and second-edition identity agree (online metadata uses 2011, print edition 2012). | confirmed |
| `Tenenbaum2015AnalyticProbabilistic` | none | CR exact-title result: DOI `10.1090/gsm/163`, *Introduction to Analytic and Probabilistic Number Theory*, Gerald Tenenbaum, 2015, Graduate Studies in Mathematics 163. | confirmed |
| `HardyWright2008Introduction` | none | CR exact-title result: DOI `10.1093/oso/9780199219858.001.0001`, *An Introduction to the Theory of Numbers*, G. H. Hardy, Oxford University Press, 2008. | confirmed |
| `HearneWagner1973MinimalCovers` | `10.1016/0012-365X(73)90141-6` | CR: *Minimal covers of finite sets*, T. Hearne, 1973, 5(3), 247--251. | confirmed |
| `Wagner1978MultiplicativeCovers` | `10.1016/0012-365X(78)90175-9` | CR: *Minimal multiplicative covers of an integer*, Carl G. Wagner, 1978, 24(1), 87--94. | confirmed |
| `WebbParberry1969FibonacciPolynomials` | none | Exact-title CR result: DOI `10.1080/00150517.1969.12431125`, *Divisibility Properties of Fibonacci Polynomials*, W. A. Webb, 1969, volume 7, 457--463; the fibotomic full-text reference list agrees. | confirmed |
| `Levy2001FibonacciPolynomials` | none | Exact-title CR result: DOI `10.1080/00150517.2001.12428710`, *The Irreducible Factorization of Fibonacci Polynomials Over Q*, Dan Levy, 2001, 39(4), 309--319; the fibotomic full-text reference list agrees. | confirmed |
| `Royle2000SetCoversSplitGraphs` | none | JIS full text: *Counting Set Covers and Split Graphs*, Gordon F. Royle, volume 3 (2000), issue 2, Article 00.2.6. | confirmed |
| `KanteLimouzyMaryNourine2014DominatingSets` | `10.1137/120862612` | CR: *On the Enumeration of Minimal Dominating Sets and Related Notions*, Mamadou Moustapha Kante, 2014, 28(4), 1916--1929. | confirmed |
| `BenderRichmondWormald1985ChordalSplit` | `10.1017/S1446788700023077` | CR: *Almost all chordal graphs split*, E. A. Bender, 1985, 38(2), 214--221. | confirmed |
| `Troyka2019SplitGraphs` | `10.37236/8278` | CR: *Split Graphs: Combinatorial Species and Asymptotics*, Justin M. Troyka, 2019, 26(2), Paper 2.42. | confirmed |

### Corrections and deletion decisions

Five entries were corrected, exactly as shown in the table: Vinson's ending
page, Yabuta's given name and title, the swapped Fulton/Morris identities, the
Sun paper's authorship, and Marques's ending page. No citing sentence was
changed: each corrected entry still identifies the same work and supports the
same claim for which it was cited.

One entry was deleted: `Sanna2016LucasSequences`. The live `main.tex` and
`supplement.tex` contain no citation to that key. The stale source snapshot had
one source-level citation in its old introduction, in a sentence jointly
attributing growth and fixed-point behavior to Sanna and Marques. That stale
snapshot was removed rather than retained or silently retargeted. No key was
substituted. The current paper independently uses the verified
`Sanna2022RankDivisibility` and `Sanna2024IndexAppearance` records only for the
precise distribution statements they actually contain, and uses the verified
Marques record for the fixed-point classification. Thus the per-citation
decisions are: live main, no site; live supplement, no site; stale snapshot,
remove the obsolete sentence with the stale tree and do not substitute; build
auxiliary copies, derived from that one stale source site and removed with the
scratch tree.

### Unverified entries and exact searches

Three non-fabricated entries remain unchanged and are classified as
unverified: `Wigert1907Divisors`, `HardyRamanujan1917NormalPrimeFactors`, and
`Kiss1987WieferichLucas`. Their exact searches and outcomes are stated in their
table rows. These are respectively a pre-DOI classic, another pre-DOI classic,
and an obscure non-DOI journal article. Service failures are not treated as
negative evidence.

### Audit limitations

- OpenAlex returned an explicit daily-budget/rate-limit error on the first
  request, so none of the 49 unique entries received OpenAlex redundancy.
- Semantic Scholar's paper-by-DOI endpoint succeeded for Wall,
  Erdos--Wintner, and Luca--Pomerance, but subsequent DOI and title requests
  returned HTTP 429. The other 46 entries therefore received no S2 redundancy.
- zbMATH's structured-search endpoint failed on this network and was dropped;
  no conclusion is drawn from that failure.
- Google Books returned HTTP 429, CORE returned HTTP 429, and the LIBRIS
  endpoint could not be reached. These failures affected only attempted
  supplementary checks and are not negative evidence.
- Crossref was available throughout: all 32 pre-existing DOIs resolved with
  matching work identity, and the exact-title search completed for all 17
  no-DOI entries. Cross-source redundancy was therefore not achieved as
  intended for most entries. Official archive/full-text checks were used for
  the discrepancies and for the arXiv/JIS records, but 46 entries were checked
  against fewer independent indexes than intended.
