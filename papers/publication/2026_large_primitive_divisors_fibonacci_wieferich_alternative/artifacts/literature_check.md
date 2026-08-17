# Literature and Citation Check

Checked 2026-08-17. This article uses only external entries already present
in the audited bibliography of the companion manuscript. The checks below
carry forward that audit's Crossref, official-archive, and full-text results.
No new external citation was added. The companion-manuscript entry was
checked directly against its local title and author line; it has no invented
arXiv identifier, DOI, or URL.

## Cited Entries

| Key | Check used | Status |
|---|---|---|
| `Wall1960FibonacciModm` | Crossref DOI returned *Fibonacci Series Modulo m*, lead author D. D. Wall. | confirmed |
| `Vinson1963RankApparition` | Crossref DOI returned *The Relation of the Period Modulo m to the Rank of Apparition of m in the Fibonacci Sequence*, lead author John Vinson; the official scan confirms pages 37--46. | confirmed |
| `Carmichael1913PrimitiveDivisors` | Crossref DOI returned *On the Numerical Factors of the Arithmetic Forms alpha^n +/- beta^n*, lead author R. D. Carmichael. | confirmed |
| `Yabuta2001PrimitiveDivisorFibonacci` | Crossref DOI and the official Fibonacci Quarterly scan returned *A Simple Proof of Carmichael's Theorem on Primitive Divisors*, lead author Minoru Yabuta. | confirmed |
| `BiluHanrotVoutier2001PrimitiveDivisorsLucas` | Crossref DOI returned *Existence of primitive divisors of Lucas and Lehmer numbers*, lead author Y. Bilu. | confirmed |
| `Lengyel1995OrderFibonacciLucas` | Crossref DOI returned *The Order of the Fibonacci and Lucas Numbers*, lead author T. Lengyel. | confirmed |
| `MedinaRowland2015PRegularity` | Crossref DOI returned *p-Regularity of the p-Adic Valuation of the Fibonacci Sequence*, lead author Luis A. Medina. | confirmed |
| `WebbParberry1969FibonacciPolynomials` | Exact-title Crossref result and the fibotomic reference chain returned *Divisibility Properties of Fibonacci Polynomials*, lead author W. A. Webb. | confirmed |
| `Levy2001FibonacciPolynomials` | Exact-title Crossref result and the fibotomic reference chain returned *The Irreducible Factorization of Fibonacci Polynomials Over Q*, lead author Dan Levy. | confirmed |
| `CameronCountsLundMillerPiechnikWong2022Fibotomic` | Crossref DOI returned *On the properties of fibotomic polynomials*, lead author Cameron Byer. | confirmed |
| `HardyWright2008Introduction` | Exact-title Crossref result returned *An Introduction to the Theory of Numbers*, lead author G. H. Hardy, Oxford University Press. | confirmed |
| `Granville2012PrimitivePrimeFactors` | Crossref DOI returned *Primitive prime factors in second-order linear recurrence sequences*, lead author Andrew Granville. | confirmed |
| `Klaska2018WallConjecture` | Crossref DOI and local full text returned *Donald Dines Wall's Conjecture*, lead author Jiri Klaska. | confirmed |
| `Stewart2013DivisorsLucasLehmer` | Crossref DOI returned *On divisors of Lucas and Lehmer numbers*, lead author Cameron L. Stewart. | confirmed |
| `Hong2025BigPrimitiveDivisors` | Crossref DOI returned *On big primitive divisors of Fibonacci numbers*, lead author Haojie Hong. | confirmed |
| `Kiss1988PrimitiveDivisors` | Crossref DOI returned *Primitive Divisors of Lucas Numbers*, lead author Peter Kiss. Publisher metadata and searchable scan text identify the cited Theorem 2 and its hypotheses. | confirmed metadata; full-text access limitation below |
| `Kiss1987WieferichLucas` | Exact-title/author Crossref search returned no record; the REAL-J archive challenged automated access, MATARKA returned no article hit, OpenAlex was unavailable, and Semantic Scholar was rate-limited. | unverified; retained with explicit claim-level warning |
| `MaZhang2026MinimalPreimages` | Local companion source gives the exact title *Minimal preimages of the Fibonacci rank map: squarefree fibers and weighted covers* and authors Haobo Ma and Wenlin Zhang. | locally confirmed unpublished companion |

## Sourcing Gaps Carried Forward

The claim attributed to `Kiss1987WieferichLucas` is retained because it is
the closest located predecessor to the pointwise alternative. Its metadata
and claim were present in the recovered material, but independent index
verification remains unresolved. The manuscript flags that unresolved status
at the citation site. It does not present the entry as verified.

The full text of the 1988 Kiss chapter was not obtained. The Springer DOI
page exposed only the opening of the abstract, while Google Books exposed
searchable OCR but restricted page images. The searchable text identifies
Theorem 2, its nondegenerate-Lucas-sequence and `0 < lambda < 1` hypotheses,
the positive-proportion conclusion, and the author's statement that the
argument does not decide whether prime bases or exponents are large. The
manuscript uses no OCR-obscured constant.

The other unresolved companion-bibliography keys,
`Wigert1907Divisors` and `HardyRamanujan1917NormalPrimeFactors`, are not cited
and do not appear in this article's bibliography.

## Fabricated Entry Exclusion

The fabricated key `Sanna2016LucasSequences` remains absent. It is neither
cited nor present in `references_local.bib`. The companion audit established
that its claimed journal pages overlap an indexed article by another author
and that no matching Crossref, arXiv, or author-portfolio record exists.

## Novelty Search Boundary

The inherited arXiv, Crossref, and primary-reference-chain searches found no
checked source stating the every-large-index alternative or its conditional
`n^(2-o(1))` corollary. They did identify the two Kiss results discussed in
the manuscript as the closest predecessors. This negative search result is
evidence about the queried corpora, not proof of global priority.

## Primitive Primary-Component Search

The unconditional conclusion that the maximum of
"p^valuation_p(F_n)" over primitive primes is at least "n^(2-o(1))" was
checked separately on 2026-08-17. Searches in Crossref, OpenAlex, and the
official arXiv index used combinations of "primitive prime power",
"primitive prime-power factor", "largest primitive prime power", "Fibonacci",
and "Lucas sequence". Semantic Scholar returned HTTP 429 and supplied no
usable result.

The closest sources located were the three already used in the comparison:
Kiss's 1988 positive-proportion theorem for a large primitive prime-power
factor, Stewart's 2013 every-index lower bound for the greatest prime factor
of a Lucas cyclotomic factor, and Hong's fixed-linear every-index bound for a
primitive prime base. The official arXiv full text of Hong's paper
(2312.04354v2) was searched for prime-power conclusions and contains none.
OpenAlex's citation lists for the Kiss and Stewart works were also inspected;
no citing title or indexed abstract stated an every-index near-quadratic
primitive primary-component theorem.

Crossref additionally returned Dov Jarden's 1963 article *On the Greatest
Primitive Divisors of Fibonacci and Lucas Numbers With Prime-Power
Subscripts* (lead author Dov Jarden, DOI
10.1080/00150517.1963.12431559). The official Fibonacci Quarterly scan was
read. Its "greatest primitive divisor" is the full factor of a term coprime
to all earlier terms, and its results concern monotonicity along prime-power
subscripts; it does not bound a single primitive primary component. No
checked record stated the theorem proved here. As with the earlier novelty
search, this is a documented negative search over the named corpora rather
than a proof of global priority.
