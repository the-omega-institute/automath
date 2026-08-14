# Named-problem and tier-route audit

Checked 2026-08-14. Searches used the arXiv Atom/API corpus, Crossref, zbMATH
Open, Semantic Scholar paper-by-DOI records, citation chains, and primary PDFs.
Semantic Scholar keyword search returned HTTP 429 during part of the check;
the affected known papers were resolved by DOI or primary PDF. Database
non-detection is not a proof that a problem is open, so the status statements
below say exactly what later evidence and searches established.

## 1. Bugeaud--Luca--Mignotte--Siksek exact divisor-count conjecture

Y. Bugeaud, F. Luca, M. Mignotte, and S. Siksek, "On Fibonacci
numbers with few prime divisors," *Proc. Japan Acad. Ser. A* 81 (2005),
17--20, DOI `10.3792/pjaa.81.17`, Section 5, Conjecture 5.1, p. 20.
Author PDF: <https://irma.math.unistra.fr/~bugeaud/travaux/OmegaDef.pdf>.

Exact statement:

> "Conjecture 5.1. \(\omega(F_n)\gg \log n\) holds for all composite
> positive integers \(n\)."

No resolution was located in the indexed citation chain through 2026. The
2005 paper proves only a weaker almost-all lower bound. In this manuscript,
`prop:blms-obstructs-mean-window` proves that the conjecture would make (H2)
false. The new `prop:sharp-cumulative-data-obstruction` proves a complementary
limitation: since \(\omega(F_n)=\sum_{d\mid n}a(d)\), total mass alone does not
control the weighted cover polynomial. What is missing is localization of
that mass among the exact ranks, plus an upper bound for the non-rank-pure
sector. The manuscript does not solve this conjecture.

## 2. Cubre--Rouse prime-rank problem

P. Cubre and J. Rouse, "Divisibility properties of the Fibonacci entry
point," *Proc. Amer. Math. Soc.* 142 (2014), 3771--3785, DOI
`10.1090/S0002-9939-2014-12269-6`, arXiv:1212.6221, Section 1, p. 3771.

Exact statement:

> "It is not presently known if there are infinitely many primes \(p\) for
> which \(Z(p)=p+1\)."

No unconditional resolution was located. Sanna's 2024 fixed-index theorem
(DOI `10.1007/s11139-023-00811-4`) assumes GRH and does not settle this moving
diagonal. Here \(Z=\alpha\), so the question is literally about exact-rank
primes, but it samples the relation \(d=p+1\), not the growing multiplicities
\(a(d)\). The fibotomic entropy theorem gives only an upper bound for a fixed
fiber, and primitive-divisor existence does not force its prime to equal
\(d-1\). A new lower-bound or moving-Chebotarev/sieve input is missing.

## 3. Wall's conjecture / Wall--Sun--Sun primes

J. Klaska, "Donald Dines Wall's Conjecture," *Fibonacci Quarterly* 56
(2018), 43--51, DOI `10.1080/00150517.2018.12427720`, Section 1, p. 43,
quotes D. D. Wall, "Fibonacci Series Modulo m," *Amer. Math. Monthly* 67
(1960), 525--532, DOI `10.1080/00029890.1960.11989541`:

> "The most perplexing problem we have met in this study concerns the
> hypothesis \(k(p^2)=k(p)\). ... we cannot yet prove that \(k(p^2)=k(p)\)
> is impossible."

Klaska calls the problem unresolved; Trojovska (2020, DOI
`10.3390/math8050773`) still states the modern conjectural rank-lifting law
\(z(p^a)=p^{a-1}z(p)\), and 2024 work still studies criteria for exceptional
primes. The manuscript's prime-power lifting formulas and ladder atoms bear
directly on the consequences: an exceptional prime changes the initial
lifting height and the nonsquarefree exact-fiber slice. Those formulas assume
neither existence nor nonexistence of such a prime. The missing input is the
very p-adic congruence \(F_{\alpha(p)}\not\equiv0\pmod {p^2}\).

## 4. Granville's odd-valuation primitive-divisor conjecture

A. Granville, "Primitive prime factors in second-order linear recurrence
sequences," *Acta Arith.* 155 (2012), 431--452, DOI
`10.4064/aa155-4-7`, arXiv:1212.6306, Section 7, p. 451.

Exact statement:

> "We conjecture that for every non-periodic Lucas sequence
> \(\{x_n\}_{n\geq0}\) there exists an integer \(n_x\) such that if
> \(n\geq n_x\) then \(x_n\) has a primitive prime factor that divides it
> to an odd power."

Granville immediately says that the unavailable odd-parameter case includes
the Fibonacci numbers. No resolution was located through 2026; Hong's 2025
result concerns size, not valuation parity. A primitive Fibonacci divisor is
an exact-rank prime, but this conjecture refines the valuation of one such
prime, whereas the weighted cover problem needs the number and distribution
of all of them. The manuscript's radical divisibility discards precisely the
exponent parity that would be needed.

## 5. Standard-object boundary: hypergraph duality

M. M. Kante, V. Limouzy, A. Mary, and L. Nourine, "On the Enumeration
of Minimal Dominating Sets and Related Notions," *SIAM J. Discrete Math.* 28
(2014), 1916--1929, DOI `10.1137/120862612`, p. 1917:

> "It is still open whether there exists an output-polynomial time algorithm
> for the Trans-Enum problem."

A. Mary, "Enumeration of minimal transversals of hypergraphs of bounded
VC-dimension," arXiv:2407.00694v4 (30 Jan 2026), p. 14, gives current-status
evidence and poses the parameterized version as Open Problem 1:

> "Given H and G with VC-dim(H) < k, can we decide in time
> \(f(k)\cdot p(|H|+|G|)\) whether H and G are dual, where f is a
> computable function and p is a polynomial?"

The printed 2014 question and January 2026 revision both record the problem as
open. New
`cor:rank-pure-minimal-transversals` canonically identifies the rank-pure
Fibonacci sector with the minimal transversals of a coordinate-star
hypergraph; on squarefree indices, `cor:canonical-squarefree-slice` identifies
that sector with the minimal squarefree exact preimages of the rank map. This
does not solve Mary's problem: the coordinate-star blow-ups are a very special
class, and general witness covers also carry essential/full-support and
coprimality constraints not present in ordinary transversal enumeration.

## A/B/C/D decision

- A: none of the named problems above is solved. BLMS and Wall are genuinely
  hard arithmetic problems; the current cover machinery exposes consequences
  but supplies no missing distributional or p-adic input.
- B: successful. The paper now maps its weighted sector bijectively to minimal
  transversals of a canonical hypergraph and, for squarefree n, identifies it
  exactly with the standard squarefree slice of \(\alpha^{-1}(n)\).
- C: no honest removable hypothesis was found. (H1), (H2), and (BW) encode
  missing arithmetic rather than proof artifacts; BLMS even contradicts (H2).
- D: successful but elementary. At fixed positive total weight A, the exact
  minimum is \(C_k+A-(2^k-1)\); for \(k\geq3\), equality forces all excess
  mass onto the full support. The extremizer is not claimed Fibonacci-realizable.

The B/D additions materially improve the paper's positioning and close a
converse, but they do not supply a Tier-2 arithmetic theorem. Without a named
problem solution, a realizable sharpness construction, or exact-rank
dispersion, the honest ceiling remains Tier 3 (with a plausible specialist
number-theory/combinatorics venue), not JFA/ETDS/Transactions/Math. Comp.

## 6. FitzGibbons--Javaheri--Miller--Verga inverse-dynamics problems

Checked 2026-08-15 against the four-author final manuscript of M.
FitzGibbons, M. Javaheri, S. J. Miller, and A. Verga, "Dynamics of the
Fibonacci Order of Appearance Map," *The Fibonacci Quarterly* (published
online 31 December 2025), DOI `10.1080/00150517.2025.2515497`. The author
manuscript is dated 18 April 2025. Its first unnumbered problem asks:

> "Is it true that for every \(k\geq1\) there exist infinitely many
> relatively prime integers whose fixed point order is \(k\)?"

After Theorem 3.3, the second unnumbered problem is stated as:

> "One conjectures that \(\Omega_x\) contains infinitely many relatively
> prime elements for every fixed point \(x>5\)."

The earlier arXiv version `arXiv:2309.14501v1` has three authors and does not
contain these formulations, so it is not the source used for the wording.
The constructions in the published manuscript prove infinitude using
multiples of a fixed seed or of the fixed point; they do not produce an
infinite pairwise-coprime family.

The arXiv Atom API searches for `"fixed point order" AND Fibonacci`,
`"order of appearance" AND "relatively prime"`, Fibonacci rank-map
preimages, and self-Fibonacci divisors located no resolution. Crossref
reported zero references to the DOI; OpenAlex reported `cited_by_count = 0`;
Semantic Scholar reported `citationCount = 0` and an empty citations result;
and the zbMATH search for "order of appearance map" found only the earlier
arXiv record. Thus no published resolution was located through 15 August
2026. This database result is a bounded priority check, not a proof that no
unindexed resolution exists.

Theorem `thm:prime-inverse-rays` and Corollaries `cor:prime-basins` and
`cor:prime-fixed-order` give infinitely many distinct primes in the two
families. Distinct primes are pairwise relatively prime, so the result
strictly strengthens both printed statements rather than changing their
quantifiers. The only manuscript input used is the unconditional exact-rank
prime existence theorem for every rank \(d\geq3\), \(d\notin\{6,12\}\),
plus the published fixed-point classification and termination of all rank-map
orbits. The exceptional basin is reached through
\(7\mapsto8\mapsto6\mapsto12\).
