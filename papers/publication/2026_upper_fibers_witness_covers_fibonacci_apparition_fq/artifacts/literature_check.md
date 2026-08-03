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
