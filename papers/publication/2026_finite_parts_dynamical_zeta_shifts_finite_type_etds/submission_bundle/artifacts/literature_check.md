# Literature and Novelty Check

Date of search: checked through 15 August 2026 (Asia/Singapore).

## Frobenius-class product and Axiom A flow audit (8 August 2026)

This additional audit was performed before attempting any flow extension.
The arXiv Atom API, Crossref, Google Scholar, zbMATH Open, and the reference
lists of the principal antecedents were searched for combinations of
`Frobenius class`, `Mertens`, `closed orbits`, `finite group extension`,
`Galois covering`, and `Axiom A flow`.  The exact arXiv queries for
`"Axiom A flows" AND Chebotarev` and for `"Frobenius class" AND
"closed orbits"` returned zero records; the broader query `"closed orbits"
AND Mertens` returned the later sofic-shift note arXiv:2202.03075.  Crossref
confirmed the records and citation trails for Sharp (1991), DOI
`10.1007/BF01237365`, and Parry--Pollicott (1986), DOI
`10.1017/S0143385700003333`.  Google Scholar returned those two works and
Mohamed--Noorani (1999) as the relevant exact-title results; subsequent
requests encountered Scholar's automated-traffic challenge.  zbMATH Open
record `0761.58041` supplies a review and full reference list for Sharp's
Mertens product theorem, and record `0626.58006` states the Frobenius-class
Chebotarev theorem for finite Galois coverings of Axiom A flows.

The official Mohamed--Noorani PDF was checked directly, including Theorem 1
on pp. 124--125 and all seven references.  Theorem 1 already proves a
Frobenius-class Mertens product for closed orbits of a subshift of finite type,
with exponent `|C|/|G|` and an explicit constant written in Artin-L terms.
The present manuscript cites it in the abstract, introduction, theorem-local
comparison, formal correction theorem, conclusion, and bibliography.  It
states plainly that product existence and the exponent are prior art, isolates
the invalid replacement of `chi(g_gamma)` by `chi(g_gamma^r)`, and separately
repairs the missing extension-level mixing/strict-gap hypothesis.  No citation
change was needed.

The proposed leading-product analogue for Axiom A flows is not a defensible
tier-up target.  Sharp already proves the unrestricted Axiom A Mertens product,
while Parry--Pollicott prove Frobenius-class density for mixing finite Galois
extensions; the class-restricted leading product is a direct synthesis of that
analytic framework.  There is also a formulation problem: a continuous (hence
Holder) cocycle `c:X x R -> G` into a discrete finite group is trivial, since
`t -> c(x,t)` is continuous and equals the identity at zero.  The non-trivial
flow category is a finite principal covering with monodromy, or equivalently a
finite cocycle on a Poincare return map/Markov coding.  In that correct
category, the genuinely defensible increment of this manuscript remains the
fixed-primitive-label correction to the constant and its exact finite-state
consequences, not a new Mertens theorem or a new Axiom A leading asymptotic.
As with the earlier audit, this is evidence delimiting the novelty claim, not
a proof of absolute priority.

## Scope and method

The search concerned the following precise question: for a fixed finite directed
graph and a finite-group one-step edge cocycle, does the family of irreducible
twisted characteristic polynomials determine the cocycle up to continuous
Livsic cohomology, and is there a published necessary-and-sufficient invariant
for that property?  This is narrower than conjugacy or flow equivalence of
`G`-SFTs and narrower than recovery of unmarked periodic data.

The arXiv Atom API (`https://export.arxiv.org/api/query`) was queried directly.
The following exact searches each returned `opensearch:totalResults = 0`:

- `all:"twisted determinant" AND all:"shift of finite type"`;
- `all:"Livsic" AND all:"finite group" AND all:"subshift"`;
- `all:"inverse rigidity" AND all:"dynamical zeta"`;
- `all:"periodic data" AND all:"non-abelian cocycle"`;
- `all:"G-SFT" AND all:"zeta"`.

The API feed timestamp was `2026-08-01T16:29:26--27Z`.  Subsequent broader
API requests were rate-limited with HTTP 429; this limitation is material and
precludes treating the search as proof of absolute priority.  Exact-title and
DOI searches were therefore cross-checked against Crossref and OpenAlex, and
the manuscript's existing adjacent bibliography was reviewed entry by entry.

## Closest prior work

1. M. Boyle and S. Schmieding, *Finite group extensions of shifts of finite
   type: K-theory, Parry and Livsic*, Ergodic Theory Dynam. Systems 37 (2017),
   1026--1059, DOI `10.1017/etds.2015.87`, arXiv:`1503.02050`.

   This is the closest comparison.  It studies periodic-data invariants and
   topological conjugacy classes of finite-group extensions, proves that zeta
   data can be compatible with infinitely many non-conjugate extensions, and
   gives computable complete invariants for periodic data.  It does not state
   the fixed-named-edge Livsic fiber cardinality used here, the one-step
   transfer-memory reduction, or the formula
   `m! / product_g n_g!` for finite-abelian bouquet cocycles.  The present
   paper cites this result as an antecedent and does not present its
   K-theoretic or `G`-SFT conjugacy results as new.

2. J. Epperlein, *Eventual conjugacy of free inert G-SFTs*, Ergodic Theory
   Dynam. Systems (First View, 2026), DOI `10.1017/etds.2026.10309`,
   arXiv:`2309.08512`.

   This concerns eventual conjugacy of a named subclass of `G`-SFTs, not
   determinant fibers on a fixed edge presentation.

3. R. Dougall and R. Sharp, *Anosov flows, growth rates on covers and group
   extensions of subshifts*, Invent. Math. 223 (2021), 445--483,
   DOI `10.1007/s00222-020-00994-3`, arXiv:`1904.01423`.

   This supplies adjacent group-extension and spectral-growth context, not an
   inverse classification of edge cocycles.

4. V. Berthe, H. Goulet-Ouellet, C.-F. Nyberg-Brodda, D. Perrin, and
   K. Petersen, *Density of group languages in shift spaces*, Ergodic Theory
   Dynam. Systems (First View, 2026), DOI `10.1017/etds.2026.10318`,
   arXiv:`2403.17892`.

   This is adjacent finite-group symbolic dynamics but does not address
   twisted-determinant inverse rigidity.

## Exact proof antecedents and metadata

| Role | Reference | Exact identifier | Use in the paper |
|---|---|---|---|
| Non-abelian Livsic theory | W. Parry, *The Livsic periodic point theorem for non-abelian cocycles*, ETDS 19 (1999), 687--701 | DOI `10.1017/S0143385799146789` | Establishes the broader periodic-weight/cohomology context and, importantly, warns that mere conjugacy of non-abelian weights is not generally the same as cohomology. The paper proves its special one-step descent independently. |
| Compact-group Livsic regularity | W. Parry and M. Pollicott, *The Livsic cocycle equation for compact Lie group extensions of hyperbolic systems*, JLMS 56 (1997), 405--416 | DOI `10.1112/S0024610797005474` | General compact-group cocycle regularity and cohomology context; not reproduced. |
| Dynamical zeta formalism | W. Parry and M. Pollicott, *Zeta Functions and the Periodic Orbit Structure of Hyperbolic Dynamics*, Asterisque 187--188 (1990) | No DOI located; stable Numdam record `AST_1990__187-188__1_0` | Standard trace/log-determinant and periodic-orbit normalization. |
| Adams operations | M. F. Atiyah and D. O. Tall, *Group representations, lambda-rings and the J-homomorphism*, Topology 8 (1969), 253--297 | DOI `10.1016/0040-9383(69)90015-9` | Representation-ring Adams operations. Crossref shows that the formerly recorded suffix `90025-7` was erroneous. |
| Lambda-ring reference | D. Knutson, *Lambda-Rings and the Representation Theory of the Symmetric Group*, LNM 308 (1973) | DOI `10.1007/BFb0069217` | Standard lambda-ring/Adams-operation reference. |
| Perron--Frobenius | E. Seneta, *Non-negative Matrices and Markov Chains*, revised printing (2006) | DOI `10.1007/0-387-32792-4` | Primitive-matrix spectral facts and strict Perron gap. |
| Primitivity exponent | H. Wielandt, *Unzerlegbare, nicht negative Matrizen*, Math. Z. 52 (1950), 642--648 | DOI `10.1007/BF02230720` | The finite verifier's terminating primitivity test uses the Wielandt bound `(n-1)^2+1`. |

Crossref metadata were queried for the journal DOIs.  The Parry Crossref
record explicitly states the distinction between coincident weights,
conjugate weights, and cohomology; that distinction is respected in the new
proof.  The Numdam bibliographic record was used for the Parry--Pollicott
Asterisque volume because no DOI was located.

## Novelty assessment

No searched source states the following combined result: continuous
cohomology between finite-group one-step edge cocycles on an essential edge
shift reduces to vertex gauge; the exact twisted-determinant rigidity
obstruction is the cardinality of a full-Wedderburn spectral fiber in
`Hom(pi_1(|Gamma|),G)/G`; and on a finite-abelian `m`-loop bouquet that
cardinality equals `m! / product_g n_g!`, with every primitive non-trivial
abelian bouquet extension consequently non-rigid.

The defensible novelty claim is therefore limited to this fixed-presentation
spectral-cohomology classification and its closed abelian-bouquet evaluation.
The general multiplicity-one criterion is an intrinsic finite reformulation,
not a claim that periodic-data or `G`-SFT classification was previously
unknown.  Absolute priority cannot be certified by a finite database search;
the zero-result API queries and the targeted comparison above provide
evidence of novelty, not a logical proof of it.

## Effective rational Mahler coboundary audit

An additional search was performed on 8 August 2026 for the normalized
nonlinear equation
`P0(z) R(z)^2 = P1(z) R(z^2)`. The arXiv Atom API returned zero results for
each of

- `all:"rational solutions" AND all:"Mahler equation"`;
- `all:"Mahler coboundary"`;
- `all:"multiplicative coboundary" AND all:Mahler`;
- `all:"rational function" AND all:"f(z^k)"`.

The broader query `all:"Mahler equations" AND all:algorithm AND
all:rational` returned four records. The only directly adjacent one was
F. Chyzak, T. Dreyfus, P. Dumas, and M. Mezzarobba, *Computing solutions of
linear Mahler equations*, Math. Comp. 87 (2018), 2977--3021,
DOI `10.1090/mcom/3359`, arXiv:`1612.05518`. It treats linear Mahler
operators, not the nonlinear normalized equation above. The same authors'
*First-order factors of linear Mahler operators*, arXiv:`2403.11545`, computes
infinite-product solutions and factors of linear Mahler operators; its
Hermite--Pade step likewise does not state the divisor bound, coefficient
height bound, or nonlinear Pade criterion used here.

Crossref and zbMATH Open were queried with the phrases `rational solutions
Mahler equations`, `effective rationality Mahler functions algorithm`,
`rational solutions nonlinear Mahler equation`, and `algebraic Mahler equation
rational solution algorithm`. The potentially closest title was C. Pegis,
*Rational solutions of a nonlinear functional equation related to Mahler's
equation*, J. Math. Anal. Appl. 199 (1996), 489--494,
DOI `10.1006/jmaa.1996.0156`. The zbMATH review identifies its equation as
`F(z^2)=A F(z)+B+C/F(z)` for constants `A,B,C`; it is not the equation
`F(z^2)=(P0/P1)F(z)^2` and supplies none of the present input-dependent
bounds. No searched record states the effective normalized rational
coboundary theorem integrated in the manuscript. As above, this is positive
evidence of novelty rather than a proof of absolute priority.

## Effective finite-sampling audit

A further search on 8 August 2026 tested the finite-sampling consequence of
the certificate.  The arXiv Atom API returned zero records for both
all:"finite sampling" AND all:Mahler and
all:"dynamical zeta" AND all:"finite samples".  It again returned zero for
all:"rational solutions" AND all:"Mahler equation" and
all:"Mahler coboundary".

Crossref, Semantic Scholar, and zbMATH Open were searched for finite sampling
Mahler function, zeros special values Mahler functions finite sampling,
Pade rational reconstruction Mahler equation, and finite group extension
dynamical zeta inverse finite samples.  The nearest records were:

- Chyzak--Dreyfus--Dumas--Mezzarobba (2018), DOI 10.1090/mcom/3359,
  for algorithms solving linear Mahler equations;
- Arreche--Zhang, *Mahler Discrete Residues and Summability for Rational
  Functions* (ISSAC 2022), DOI 10.1145/3476446.3536186, for additive
  rational summability;
- Pegis (1996), DOI 10.1006/jmaa.1996.0156, for the different equation
  F(z^2)=A F(z)+B+C/F(z);
- Boyle--Schmieding (2017), DOI 10.1017/etds.2015.87, for periodic-data
  invariants of finite-group extensions.

Semantic Scholar resolved all four DOI records; its keyword-search endpoint
was intermittently rate-limited with HTTP 429.  zbMATH Open returned the
linear-solution paper (record 1393.39002), the 2025 first-order-factor paper
(record 1572.11106), and the Mahler-residue paper, but no finite-sampling
inverse theorem.  None of the located works bounds radial collision points by
the degree of a normalized multiplicative Mahler certificate or derives a
finite dynamical-zeta sampling theorem.  This supports, but cannot prove,
the priority of Theorem thm:finite-radial-sampling.

Finally, the requested stronger dependence on only `(graph, group,
Perron-peripheral spectrum)` is mathematically impossible.  The paper gives
two primitive `Z/2` extensions of the same two-vertex graph with the same
Perron-peripheral spectrum `{2}` but spectral cohomology multiplicities `2`
and `1`.  Thus the sharp invariant must retain the full Wedderburn
characteristic data; peripheral data alone cannot be repaired by stronger
mixing or semisimplicity assumptions.

## General-group polynomial sampling audit (10 August 2026)

A fresh search targeted the proposed statement that finitely many algebraic
radial values determine all primitive length--class data for every finite
group, with a sample bound polynomial in the graph size and group order.
The arXiv API query
`("finite sampling" OR "finite determination") AND
("dynamical zeta" OR Mahler)` returned no records.  Broad zbMATH Open
searches for `"finite sampling" Mahler` and
`"dynamical zeta" "finite group" inverse` likewise returned no records.

Crossref and exact-DOI lookups identified two nearest antecedents:

- F. Chyzak, T. Dreyfus, P. Dumas, and M. Mezzarobba, *Computing
  solutions of linear Mahler equations*, Math. Comp. 87 (2018), 2977--3021,
  DOI `10.1090/mcom/3359`, arXiv:`1612.05518`, zbMATH `1393.39002`;
- M. Boyle and S. Schmieding, *Finite group extensions of shifts of finite
  type: K-theory, Parry and Livsic*, ETDS 37 (2017), 2355--2366,
  DOI `10.1017/etds.2015.87`, zbMATH record `6728708`.

The first is the nearest effective Mahler work but concerns linear Mahler
equations.  The second is the nearest dynamical work and studies periodic-data
invariants and non-rigidity for finite-group SFT extensions.  Neither states
an effective inverse theorem for nonlinear multiplicative-coboundary radial
sampling.  Semantic Scholar's keyword endpoint returned HTTP 429 during this
audit, while exact DOI lookups for both records succeeded.  As always, these
database results are evidence about nearest prior work, not proof of absolute
priority.

## Current priority boundary (15 August 2026)

The current manuscript uses the following narrower priority narrative, which
supersedes any broader wording in earlier audit notes:

- Ostrowski (1968) treats the linear multiplicative equation
  `Phi(phi(z)) = g(z) Phi(z)` for rational data.
- Kumiko Nishioka, *Mahler Functions and Transcendence* (1996), Theorem 5.1.7,
  is the standard reference for the rational--transcendental dichotomy for
  `k`-Mahler functions defined by a linear functional equation. Bell, Coons and
  Rowland, arXiv:1210.2070v2, Corollary 8, gives an open-access restatement and
  a new proof.
- The equation `F(z^2) = H(z)^(-1) F(z)^2` is quadratic in `F` and therefore
  outside that linear class. Keiji Nishioka's 1985 nonlinear class
  `f(z^p) = R(z,f(z))` is the applicable result, with `p = 2` and
  `R(z,Y) = Y^2/H(z)`. This algebraic-to-rational step is prior work and is not
  a contribution of the paper.
- Springer keeps the cited 1985 pages 330--335 behind subscription, and
  Unpaywall reported no open-access copy; this audit does not record a
  first-hand check of the printed text.
- The paper's claimed contribution is limited to parity-compatible algebraic
  collision lifting, effective rational-coboundary bounds and reconstruction,
  and the cross-base elementary-two-group result.

In particular, the paper does not claim originality for the general
algebraic-solution rationality theorem, for the fixed-label Euler coordinate,
for Frobenius-class products or equidistribution, or for the general
periodic-data dictionary. This boundary matches the introduction and
conclusion of the present manuscript.

## General-p multiplicative Mahler priority correction (15 August 2026)

A new search was made before extending the effective theorem from `p=2` to
arbitrary fixed `p >= 2`.  It covered the arXiv API, Crossref, the full texts
of arXiv:1612.05518 and arXiv:2403.11545, the author-hosted full text of the
ISSAC 2022 paper below, zbMATH/Open search results, and exact-title web
searches for combinations of `rational solutions`, `Mahler equation`,
`multiplicative`, `summability`, `Riccati`, and `first-order factors`.
OpenAlex returned a depleted daily API budget and ACM's landing page returned
a browser challenge, so neither was treated as negative evidence.  Crossref
metadata and the author-hosted paper supplied the primary record instead.

The decisive antecedents are:

- F. Chyzak, T. Dreyfus, P. Dumas, and M. Mezzarobba, *Computing
  solutions of linear Mahler equations*, Math. Comp. 87 (2018), 2977--3021,
  DOI `10.1090/mcom/3359`, arXiv:`1612.05518`.  Its abstract and Section 3
  give algorithms for rational solutions of linear Mahler equations.
- C. E. Arreche and Y. Zhang, *Mahler Discrete Residues and Summability for
  Rational Functions*, ISSAC 2022, 525--533, DOI
  `10.1145/3476446.3536186`.  Its abstract and Main Theorem give a complete
  effective obstruction to deciding whether a given rational `f(z)` equals
  `g(z^p)-g(z)` for rational `g`.  Its introduction explicitly notes that
  the 2018 linear-Mahler rational-solution algorithm also decides this
  certificate problem.
- F. Chyzak, T. Dreyfus, P. Dumas, and M. Mezzarobba, *First-order factors
  of linear Mahler operators*, J. Symbolic Comput. 130 (2025), 102424, DOI
  `10.1016/j.jsc.2025.102424`, arXiv:`2403.11545`.  Its Riccati monomials are
  products of successive shifts.  It is adjacent, but it is not needed for
  the reduction below.
- C. Pegis, *Rational Solutions of a Nonlinear Functional Equation Related
  to Mahler's Equation*, J. Math. Anal. Appl. 199 (1996), 489--494, DOI
  `10.1006/jmaa.1996.0156`, treats the different equation
  `F(z^2)=A F(z)+B+C/F(z)` with constant coefficients.

The multiplicative decision problem is not formally separate from the first
two algorithms.  Put `H=P0/P1`, let `sigma f(z)=f(z^p)`, and define
`u=z R'/R`.  Direct logarithmic differentiation proves

```
(sigma-1)u = (z/p) H'/H.                                      (1)
```

Thus Arreche--Zhang directly decides and constructs the possible `u`.  The
2018 homogeneous algorithm also applies: for nonzero right-hand side `f`, any
solution of `(sigma-1)u=f` satisfies
`(sigma-(sigma f)/f)(sigma-1)u=0`, after which one filters the rational
solution space by the original affine equation.

The converse is also effective, so this is a reduction rather than a
one-way necessary condition.  A rational solution `u` of (1) comes from a
normalized `R in Q(z)` exactly when `u/z` is regular at zero, has no
polynomial part, and has only simple poles with integer residues.  Necessity
is the standard partial-fraction form of a rational logarithmic derivative.
For sufficiency, Galois invariance groups poles with the same integer residue
into rational irreducible factors; their normalized product gives
`R'/R=u/z` and `R(0)=1`.  Equation (1) then says that
`R(z^p)/(H(z)R(z)^p)` has zero logarithmic derivative.  Its value at zero is
one, so it is identically one.

Consequently, bare decidability of the multiplicative rational-solution
problem is already subsumed after this non-obvious transformation.  The
defensible effective contribution of the revised theorem is narrower: an
input-only degree bound of sharp order `D log D`, an explicit height bound,
computable coefficient numerator and denominator bounds, direct recovery by
one normalized affine Pade system, exact rejection, and polynomial bit
complexity for fixed `p`.  No finite search certifies absolute priority for
each of those quantitative refinements separately.
