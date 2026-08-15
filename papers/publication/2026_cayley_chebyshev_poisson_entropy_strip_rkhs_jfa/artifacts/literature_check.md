# Literature Check: Regularly Varying Poisson-Entropy Boundary Layer

Checked 2026-08-02 (Asia/Singapore). The search target was the
coefficient-subtracted large-scale asymptotic

\[
t^{2N}\left\{
D_{\mathrm{KL}}(P_t*\nu\Vert P_t)
-\sum_{j=2}^{N-1}A_{2j}(\nu)t^{-2j}
\right\}
\]

for a fixed centred law whose tail is regularly varying with the exact
missing-moment index \(2N-2\).

## arXiv API Queries

The following requests were made directly to the required HTTP API endpoint.
The returned Atom feeds were inspected through their
`opensearch:totalResults` fields and, for nonempty feeds, through their
entry titles and abstracts.

| Query | Results | Relevance finding |
|---|---:|---|
| `http://export.arxiv.org/api/query?search_query=all:%22Poisson%20kernel%22%20AND%20all:%22relative%20entropy%22%20AND%20all:%22regular%20variation%22&start=0&max_results=25` | 0 | No direct match. |
| `http://export.arxiv.org/api/query?search_query=all:%22Cauchy%20semigroup%22%20AND%20all:entropy%20AND%20all:asymptotic&start=0&max_results=25` | 0 | No direct match. |
| `http://export.arxiv.org/api/query?search_query=all:%22regularly%20varying%22%20AND%20all:%22relative%20entropy%22&start=0&max_results=25` | 0 | No direct match. |
| `http://export.arxiv.org/api/query?search_query=all:%22Poisson%20semigroup%22%20AND%20all:%22entropy%22&start=0&max_results=25` | 0 | No direct match. |
| `http://export.arxiv.org/api/query?search_query=all:%22truncated%20moment%22%20AND%20all:%22Poisson%20kernel%22%20AND%20all:entropy&start=0&max_results=50` | 0 | No direct match. |
| `http://export.arxiv.org/api/query?search_query=all:%22regular%20variation%22%20AND%20all:%22Cauchy%22%20AND%20all:%22relative%20entropy%22&start=0&max_results=50` | 0 | No direct match. |
| `http://export.arxiv.org/api/query?search_query=all:%22slowly%20varying%22%20AND%20all:%22Poisson%20semigroup%22%20AND%20all:entropy&start=0&max_results=50` | 0 | No direct match. |
| `http://export.arxiv.org/api/query?search_query=all:%22stable%20law%22%20AND%20all:%22relative%20entropy%22&start=0&max_results=25` | 4 | Relevant comparators, but none studies the fixed-law, moving-Cauchy-reference, coefficient-subtracted boundary residual. |
| `http://export.arxiv.org/api/query?search_query=all:%22Hardy-Stein%22&start=0&max_results=50` | 14 | Structural semigroup/Bregman comparators; no matching boundary-layer theorem. |

The nonempty stable-law query returned, in particular:

- S. G. Bobkov, G. P. Chistyakov, and F. Goetze, *Convergence to Stable
  Laws in Relative Entropy*, arXiv:1104.4360,
  DOI 10.1007/s10959-011-0377-0.
- Oliver Johnson, *A de Bruijn identity for symmetric stable laws*,
  arXiv:1310.2045. No DOI was present in the arXiv or Crossref records
  located.
- Giuseppe Toscani, *Entropy Inequalities for Stable Densities and
  Strengthened Central Limit Theorems*, arXiv:1512.05874,
  DOI 10.1007/s10955-016-1619-4.

The Hardy--Stein query returned the principal comparators:

- Rodrigo Banuelos, Krzysztof Bogdan, and Tomasz Luks,
  *Hardy--Stein identities and square functions for semigroups*,
  arXiv:1506.09007, DOI 10.1112/jlms/jdw042.
- Rodrigo Banuelos and Daesung Kim,
  *Hardy--Stein identity for non-symmetric Levy processes and Fourier
  multipliers*, arXiv:1702.06573,
  DOI 10.1016/j.jmaa.2019.123383.
- Michal Gutowski, *Hardy--Stein identity for pure-jump Dirichlet forms*,
  arXiv:2209.13568, DOI 10.4064/ba230404-1-6.
- Krzysztof Bogdan, Michal Gutowski, and Katarzyna Pietruska-Paluba,
  *Polarized Hardy--Stein identity*, arXiv:2309.09856,
  DOI 10.1016/j.jfa.2025.110827.
- Michal Gutowski and Mateusz Kwasnicki,
  *Beurling--Deny formula for Sobolev--Bregman forms*,
  arXiv:2312.10824, DOI 10.1016/j.na.2025.113808.

## Standard External Inputs

The new proof invokes only the regular-variation results in the first item
below. The remaining items are exact contextual comparators; their theorems
are not imported into the boundary-layer proof.

- N. H. Bingham, C. M. Goldie, and J. L. Teugels,
  *Regular Variation*, Cambridge University Press, 1987,
  DOI 10.1017/CBO9780511721434. Proposition 1.5.9a supplies the divergent
  integrated-slow-variation fact
  \(L(t)=o(\int^tL(s)\,ds/s)\); Theorem 1.5.11 supplies Karamata's
  direct and tail integral theorems. This is the only external theorem used
  in the new proof.
- Laurens de Haan and Ana Ferreira, *Extreme Value Theory: An
  Introduction*, Springer, 2006, DOI 10.1007/0-387-34471-3. This records the
  de Haan/second-order regular-variation framework. No second-order theorem
  from this source is used; the paper explicitly leaves second-order entropy
  corrections open.
- N. G. de Bruijn, *A property of heat equation connected with Shannon's
  theory of information*, Nederl. Akad. Wetensch. Proc. Ser. A 56 (1953),
  80-81. No DOI or arXiv identifier was found. This is historical context,
  not a proof input.
- The Hardy--Stein and stable-entropy papers listed above are contextual
  comparators, not proof inputs.

DOI metadata for the books and journal articles was independently checked
against the Crossref REST endpoint
`https://api.crossref.org/works/<DOI>`.

## Novelty Determination

No arXiv record located by the targeted or comparator queries states the
following combination: a fixed centred input law, harmonic Poisson/Cauchy
smoothing, subtraction of all finite Cayley--entropy coefficients below the
missing moment, a tail index exactly \(2N-2\), and the explicit limit
normalized by
\(\ell_L(t)=\int^tL(s)\,ds/s\).

The nearest results separate into three established bodies of work:
Karamata/de Haan regular-variation theory; de Bruijn or Hardy--Stein entropy
dissipation identities; and entropic convergence to stable laws. The
manuscript cites those inputs and does not claim any of their theorems as
new. Its new statement is the quotient-to-entropy synthesis yielding the
constant
\[
p(c_++c_-)(-1)^N(N-1)2^{-2N+2}\mu_2.
\]

This is a documented negative literature search, not a logically exhaustive
proof that no publication exists outside the indexed sources. Within the
queried arXiv corpus and the standard references/comparators above, no prior
publication of the stated theorem was found.

## Covariance-Proxy Defect Search

Checked 2026-08-08 (Asia/Singapore).  The additional search target was an
exact large-scale decomposition of radial Poisson relative entropy into the
quadratic covariance coefficient and the relative entropy from a
covariance-matched second-order Poisson proxy.

Direct arXiv API queries gave the following results:

| Query | Results | Relevance finding |
|---|---:|---|
| `all:"Poisson kernel" AND all:"relative entropy" AND all:covariance` | 0 | No matching record. |
| `all:"Cauchy semigroup" AND all:"relative entropy"` | 0 | No matching record. |
| `all:"Poisson semigroup" AND all:entropy AND all:deficit` | 0 | No matching record. |
| `all:"Poisson kernel" AND all:"Kullback-Leibler"` | 2 | The returned path-planning and discrete-kernel-smoothing papers are unrelated. |
| `all:Poisson AND all:"relative entropy"` | 10 in the requested page | The results concern Poisson channels, Poisson approximation, coding, Euler--Poisson systems, or Poisson suspensions, not harmonic Poisson smoothing against a covariance proxy. |

A Crossref bibliographic search for `Poisson kernel relative entropy
covariance deficit` returned Poisson-channel and Poisson-approximation papers,
an ARMA covariance-constraint paper, and unrelated applications.  None states
the covariance-proxy decomposition.  The closest standard information-theory
inputs remain the classical data-processing and finite-partition
characterizations of relative entropy; those facts are not claimed as new.

No indexed source located in this search gives the combination of a fixed
input law with only finite covariance, harmonic Poisson smoothing, the
explicit bounded mode (b_\Sigma), and the asymptotic identity

\[
t^4D_{\rm KL}(h_t\Vert g_t)
=\mathcal Q_d(\Sigma)+t^4D_{\rm KL}(h_t\Vert k_{\Sigma,t})+o(1).
\]

As above, this is a documented negative search rather than a logically
exhaustive proof of absence from all literature.

## Stable-Kernel Critical-Moment Search

Checked 2026-08-08 (Asia/Singapore).  The search target was the optimal
absolute-moment hypothesis for the covariance-order relative-entropy
asymptotic of a fixed law smoothed by an isotropic strictly alpha-stable
kernel, with the stable kernel itself as the translated reference.

The nearest paper was inspected in full:

- K. Ishige, T. Kawakami, and H. Michihisa, *Asymptotic Expansions of
  Solutions of Fractional Diffusion Equations*, SIAM J. Math. Anal. 49
  (2017), 2167--2190, arXiv:1610.09789,
  DOI 10.1137/16M1101428.
- K. Ishige and T. Kawakami, *Refined Asymptotic Expansions of Solutions to
  Fractional Diffusion Equations*, J. Dynam. Differential Equations 36
  (2024), 2679--2702, arXiv:2109.14193,
  DOI 10.1007/s10884-022-10224-4.

Their theorems, bibliographies, and forward-citation records were checked,
along with Crossref, Semantic Scholar, zbMATH, and targeted arXiv searches
for combinations of stable/fractional heat kernels, translated density
quotients, relative entropy, asymptotic expansions, and moment conditions.
The arXiv API returned HTTP 429 during this audit, so arXiv abstract pages,
HTML, and PDFs were used to inspect the relevant records.  Google Scholar
was also queried but returned its unusual-traffic interstitial; no Scholar
results are therefore represented as inspected.

Ishige--Kawakami--Michihisa prove density-level fractional-heat expansions:
moment-weighted kernel derivatives are subtracted and the remainder is
controlled in scaled L^q and weighted L^1 norms.  The refined paper extends
that framework to inhomogeneous and nonlinear equations.  Neither paper
states the critical matched-quotient estimate

\[
\left\|\frac{p_1(\mathord\cdot-z)}{p_1}\right\|_{L^q(p_1)}^q
\asymp (1+|z|)^{(d+\alpha)(q-1)},
\]

uses it to transfer a moment expansion through relative entropy, or gives
the uniform sufficient exponent

\[
p_{\alpha,d}=\max\left\{2,
\frac{4(d+\alpha)}{d+\alpha+4}\right\}.
\]

The stable-entropy papers of Bobkov--Chistyakov--Goetze, Johnson, and
Toscani concern convergence of normalized convolution sequences or entropy
relative to a fixed stable target.  They do not address this fixed-input,
large-spatial-scale, moving matched-reference problem.  No indexed source
located in the audit states the exponent or the matching uniform
moment-class optimality result.  This remains a qualified negative search,
not a proof of absence from every publication.

## Stable Law-by-Law Tail-Decomposition Search

Checked 2026-08-10 (Asia/Singapore), before extending the Poisson raw-tail
identity to every isotropic strictly alpha-stable kernel.  The target was the
finite-covariance decomposition

\[
H_{\alpha,d}(s)=\mathcal Q_{\alpha,d}(\Sigma)s^{-4}
+\int\Phi\!\left(\int_{|x|>s}
  \frac{p_1^{(\alpha,d)}(y-x/s)}{p_1^{(\alpha,d)}(y)}\,\nu(dx)
 \right)\Omega_{\alpha,d}(dy)+o(s^{-4}).
\]

The arXiv API was queried for combinations of `isotropic stable kernel`,
`relative entropy`, `covariance asymptotic`, `fractional heat kernel`,
`moment expansion`, and `Kullback--Leibler`.  Broad queries were noisy; exact
title queries recovered the two fractional-diffusion papers below and no
record stating the displayed nonlinear tail-potential formula.  Crossref
bibliographic queries likewise returned the two papers with DOI
10.1137/16M1101428 and DOI 10.1007/s10884-022-10224-4 as the closest
mathematical matches.  Semantic Scholar's API returned HTTP 429 during this
live pass; its records and forward citations for the same papers had already
been inspected in the 2026-08-08 audit above.  The zbMATH Open API was queried
through `/v1/document/_search`; its fractional-diffusion results contained no
matching entropy decomposition.

A subsequent exact-record retry on the same date succeeded.  The arXiv title
queries returned arXiv:1610.09789 and arXiv:2109.14193; the targeted stable
kernel/relative entropy/covariance and fractional heat
kernel/relative entropy/moment queries each returned zero records.  Semantic
Scholar's DOI endpoints returned the same two papers and their forward
citation sets (21 and 5 citations at query time).  The exact zbMATH title
query returned the 2017 paper as its single result.  Inspection of these
records did not locate the displayed nonlinear tail-potential decomposition.

The nearest prior work remains:

- K. Ishige, T. Kawakami, and H. Michihisa, *Asymptotic Expansions of
  Solutions of Fractional Diffusion Equations*, SIAM J. Math. Anal. 49
  (2017), 2167--2190, arXiv:1610.09789, DOI 10.1137/16M1101428.
- K. Ishige and T. Kawakami, *Refined Asymptotic Expansions of Solutions to
  Fractional Diffusion Equations*, J. Dynam. Differential Equations 36
  (2024), 2679--2702, arXiv:2109.14193,
  DOI 10.1007/s10884-022-10224-4.

Those works prove stable heat-kernel density expansions after subtracting
moment derivatives.  They provide the decay and derivative estimates used in
the present proof, but the inspected theorem statements do not aggregate the
unexpanded mass beyond the moving scale before applying the entropy
nonlinearity.  The Bobkov--Chistyakov--Goetze, Johnson, and Toscani papers
listed above remain the nearest entropy comparators, in the different regime
of stable limits or stable de Bruijn identities.  This is a documented,
qualified search of the four requested indexes, not a proof of global
novelty.

## All-Order First-Unmatched Stable-Tensor Search

Checked 2026-08-15 (Asia/Singapore), before adding Theorem
thm:all-order-stable-first-unmatched-moment.  The target was a two-input
relative-entropy asymptotic under isotropic strictly stable smoothing, at an
arbitrary first unmatched tensor order \(r\), together with the endpoint
\[
q_{r,\alpha,d}=\min\{2,1+2r/(d+\alpha)\},\qquad
p_{r,\alpha,d}=2r/q_{r,\alpha,d}
\]
and uniform moment-class optimality.

The arXiv API was queried directly.  The searches “stable kernel” AND
“moment asymptotic”, “fractional heat kernel” AND “relative entropy”, and
“Gaussian quadrature” AND “stable” AND “entropy” returned zero records.
The search “moment matched” AND “relative entropy” returned three records:
arXiv:1801.01740 (micro--macro acceleration), arXiv:2005.00738 (smoothed
Wasserstein distances), and arXiv:1706.00050 (cellular-network interference).
The initial audit incorrectly dismissed arXiv:2005.00738.  Chen--Niles-Weed,
Theorem 2.5, is the direct Gaussian precedent: under sub-Gaussian tails it
proves the exact KL coefficient in every dimension and at every first
unmatched order.  With their heat time \(t=s^2\), their coefficient is exactly
the Gaussian/Hermite specialization of the quadratic form in the present
theorem.  It does not cover \(0<\alpha<2\), the critical finite-moment
exponent, endpoint sufficiency, or uniform moment-class sharpness.  The
broader “stable law” AND
“relative entropy” query returned Bobkov--Chistyakov--Goetze
(arXiv:1104.4360), Johnson (arXiv:1310.2045), Toscani
(arXiv:1512.05874), and Cook (arXiv:2504.13423).  Their abstracts and stated
regimes concern stable-limit convergence, stable de Bruijn identities, or
stable-to-stable scale families, not fixed-input large-scale smoothing with a
first unmatched tensor.

Crossref title and bibliographic searches returned
Bobkov--Chistyakov--Goetze, DOI 10.1007/s10959-011-0377-0, as the closest
stable-entropy record, together with unrelated moment-problem papers.  The
zbMATH Open API returned no record for the combined stable-kernel,
relative-entropy, moment query.  Semantic Scholar's live API returned HTTP
429 and is not counted as a completed search in this pass; its records and
forward citations for the two nearest fractional-diffusion papers had been
inspected in the 2026-08-08 audit above.

The closest density-expansion results remain Ishige--Kawakami--Michihisa,
SIAM J. Math. Anal. 49 (2017), 2167--2190, arXiv:1610.09789, and
Ishige--Kawakami, J. Dynam. Differential Equations 36 (2024), 2679--2702,
arXiv:2109.14193.  They establish moment-subtracted stable heat-kernel
expansions, but the inspected theorem statements do not give the critical
matched-quotient remainder, the two-background Bregman transfer, the
\(s^{-2r}\) KL tensor coefficient, or the endpoint uniform counterexample.
No indexed source located in this audit states the combined heavy-tailed
theorem with its critical moment threshold and sharpness.  This revised
conclusion concerns only that surviving increment; arbitrary-order
first-unmatched KL asymptotics themselves are not claimed as new.

## Two-Stable-Heat-Flow Dissipation Search

Checked 2026-08-15 (Asia/Singapore), before adding Theorem
thm:two-stable-heat-flow-relative-entropy.  The target was the exact
moving-denominator theorem for
\[
 D_{\rm KL}(p_t*\mu\Vert p_t*\nu),
\]
including a measure-data domain, rigorous noncompact fractional Green
pairings, the endpoint at infinity, and the stable-reference integral
representation requested in Johnson's Open Problem 4.

Direct arXiv API searches were run for "relative entropy" AND "fractional
heat" (one unrelated SPDE record), "relative entropy dissipation" AND
"fractional Laplacian" (zero records), "stable heat flow" AND entropy
(zero records), and "symmetric stable" AND "de Bruijn" (Johnson's paper
only).  Crossref bibliographic searches for the same combinations returned
the local-diffusion comparator *A Dissipation of Relative Entropy by
Diffusion Flows*, stable-limit entropy papers, and unrelated fractional
models; they did not return a two-stable-heat-flow theorem.  The earlier
Semantic Scholar and zbMATH checks of Johnson and the nearest
fractional-diffusion records are documented above; neither index supplied
the target theorem.

The pure-jump search was intentionally broader.  The arXiv query
"Hardy-Stein" returned 14 records, including Banuelos--Bogdan--Luks,
Gutowski, Bogdan--Gutowski--Pietruska-Paluba, and
Gutowski--Kwasnicki.  The query "Sobolev-Bregman" returned four records,
including the nonlinear Douglas and Beurling--Deny papers already cited.
These works establish broad one-function, polarized, and Sobolev--Bregman
identities, so the manuscript makes no discovery claim for the two-point
logarithmic jump algebra.

The closest additional record is T. Klimsiak and A. Rozkosz,
*Nonlinear Hardy--Stein type identities for harmonic functions relative to
symmetric integro-differential operators*, arXiv:2507.18308.  Its abstract
and Sections 4--6 were inspected through the arXiv HTML rendering.  It proves
conditional Hardy--Stein identities for ratios of harmonic functions and
general convex functions, including purely nonlocal examples.  This makes
the ratio/Bregman algebra an explicit prior-art boundary.  It does not state
the parabolic evolution of two simultaneous stable heat flows, compact-time
quotient estimates for measure initial data, the finite
$(d+\alpha)$-moment domain, separate noncompact Green-pairing limits, or the
$t=\infty$ and $q\downarrow0$ entropy closures.

Johnson's arXiv:1310.2045 was re-inspected at the theorem and open-problem
level.  His differential stable de Bruijn identity uses an
integration-by-parts qualification, and Open Problem 4 asks for a
representation of $D(f\Vert g_s^{(\alpha)})$ as an integral.  No later
indexed source located in this search supplies that representation.

Accordingly, the novelty claim written in the manuscript is only the exact
moving-denominator parabolic theorem for symmetric stable heat flows from
measure data, its explicit sufficient moment domain, the rigorous
noncompact and endpoint closures, and the connection to Johnson's integral
representation.  The exponent $d+\alpha$ is not claimed optimal.  No claim
is made for all isotropic unimodal Levy semigroups or all subordinate
Brownian motions.  This remains a documented negative search, not proof of
absence from every publication.
