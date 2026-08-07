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
