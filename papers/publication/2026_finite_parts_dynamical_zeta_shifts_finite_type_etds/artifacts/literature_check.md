# Literature and Novelty Check

Date of search: 2 August 2026 (Asia/Singapore).

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

Finally, the requested stronger dependence on only `(graph, group,
Perron-peripheral spectrum)` is mathematically impossible.  The paper gives
two primitive `Z/2` extensions of the same two-vertex graph with the same
Perron-peripheral spectrum `{2}` but spectral cohomology multiplicities `2`
and `1`.  Thus the sharp invariant must retain the full Wedderburn
characteristic data; peripheral data alone cannot be repaired by stronger
mixing or semisimplicity assumptions.
