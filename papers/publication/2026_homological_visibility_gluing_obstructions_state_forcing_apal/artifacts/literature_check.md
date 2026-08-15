# Literature and Priority Check

Date of record: 15 August 2026 (Asia/Singapore).

## Scope and evidentiary basis

This record states the priority boundary supported by the current manuscript,
its `references.bib`, and the external assessment in
`oracle_sprint_A9_referee.md`. It is not a claim that an exhaustive literature
search can certify absolute priority. In particular, a statement not found
verbatim in the referee's targeted search is not thereby a substantial new
mathematical result.

All bibliographic metadata asserted below were checked against
`references.bib`. Chapter and proposition locators were also checked against
the citations in the manuscript. No unconfirmed bibliographic detail is used.

## Direct antecedent: Giraud's component-gerbe construction

The relevant book is Jean Giraud, *Cohomologie non abelienne*, Grundlehren der
mathematischen Wissenschaften 179, Springer-Verlag, 1971. These metadata are
the metadata recorded in `references.bib`.

Chapter III, Proposition 2.1.5.3 is the direct antecedent for the
component-gerbe construction. For any stack `S`, the projection

```text
S -> pi_0(S)
```

makes `S` a gerbe over its sheaf of connected components, and pullback along a
section of `pi_0(S)` gives the corresponding maximal subgerbe. As the referee
observes, this is essentially the structural content of Theorems 4.8(i) and
4.9. It is an input to this paper, not a contribution of this paper. The map
that assigns the gerbe class of the component selected by a section is useful
packaging for later comparisons, but it is not a new construction principle.

The paper also cites Giraud, Chapter IV for the classification of
abelian-banded gerbes by `H^2`, including the identification of neutral gerbes
with the zero class. That classification is a different result from the
Chapter III component-gerbe construction. Both results are used here, and
both are prior work.

## Standard inputs and formal consequences

The referee's assessment is that much of the advertised theorem structure is
textbook gerbe theory, universal-coefficient-theorem naturality, finite
duality, subgroup arithmetic, or fibre counting. The exact organization may
be specific to this manuscript, but the mathematical advance is smaller than
the theorem count and theorem-level presentation suggest.

The following boundaries therefore apply.

| Material used in the paper | Priority status |
|---|---|
| A component selected by a global component section is a maximal subgerbe | Giraud, Chapter III, Proposition 2.1.5.3; standard input |
| Neutrality is equivalent to existence of a global object, and abelian-banded gerbes are classified by `H^2` | Giraud, Chapter IV; standard input |
| Local objects, overlap arrows, triple-overlap Cech 2-cocycles, and change of representative by a coboundary | Standard gerbe theory |
| Realization of a supplied `H^2` class by an abelian-band gerbe | Standard gerbe theory |
| The matching/non-neutrality equivalence | A paper-specific corollary obtained by matching separatedness, sheafification, terminal essential surjectivity, and neutrality; not a new gerbe obstruction theorem, and substantially present in the cited companion project |
| Homological images, Ext-kernel descriptions, annihilating-character descriptions, and quotient factorization | Formal consequences of UCT naturality, finite duality, and quotient universal properties |
| Intersection/sum quotients and their exact sequence | Elementary subgroup and quotient arithmetic |
| Unrestricted auxiliary-register sizes | Fibre cardinality of quotient maps, not an independent information-theoretic result |
| The finite-abelian decomposition used in the wedge result | Standard finite-abelian group structure and generator arithmetic |
| The split component stack used in the empirical-model comparison | Standard construction |

Accordingly, whenever this manuscript applies one of these facts in its chosen
finite-site notation, that application should be described as an application
of a standard result. New notation, a named quotient, or a theorem-sized
restatement does not by itself establish mathematical priority.

## Two-label wedge classification

The referee found no previously published theorem stating the entire
two-label wedge classification verbatim. That negative search result must be
recorded together with its qualification: it does not support a substantial
priority claim. An exact statement obtained by composing standard
equivalences can be formally new while carrying little independent
mathematical priority.

Here the wedge statement is derived from `H_2` of a wedge of 2-spheres, the
description of attainable images of maps from a free abelian group, the
equivalence between complementary image subgroups and an internal direct-sum
decomposition, the classification of finite indecomposable abelian groups,
and generator bounds on the two summands. The resulting exact criterion may
be specific to this selected realization problem, but it is an elementary
two-component realization corollary, not a new classification theorem about
finite abelian groups or gerbes. It is also presentation-relative to the
chosen good-cover construction.

## Closed route: Neeb-Wagemann-Wockel comparison

The bibliography records Karl-Hermann Neeb, Friedrich Wagemann, and Christoph
Wockel, *Making Lifting Obstructions Explicit*, Proceedings of the London
Mathematical Society 106(3) (2013), 589--620, DOI
`10.1112/plms/pds047`, arXiv:`1108.5853`.

The crossed-module comparison discussed in connection with that work is an
explicitly closed route for this paper. This paper begins only after a gerbe
`H^2` class and a Cech representative of that class have been supplied. It
does not contain the source-side degree-three locally continuous or locally
smooth group-cohomology chain model, the characteristic 3-cocycle derived
from strict crossed-module data, or the comparison cochain needed to identify
its Cechization with the lifting-gerbe 2-cocycle.

In particular, the missing step is not supplied by the paper's UCT images,
finite quotients, banded-equivalence naturality, or wedge calculation. It
would require an explicit cochain comparison, with conventions, choice
independence, refinement compatibility, and naturality proved at chain level.
The current paper therefore neither derives a gerbe class from crossed-module
data nor claims to solve that comparison problem. Pursuing the comparison
would require a separate source-side theory and a separate proof, not an
extension of the results recorded here.

## Defensible paper-specific remainder

After the prior inputs and formal consequences above are removed from the
priority account, the defensible paper-specific content is narrow:

1. The exact representative-rigid terminal-fibre no-go formulation is the
   strongest plausible technical priority claim identified by the referee.
   Its formulation may be new, but its ingredients - split cleavages,
   pseudofunctorial pullback choices, and `H^1` classification of torsors -
   are classical. It is not a new general descent principle.

2. The exact prestack presentation simultaneously controls the component
   presheaf, terminal essential surjectivity, neutral versus non-neutral
   labels, and prescribed componentwise homological images, and places these
   controls inside the paper's typed-model convention. This simultaneous
   finite-label/presheaf packaging is paper-specific. The underlying
   Cech-cocycle gerbe realization and the disjoint-union assembly are standard
   inputs.

3. The exact two-label wedge criterion is, at most, a sharp algebraic
   corollary for the selected realization construction. The referee found no
   verbatim antecedent, but this supports only a claim about the exact
   packaging, not a substantial independent classification priority.

4. The empty-domain comparison with local-section-indexed contextuality
   classes is a useful narrow boundary observation: for a strongly contextual
   empirical model there is no global component section, while the comparison
   classes are indexed by local sections. The split stack used to expose this
   mismatch is standard.

5. The one-model, one-variable, parameter-free, constant-free lower-language
   separation example is plausibly specific to the paper but deliberately
   narrow. It does not establish general expressive incomparability.

The organization of presentation-relative homological images is bookkeeping
that may be useful to readers, not an independent priority claim. The
referee also identified unresolved overlap with an unpublished companion
manuscript for the component-obstruction framework, the matching/non-neutral
criterion, and quotient initiality. Until that overlap is documented in a
theorem-by-theorem public comparison, chronological priority for those parts
cannot be certified here.

This is the priority boundary for the submission package: standard inputs are
credited as standard, exact packaging is not inflated into a broad novelty
claim, and the remaining claims are limited to the concrete formulations and
simultaneous controls listed above.
