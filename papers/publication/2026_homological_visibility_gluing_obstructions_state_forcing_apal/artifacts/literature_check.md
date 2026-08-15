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

## Bibliographic integrity audit (15 August 2026)

### Scope and counts

The root `references.bib` contained 45 entries.  The older
`apal_submission_source.zip` contained 44 `.bib` records and a rendered
`main.bbl` containing 38 entries; the root rendered `main.bbl` contained 13
entries.  The 44 archive records used the same key set except that the archive
omitted `NeebWagemannWockel2013` and contained an obsolete, incorrect version
of `BarbosaKharoofOkay2024`.  Thus the audit covers 45 distinct root works plus
that one submission-only metadata variant.  After synchronization, the root
and archive each contain the same 45-entry bibliography.

The table records the metadata as claimed before this audit.  For every DOI,
the Crossref-returned title and lead author are shown explicitly.  `CR 404`
means Crossref returned no work for that DOI; it is not treated as negative
evidence, and the named primary/index record was used instead.  Journal and
proceedings volume/page slots were compared wherever present.  Book DOI checks
used the publisher record in addition to Crossref.

### Per-entry verification table

| Key | Claimed title; lead author | Claimed DOI | Index-returned title; lead author | Slot / corroborating record | Classification |
|---|---|---|---|---|---|
| `Breen2006` | *Notes on 1- and 2-Gerbes*; Lawrence Breen | `10.1007/978-1-4419-1524-5_5` | CR: *Notes on 1- and 2-Gerbes*; Lawrence Breen | Springer publisher: *Towards Higher Categories*, pp. 193-235, bibliographic year 2010 (CR online date 2009) | confirmed |
| `Murray1996` | *Bundle Gerbes*; Michael K. Murray | `10.1112/jlms/54.2.403` | CR: *Bundle Gerbes*; M. K. Murray | *JLMS* 54(2), 403-416 (1996) | confirmed |
| `NeebWagemannWockel2013` | *Making Lifting Obstructions Explicit*; Karl-Hermann Neeb | `10.1112/plms/pds047` | CR: *Making lifting obstructions explicit*; Karl-Hermann Neeb | *PLMS* 106(3), 589-620; arXiv `1108.5853` exact title/authors/DOI; print 2013 (CR online 2012) | confirmed |
| `Beth1956` | *Semantic Construction of Intuitionistic Logic*; Evert W. Beth | none | no exact index result obtained | Claimed *Mededelingen...* 19(11), 357-388 (1956); searches detailed below | **unverified** |
| `Hodges1997` | *Compositional Semantics for a Language of Imperfect Information*; Wilfrid Hodges | `10.1093/jigpal/5.4.539` | CR: same title; W Hodges | *Logic Journal of IGPL* 5(4), 539-563 (1997) | confirmed |
| `AbramskyBrandenburger2011` | *The Sheaf-Theoretic Structure of Non-Locality and Contextuality*; Samson Abramsky | `10.1088/1367-2630/13/11/113036` | CR: same title; Samson Abramsky | *NJP* 13(11), article 113036; claimed pseudo-range 113036-113075 corrected | **confirmed after metadata correction** |
| `AbramskyMansfieldSoaresBarbosa2012` | *The Cohomology of Non-Locality and Contextuality*; Samson Abramsky | `10.4204/EPTCS.95.1` | CR: same title; Samson Abramsky | EPTCS 95, 1-14, published 2012 (workshop QPL 2011) | **confirmed after metadata correction** |
| `AbramskyBarbosaKishidaLalMansfield2015` | *Contextuality, Cohomology and Paradox*; Samson Abramsky | `10.4230/LIPIcs.CSL.2015.211` | CR 404; Dagstuhl: same title; Abramsky, Samson | Official LIPIcs 41, 211-228 (2015); DOI resolves to Dagstuhl record | confirmed |
| `Fitting1969` | *Intuitionistic Logic, Model Theory, and Forcing*; Melvin Fitting | none | OpenLibrary: same title; Melvin Fitting | North-Holland (1969), ISBN `9780720422566` | confirmed |
| `DummitFoote2004` | *Abstract Algebra*; David S. Dummit | none | Wiley/OpenLibrary: *Abstract Algebra*; David S. Dummit and Richard M. Foote | Wiley, 3rd ed.; ISBN `9780471433347`; OpenLibrary date 2004 (Wiley release 2003) | confirmed |
| `Caru2017` | *On the Cohomology of Contextuality*; Giovanni Caru | `10.4204/EPTCS.236.2` | CR: same title; Giovanni Caru | EPTCS 236, 21-39 (2017) | confirmed |
| `Caru2018` | *Towards a Complete Cohomology Invariant for Non-Locality and Contextuality*; Giovanni Caru | none | arXiv: same title; Giovanni Caru | arXiv `1807.04203`, submitted 2018-07-11 | confirmed |
| `Montanhano2021` | *Characterization of Contextuality with Semi-Module Cech Cohomology and its Relation with Cohomology of Effect Algebras*; Sidiney B. Montanhano | `10.48550/arXiv.2104.11411` | CR 404; arXiv: same title; Sidiney B. Montanhano | Official arXiv `2104.11411`, submitted 2021-04-23; DOI resolves to that record | confirmed |
| `Goldblatt2006` | *Topoi: The Categorial Analysis of Logic*; Robert Goldblatt | none | Dover/OpenLibrary: *Topoi* / full title; Robert Goldblatt | Dover paperback product `9780486450261`, publication 2006-04-28, explicitly reprints the 1983 edition | **confirmed after metadata correction** |
| `Johnstone2002` | *Sketches of an Elephant: A Topos Theory Compendium*; Peter T. Johnstone | none | CR exact-title result: *Sketches of an Elephant A Topos Theory Compendium*; Peter T Johnstone | OUP (2002), DOI indexed as `10.1093/oso/9780198515982.001.0001` | confirmed |
| `Tierney1972` | *Sheaf Theory and the Continuum Hypothesis*; Myles Tierney | `10.1007/BFb0073963` | CR: same title; Myles Tierney | LNM 274, 13-42 (1972), Springer | confirmed |
| `Kripke1965` | *Semantical Analysis of Intuitionistic Logic I*; Saul A. Kripke | none | Semantic Scholar: same title; Saul A. Kripke; CR exact DOI record has same title (lead omitted) | *Formal Systems and Recursive Functions*, 92-130 (1965), DOI `10.1016/S0049-237X(08)71685-9` | confirmed |
| `MacLaneMoerdijk1994` | *Sheaves in Geometry and Logic: A First Introduction to Topos Theory*; Saunders Mac Lane | none | CR: *Sheaves in Geometry and Logic*; Saunders Mac Lane | Springer Universitext (1994), DOI `10.1007/978-1-4612-0927-0`; BibTeX surname encoding corrected | **confirmed after metadata correction** |
| `Moerdijk2002` | *Introduction to the Language of Stacks and Gerbes*; Ieke Moerdijk | `10.48550/arXiv.math/0212266` | CR 404; arXiv: same title; Ieke Moerdijk | Official arXiv `math/0212266`, submitted 2002-12-19; DOI resolves to that record | confirmed |
| `Vaananen2007` | *Dependence Logic: A New Approach to Independence Friendly Logic*; Jouko Vaananen | `10.1017/CBO9780511611193` | CR: *Dependence Logic*; Jouko Vaananen | CUP publisher record, ISBN `9780521876599`, 2007; title/author/year match, subtitle retained from edition record | confirmed |
| `BerghSchnurer2021` | *Decompositions for Gerbes and Brauer-Severi Varieties*; Daniel Bergh | none | CR/EMS: *Decompositions of derived categories of gerbes and of families of Brauer-Severi varieties*; Daniel Bergh | *Documenta Mathematica* 26, 1465-1500 (2021), DOI `10.4171/DM/846`; EMS lists Olaf M. Schnurer | **confirmed after metadata correction** |
| `Hatcher2002` | *Algebraic Topology*; Allen Hatcher | none | Author/publisher page: *Algebraic Topology*; Allen Hatcher | CUP, 2002, ISBN `0-521-79540-0`; OpenLibrary corroborates | confirmed |
| `Giraud1971` | *Cohomologie non abelienne*; Jean Giraud | none | CR/Springer: *Cohomologie non abelienne*; Jean Giraud | Grundlehren 179, Springer (1971), DOI `10.1007/978-3-662-62103-5` | confirmed |
| `StacksProject` | *The Stacks Project*; The Stacks Project Authors | none | official site: *The Stacks Project*; project authorship | Live official record at `stacks.math.columbia.edu`; individual tag audit below | confirmed |
| `Terras1999` | *Fourier Analysis on Finite Groups and Applications*; Audrey Terras | `10.1017/CBO9780511626265` | CR: same title; Audrey Terras | CUP publisher record, ISBN `9780521457187`, LMS Student Texts 43 (1999) | confirmed |
| `Weibel1994` | *An Introduction to Homological Algebra*; Charles A. Weibel | none | CR: same title; Charles A. Weibel | CUP, Cambridge Studies in Advanced Mathematics 38 (1994), DOI `10.1017/CBO9781139644136`; OpenLibrary corroborates | confirmed |
| `PapadimitriouYannakakis1984` | *The Complexity of Facets (and Some Facets of Complexity)*; Christos H. Papadimitriou | `10.1016/0022-0000(84)90068-0` | CR: same title; C. H. Papadimitriou | *JCSS* 28(2), 244-259 (1984) | confirmed |
| `OkayRobertsBartlettRaussendorf2017` | *Topological Proofs of Contextuality in Quantum Mechanics*; Cihan Okay | `10.26421/QIC17.13-14-5` | CR: same title; Cihan Okay | *QIC* 17(13&14), 1135-1166 (2017); slot belongs to this article | confirmed |
| `OkayTyhurstRaussendorf2018` | *The Cohomological and the Resource-Theoretic Perspective on Quantum Contextuality: Common Ground Through the Lens of Sheaf Theory*; Cihan Okay | old `10.1007/s11005-018-1054-3` | old DOI CR: *Systems of conservation laws with third-order Hamiltonian structures*; Evgeny V. Ferapontov. New DOI CR: intended contextuality title; C. Okay | Correct record: *QIC* 18(15&16), 1272-1294 (2018), DOI `10.26421/QIC18.15-16-2`, arXiv `1806.04657`; old LMP slot is 1525-1550 and unrelated | **confirmed after metadata correction** |
| `MansfieldBarbosa2012` | *Extendability in the Sheaf-theoretic Approach: Construction of Bell Models from Kochen-Specker Models*; Shane Mansfield | none | arXiv exact-title search: same title; Shane Mansfield | Correct arXiv `1402.4827` (2014); claimed `1203.5307` is Wu and Ye, *A Note On Obata's Rigidity Theorem I* | **confirmed after metadata correction** |
| `MansfieldThesis` | *The Mathematical Structure of Non-locality and Contextuality*; Shane Mansfield | none | no exact accessible index record obtained | Claimed Oxford PhD thesis (2013); searches detailed below | **unverified** |
| `AbramskyBarbosaLogicContextuality` | *The Logic of Contextuality*; Samson Abramsky | none | CR 404 for new DOI; Dagstuhl/arXiv: same title; Samson Abramsky | LIPIcs 183, article 5:1-5:18 (2021), DOI `10.4230/LIPIcs.CSL.2021.5`, arXiv `2011.03064`; claimed `1902.07006` is an unrelated Yoshioka-Hamazaki physics paper | **confirmed after metadata correction** |
| `AbramskyPuljujarviVaananen2025` | *Team Semantics and Independence Notions in Quantum Physics*; Samson Abramsky | `10.1017/bsl.2025.10089` | CR: same title; Samson Abramsky | *BSL* 32(1), 82-135, print 2026; online 2025 as already noted | confirmed |
| `AbramskyBarbosaSearle2024` | *Combining Contextuality and Causality: A Game Semantics Approach*; Samson Abramsky | `10.1098/rsta.2023.0002` | CR: same title; Samson Abramsky | *Phil. Trans. R. Soc. A* 382(2268), article 20230002 (2024) | confirmed |
| `CaruAbramskyValuation2021` | *Non-locality, Contextuality and Valuation Algebras: a General Theory of Disagreement*; Samson Abramsky | old `10.1016/j.jlamp.2021.100661` | old DOI CR/DOI resolver: 404. New DOI CR: same title; Samson Abramsky | Correct record: *Phil. Trans. R. Soc. A* 377(2157), article 20190036 (2019), DOI `10.1098/rsta.2019.0036`, arXiv `1911.03521`; claimed JLAMP slot/DOI does not exist | **confirmed after metadata correction** |
| `BarbosaKharoofOkay2024` | *A Bundle Perspective on Contextuality: Empirical Models and Simplicial Distributions on Bundle Scenarios*; Rui Soares Barbosa | `10.48550/arXiv.2308.06336` | CR 404; arXiv: same title; Rui Soares Barbosa | Official arXiv `2308.06336`, submitted 2023-08-11; DOI resolves to that record | confirmed (root); submission-only variant corrected below |
| `Aasnaess2022` | *Cohomology and the Algebraic Structure of Contextuality in Measurement Based Quantum Computation*; Sivert Aasnæss | none | New DOI CR: same title; Sivert Aasnæss | EPTCS 318, 242-253 (2020), DOI `10.4204/EPTCS.318.15`, arXiv `2005.00213`; claimed `2207.06065` is an unrelated Campos-Villalobos et al. chemistry paper | **confirmed after metadata correction** |
| `MaZhang2026ConditionalGluingFailure` | *Conditional Gluing Failure, Visible Quotients, and Pure-Ext Blind Spots*; Haobo Ma | none | no exact external index record obtained | Described as an unpublished companion manuscript; searches detailed below | **unverified** |
| `GreenbergerHorneZeilinger1989` | *Going Beyond Bell's Theorem*; Daniel M. Greenberger | `10.1007/978-94-017-0849-4_10` | CR: *Going Beyond Bell's Theorem*; Daniel M. Greenberger | Springer chapter in *Bell's Theorem, Quantum Theory and Conceptions of the Universe*, 69-72 (1989) | confirmed |
| `Mermin1990` | *Extreme Quantum Entanglement in a Superposition of Macroscopically Distinct States*; N. David Mermin | `10.1103/PhysRevLett.65.1838` | CR: same title; N. David Mermin | *PRL* 65(15), 1838-1840 (1990) | confirmed |
| `KochenSpecker1967` | *The Problem of Hidden Variables in Quantum Mechanics*; Simon Kochen | none | CR exact-title result: same title; Simon Kochen | *Journal of Mathematics and Mechanics* 17(1), 59-87 (1967), DOI `10.1512/iumj.1968.17.17004`; slot matches | confirmed |
| `Brylinski1993` | *Loop Spaces, Characteristic Classes and Geometric Quantization*; Jean-Luc Brylinski | old `10.1007/978-0-8176-4574-5` | old DOI CR/resolver: 404. New DOI CR: same title; Jean-Luc Brylinski | Birkhauser, Progress in Mathematics 107 (1993); publisher ISBN/DOI `10.1007/978-0-8176-4731-5` | **confirmed after metadata correction** |
| `Bredon1997` | *Sheaf Theory*; Glen E. Bredon | `10.1007/978-1-4612-0647-7` | CR: *Sheaf Theory*; Glen E. Bredon | Springer GTM 170, 2nd ed. (1997); publisher title/author/ISBN match | confirmed |
| `Jardine2015` | *Local Homotopy Theory*; John F. Jardine | `10.1007/978-1-4939-2300-7` | CR: same title; John F. Jardine | Springer Monographs in Mathematics (2015); publisher title/author/ISBN match | confirmed |
| `OkayRaussendorf2016` -> `OkayRaussendorf2020` | *Homotopical Approach to Quantum Contextuality*; Cihan Okay | `10.26421/QIC17.13-14-5` | CR for the claimed DOI: *Topological Proofs of Contextuality in Quantum Mechanics*; Cihan Okay | The original record conflated two genuine works. The DOI and QIC 17(13&14) slot identify Okay, Roberts, Bartlett, and Raussendorf, pp. 1135-1166 (2017), already retained separately as `OkayRobertsBartlettRaussendorf2017`; the claimed title/two-author list identify *Quantum* 4:217 (2020), DOI `10.22331/q-2020-01-05-217`, arXiv `1905.03822`, now keyed `OkayRaussendorf2020`. The claimed end page 1170 and arXiv `1602.04552` match neither work. | **confirmed after metadata correction** |

Classification totals for the 45 root entries are **30 confirmed**, **12
confirmed after metadata correction**, and **3 unverified**.

### Exact metadata corrections

1. `AbramskyBrandenburger2011`: pages `113036--113075` -> article number `113036`.
2. `AbramskyMansfieldSoaresBarbosa2012`: year `2011` -> `2012` (QPL 2011 is the workshop name; EPTCS 95 was published in 2012).
3. `Goldblatt2006`: edition note `Reprint of the 1984 edition` -> `Reprint of the 1983 edition`, following Dover's product record.
4. `MacLaneMoerdijk1994`: BibTeX author `Saunders Mac Lane` (parsed and rendered as surname `Lane`) -> `{Mac Lane}, Saunders`; the human-readable author is unchanged.
5. `BerghSchnurer2021`: author `Oliver M. Schnurer` -> `Olaf M. Schnurer`; title *Decompositions for Gerbes and Brauer--Severi Varieties* -> *Decompositions of Derived Categories of Gerbes and of Families of Brauer--Severi Varieties*; added verified DOI `10.4171/DM/846`.
6. `OkayTyhurstRaussendorf2018`: title ending `Common Ground Through the Lens of Sheaf Theory` -> `Common Ground Through the Contextual Fraction`; journal `Letters in Mathematical Physics` -> `Quantum Information and Computation`; volume/issue/pages `108(6), 1523--1536` -> `18(15--16), 1272--1294`; DOI `10.1007/s11005-018-1054-3` -> `10.26421/QIC18.15-16-2`; added arXiv `1806.04657`.
7. `MansfieldBarbosa2012`: year `2012` -> `2014`; arXiv `1203.5307` -> `1402.4827`.
8. `AbramskyBarbosaLogicContextuality`: misc/preprint year `2019`, arXiv `1902.07006` -> CSL 2021 LIPIcs 183, pages `5:1--5:18`, DOI `10.4230/LIPIcs.CSL.2021.5`, arXiv `2011.03064`.
9. `CaruAbramskyValuation2021`: JLAMP `121`, article `100661` (2021), nonexistent DOI `10.1016/j.jlamp.2021.100661` -> *Phil. Trans. R. Soc. A* `377(2157)`, article `20190036` (2019), DOI `10.1098/rsta.2019.0036`, arXiv `1911.03521`.
10. `Aasnaess2022`: misc/preprint year `2022`, arXiv `2207.06065` -> EPTCS `318`, pages `242--253` (2020), DOI `10.4204/EPTCS.318.15`, arXiv `2005.00213`.
11. `Brylinski1993`: DOI `10.1007/978-0-8176-4574-5` -> `10.1007/978-0-8176-4731-5`.
12. Original `OkayRaussendorf2016` conflation: authors Cihan Okay and Robert
    Raussendorf; title *Homotopical Approach to Quantum Contextuality*; *QIC*
    `17(13--14)`, pages `1135--1170` (2017); DOI
    `10.26421/QIC17.13-14-5`; arXiv `1602.04552`.  Crossref resolves that DOI
    to the different four-author article by Cihan Okay, Sam Roberts, Stephen
    D. Bartlett, and Robert Raussendorf, *Topological Proofs of Contextuality
    in Quantum Mechanics*, *QIC* `17(13--14)`, pages `1135--1166` (2017).
    The bibliography already contains that exact work, unchanged, as
    `OkayRobertsBartlettRaussendorf2017`.  The conflated record was corrected
    and renamed `OkayRaussendorf2020`: authors Cihan Okay and Robert
    Raussendorf; *Homotopical Approach to Quantum Contextuality*; *Quantum*
    `4`, article `217` (2020); DOI `10.22331/q-2020-01-05-217`; arXiv
    `1905.03822`.  This is a split resolution of two genuine papers, not a
    blanket retarget of the original key.

### Per-site decision for the conflated Okay/Raussendorf record

- Root sources: an exact search of every root `*.tex` for
  `OkayRaussendorf2016`, `OkayRaussendorf2020`, and
  `OkayRobertsBartlettRaussendorf2017` found **no `\cite` site**.  Decision:
  no sentence relies on either the 2017 topological/cohomological MBQC
  framework or the 2020 commutativity-structure/Arkhipov generalization, so no
  sentence-level source choice or rewrite was made.
- Submission archive sources: the same exact search of every `*.tex` member
  of `apal_submission_source.zip` found **no `\cite` site**.  Decision: no
  archive sentence required a source choice or rewrite.  The two correctly
  attributed bibliography records are retained separately.

Submission-only variant: the archived `BarbosaKharoofOkay2024` claimed
Francisco Barbosa / Hamed Kharoof / Cihan Okay, title *A Bundle Perspective on
Contextuality*, year 2024, arXiv `2402.01542`.  The arXiv ID belongs to Yang et
al., *Learning Collective Variables with Synthetic Data Augmentation through
Physics-Inspired Geodesic Interpolation*.  It was replaced with the verified
root metadata: Rui Soares Barbosa / Aziz Kharoof / Cihan Okay, full title *A
Bundle Perspective on Contextuality: Empirical Models and Simplicial
Distributions on Bundle Scenarios*, year 2023, arXiv `2308.06336`, DOI
`10.48550/arXiv.2308.06336`.

No entry was deleted.  Consequently there are no per-`cite` deletion
decisions and no citing sentence was rewritten.  Every bad DOI or identifier
had a plausible exact-title/author near-match, so correction rather than
deletion was required by the audit rule.

### Unverified entries and exact searches

- `Beth1956`: Crossref exact title+author returned no matching work (only
  unrelated Beth works); OpenLibrary exact title+author returned no result;
  Semantic Scholar exact search returned HTTP 429; OpenAlex exact search
  returned `Insufficient budget`/daily rate-limit; Google Books exact
  title+author returned HTTP 429.  The pre-DOI academy-journal entry remains
  unchanged; failure of the services is not negative evidence.
- `MansfieldThesis`: Crossref exact title+author returned no thesis record;
  OpenLibrary exact title+author returned no result; the Oxford Research
  Archive catalogue request was stopped by a Cloudflare `Just a moment`
  challenge; Semantic Scholar returned HTTP 429; OpenAlex returned the daily
  budget rate-limit; Google Books returned HTTP 429.  The thesis entry remains
  unchanged.
- `MaZhang2026ConditionalGluingFailure`: Crossref exact title+author returned
  unrelated works and no exact match; a repository-wide exact-title search
  found only this bibliography record; Semantic Scholar returned HTTP 429;
  OpenAlex returned the daily budget rate-limit.  It is explicitly described
  as an unpublished companion manuscript and remains unchanged.

### Stacks Project tag audit

Every URL in this table was fetched directly from
`stacks.math.columbia.edu/tag/<TAG>` on 15 August 2026 and returned HTTP 200;
the displayed lemma/section text was read from the returned page.  In
particular, `00WK` was **actually fetched and read**, not inferred from its
adjacency to `00W1`.

| Tag | Actual official statement read from the fetched tag page | Manuscript use | Verdict |
|---|---|---|---|
| `02ZP` | Lemma 8.9.1 constructs stackification of a category fibred in groupoids: the induced Hom map identifies the target Hom sheaf with the sheafification of the source Hom presheaf, and every target object is locally in the essential image. | Definition of stackification; sheafification of morphisms/local essential image; full faithfulness when the source is already a prestack. | **match** in all three citing locations |
| `042Y` | Section 8.6 says a stack in sets is the same as a sheaf of sets; Lemma 8.6.2 states that, under the cited equivalence, stacks in sets correspond precisely to sheaves.  The section also gives the setoid formulation. | Identifies the sheaf of connected components with a sheaf of sets. | **match** |
| `00W1` | Section 7.10 is *Sheafification*.  It defines the plus construction from matching families over coverings, proves `F++` is a sheaf, and defines `F# = F++`. | General citation for the usual plus construction. | **match**, broad section locator |
| old `00W3` | Example 7.10.2 says the limit of the empty diagram is the final singleton presheaf and that this presheaf is a sheaf. | Previously cited for flattening a section of sheafification into local presheaf representatives. | **mismatch; corrected** |
| new `00WK` | Lemma 7.10.16 states that each section of `F#(U)` has representatives `s_i` in `F(U_i)` on a cover, whose two restrictions agree after a further cover of every pairwise overlap; conversely, such data determine a unique section of `F#(U)`. | Exact flattening/refined-overlap statement used in the proof. | **match** |
| historical `04TU` | Lemma 8.4.3 concerns when a subcategory of a stack is itself a stack; it is not the fully-faithful stackification statement used here. | Does not occur in the current manuscript; it had been rejected in an earlier round for the fully-faithful step. | **not cited; independently rechecked** |
| historical `06NY` | Section 8.11 is *Gerbes* and begins with the definition and invariance/basic properties of gerbes; it is not a statement of Giraud `H^2` naturality. | Does not occur in the current manuscript; it had been rejected in an earlier round for `H^2` naturality. | **not cited; independently rechecked** |

No tags `04TU` or `06NY` and no nLab/other wiki-style citations occur in the
current root manuscript.  Both historical tags were nevertheless fetched and
read again as recorded above.  The only current-source tag correction was
`00W3` -> `00WK` in `sec_null_decomposition.tex`; no theorem or proof content
changed.

### Audit limitations

- Crossref was available for DOI and title queries, but returned 404/empty for
  the valid Dagstuhl DOIs `10.4230/LIPIcs.CSL.2015.211` and
  `10.4230/LIPIcs.CSL.2021.5` and for the three `10.48550` arXiv DOIs.  Those
  five were checked against their official Dagstuhl or arXiv records.
- OpenAlex was unavailable for useful redundancy: every attempted request
  returned HTTP 429 / `Insufficient budget`, with the daily allowance at zero.
- Semantic Scholar was intermittently rate-limited with HTTP 429.  It returned
  usable exact records for `OkayRaussendorf2020` and `Kripke1965`; most other
  fallback attempts could not use it.
- Google Books returned HTTP 429 for every exact book query.  The affected
  books were routed to OpenLibrary, Crossref, and official Wiley, Dover,
  Cambridge, Springer, EMS, Dagstuhl, Cornell-author, or other publisher
  records as available.
- Oxford Research Archive was inaccessible to the command-line client because
  of a Cloudflare challenge, reducing checks for `MansfieldThesis`.
- Dynamic publisher pages sometimes exposed title/ISBN but not every edition
  field in machine-readable HTML; Crossref/OpenLibrary supplied complementary
  metadata.  Intended cross-source redundancy was therefore not achieved for
  the three unverified entries and was reduced for the five Crossref-empty
  DOI entries.  Service failure was never treated as evidence that a citation
  was false.

### Build and invariant record

Before the audit, `main.pdf` had 38 pages and `supplement.pdf` had 6 pages.
The compiled document trees contained 11 theorem/proposition/lemma/corollary
environments in the article and 1 in the supplement (12 total); all 62 such
environments across every repository `.tex` source, including sources not in
the current compiled document trees, were also counted.  Final after-audit
counts and command results are recorded below after the clean rebuild.

After the audit, `main.pdf` remains 38 pages and `supplement.pdf` remains 6
pages.  The compiled theorem-like counts remain 11 and 1 (12 total), and the
all-source count remains 62.  The largest `.tex` file is
`sec_homological_visibility.tex` at 726 lines; no `.tex` file reaches 800
lines.

The clean sequence removed each document's `.aux`, bootstrapped a fresh `.aux`
with `xelatex -no-pdf` while retaining the required `.fdb_latexmk` evidence,
and then ran `latexmk -pdfxe`.  The main/supplement alternation was repeated
once; the final pass used `latexmk -pdfxe -g` so XeLaTeX, BibTeX where
applicable, and PDF generation were actually rerun rather than accepted from
the bootstrap state.  Final `latexmk` exits were 0 for both documents.  Direct
scans of the final `main.log` and `supplement.log` found zero undefined
references, zero undefined citations, and zero multiply-defined labels.
`main.blg` reports 13 entries and `warning$ -- 0`, with no BibTeX error.  MiKTeX
also emitted its environment notice that this Windows version is unsupported;
that notice did not change either exit code or the final warning scans.  Build
logs and dependency files were retained.

Artifact script results:

- `artifacts/verify_A9_r1.py`: exit 0; four PASS blocks, covering 79,170
  enumerated/check instances (group-cocycle 6,561; tau rewrite 6,561; Cech
  cocycle 59,049; factorization 2,935; exact-sequence 3,896; seven groups and
  160 classification cases; one pullback-direction check).  Its intentional
  Peiffer counterexample and explicitly open NWW comparisons are not failures.
- `artifacts/test_verify_A9_r1.py`: exit 0; 5 tests run, 5 passed.
