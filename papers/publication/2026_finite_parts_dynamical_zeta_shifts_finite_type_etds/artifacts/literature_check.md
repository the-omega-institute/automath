# Literature and Novelty Check


## Nishioka source verification for the linear collision audit (16 August 2026)

The two similarly named sources used by the scalar lifting theorem were
checked separately.  They are by different authors and supply different
steps.

- **Kumiko Nishioka (1982):** *On a problem of Mahler for transcendency of
  function values*, J. Austral. Math. Soc. Ser. A **33** (1982), 386--393,
  DOI `10.1017/S1446788700018814`.  Crossref returns Kumiko Nishioka, volume
  33, issue 3, and pages 386--393; Semantic Scholar resolves the same DOI and
  links the Cambridge publisher PDF.  The Cambridge PDF was checked directly.
  Its theorem on p. 387 treats a transcendental convergent power series
  satisfying the algebraic equation (1.2), assumes coefficient-size and
  common-denominator bounds `log [a_h], log d_h <= c h^L`, the orbit conditions
  `T^i alpha != 0` and `g(T^i alpha) != 0`, and
  `M(p+N)n^2 < p^(2+1/L)`, and concludes that `f(alpha)` is transcendental.
  For the manuscript's equation, the checked substitution is
  `Tz=z^p`, `Q_0=P_0`, `Q_1=-P_1 u^p`, `g=P_0`, and
  `N=0, n=1, m=M=p, U=L=1`; the strict inequality is `p^2<p^3`.
  The manuscript's linear coefficient-height and denominator bounds give the
  printed growth hypothesis, while zero-freedom of `H=P_0/P_1` on the orbit
  gives `P_0(alpha^(p^i)) != 0` and analyticity.  Thus this source supports the
  algebraic-special-value implication used in the lifting theorem.

- **Keiji Nishioka (1985):** *Algebraic function solutions of a certain class
  of functional equations*, Arch. Math. (Basel) **44** (1985), 330--335,
  DOI `10.1007/BF01235775`.  **BIBLIOGRAPHIC RECORD VERIFIED; STATEMENT NOT
  VERIFIED.** Crossref and the official Springer record return Keiji Nishioka,
  volume 44, issue 4, and pages 330--335.  The original pages are
  subscription-only.  The prior exhausted retrieval finding is recorded in
  `artifacts/oracle_nishioka_blocker.md`; no paywall workaround was attempted
  in this pass.  John H. Loxton's zbMATH review Zbl `0568.12014` (`zbMATH`
  document `3906608`) gives a secondary restatement, but it is a third-party
  review and does not verify the original theorem's printed statement or
  hypotheses.  Consequently it does not close the algebraic-to-rational step.
  The exact one-variable statement still required is: for every integer
  `p >= 2` and every `H in C(z)^*`, every convergent Laurent-series germ `F`
  algebraic over `C(z)` and satisfying
  `F(z^p)=F(z)^p/H(z)` belongs to `C(z)`.

No priority conclusion is drawn from these checks.  Kumiko Nishioka's
imported interface and both bibliographic attributions are verified; Keiji
Nishioka's imported statement remains unverified.  None of this establishes
novelty of the new divisor and collision arguments.


## Full bibliography verification (15 August 2026)

This audit supersedes the verification status implied by the earlier thematic
searches. All 84 entries in `references.bib` were checked individually. For
the 74 entries carrying a DOI, the DOI and returned title were checked against
Crossref first, with OpenAlex or Semantic Scholar as fallbacks. For the 10
entries without a DOI, exact title and first-author matches were sought in
Crossref, OpenAlex, or Semantic Scholar; three arXiv records were additionally
confirmed from the arXiv Atom API by identifier, full title, and authors.
Database rate limits were not treated as negative evidence. The result is 81
verified entries and 3 entries left explicitly unverified; none was deleted or
replaced.

| BibTeX key | Title and first author | Identifier | Result | Evidence |
|---|---|---|---|---|
| `AtiyahTall1969GroupRepresentationsLambdaRings` | Group representations, (lambda)-rings and the (J)-homomorphism; M. F. Atiyah | DOI `10.1016/0040-9383(69)90015-9` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `AdachiSunada1987TwistedPF` | Twisted Perron--Frobenius theorem and $L$-functions; T. Adachi | DOI `10.1016/0022-1236(87)90014-0` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `AdlerKitchensMarcus1985FiniteGroupActions` | Finite group actions on shifts of finite type; R. L. Adler | DOI `10.1017/s0143385700002728` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `ArangoPinerosKeliherKeyes2022ChebotarevMertens` | Mertens' theorem for Chebotarev sets; S. Arango-Pi neros | DOI `10.1142/s1793042122500932` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `Baladi2018DynamicalZeta` | Dynamical Zeta Functions and Dynamical Determinants for Hyperbolic Maps; V. Baladi | DOI `10.1007/978-3-319-77661-3` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `BertheGouletOuelletNybergBroddaPerrinPetersen2026GroupLanguages` | Density of group languages in shift spaces; V. Berthe | DOI `10.1017/etds.2026.10318` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `BertheGouletOuelletPerrin2025RationalLanguagesDensity` | Density of Rational Languages Under Shift Invariant Measures; V. Berthe | DOI `10.4230/lipics.icalp.2025.143` | Verified | Semantic Scholar DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `BowenLanford1970Zeta` | Zeta functions of restrictions of the shift transformation; R. Bowen | No DOI | Verified | Crossref title/author; title and first author matched. |
| `BoyleSchmieding2017FiniteGroupExtensions` | Finite group extensions of shifts of finite type: $K$-theory, Parry and Livsic; M. Boyle | DOI `10.1017/etds.2015.87` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `BoyleCarlsenEilers2020FlowEquivalenceGSFT` | Flow equivalence of $G$-SFTs; M. Boyle | DOI `10.1090/tran/7981` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `Coles2025VassilievWritheAxiomA` | Vassiliev invariants and writhe for periodic orbits of Axiom A flows; S. Coles | DOI `10.1017/etds.2025.7` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `CrismaleDelVecchioGrisetaRossi2025NoncommutativeSkewProduct` | Non-commutative skew-product extension dynamical systems; V. Crismale | DOI `10.1017/etds.2025.9` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `DeJong2026PeriodicOrbitLengths` | On sets of periodic orbit lengths in finitely presented dynamical systems; H. de Jong | DOI `10.1017/etds.2026.10313` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `Epperlein2026FreeInertGSFTs` | Eventual conjugacy of free inert $G$-SFTs; J. Epperlein | DOI `10.1017/etds.2026.10309` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `DougallSharp2021AnosovGrowthGroupExtensions` | Anosov flows, growth rates on covers and group extensions of subshifts; R. Dougall | DOI `10.1007/s00222-020-00994-3` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `Hashimoto1989ZetaFiniteGraphs` | Zeta functions of finite graphs and representations of $p$-adic groups; K.-I. Hashimoto | No DOI | Verified | Crossref title/author; title and first author matched. |
| `Hashimoto1990ZetaLFunctionsFiniteGraphs` | On zeta and $L$-functions of finite graphs; K.-I. Hashimoto | DOI `10.1142/s0129167x90000204` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `Hashimoto1992ArtinDensityPrimeCycles` | Artin type $L$-functions and the density theorem for prime cycles on finite graphs; K.-I. Hashimoto | DOI `10.1142/s0129167x92000370` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `HasegawaSaito2016GraphMertens` | On graph theory Mertens' theorems; T. Hasegawa | DOI `10.1007/s00373-016-1710-2` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `Fiebig1993PeriodicFiniteGroupActions` | Periodic points and finite group actions on shifts of finite type; U.-R. Fiebig | DOI `10.1017/s0143385700007495` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `Fried1983PeriodicPointsTwistedCoefficients` | Periodic points and twisted coefficients; D. Fried | DOI `10.1007/bfb0061419` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `Fried1983HomologicalIdentitiesClosedOrbits` | Homological identities for closed orbits; D. Fried | DOI `10.1007/bf01389105` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `SilverWilliams2005InvariantFiniteGroupActions` | An invariant of finite group actions on shifts of finite type; D. S. Silver | DOI `10.1017/s0143385705000246` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `Humbert2025FirstRuelleResonance` | First Ruelle resonance for an Anosov flow with smooth potential; T. Humbert | DOI `10.1017/etds.2024.131` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `LindMarcus1995` | An Introduction to Symbolic Dynamics and Coding; D. Lind | DOI `10.1017/9781108899727` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `Matsumoto2016ExtensionsSubshiftsFiniteGroups` | On extensions of subshifts by finite groups; K. Matsumoto | DOI `10.1080/14689367.2016.1278430` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `KatsudaSunada1990ClosedOrbitsHomology` | Closed orbits in homology classes; A. Katsuda | DOI `10.1007/bf02699875` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `Jaerisch2015GroupExtendedMarkovSystems` | Group-extended Markov systems, amenability, and the Perron--Frobenius operator; J. Jaerisch | DOI `10.1090/s0002-9939-2014-12237-4` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `Jaerisch2016RecurrencePressureGroupExtensions` | Recurrence and pressure for group extensions; J. Jaerisch | DOI `10.1017/etds.2014.54` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `Knutson1973LambdaRings` | (lambda)-Rings and the Representation Theory of the Symmetric Group; D. Knutson | DOI `10.1007/bfb0069217` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `Lalley1987DistributionPeriodicOrbits` | Distribution of periodic orbits of symbolic and Axiom A flows; S. P. Lalley | DOI `10.1016/0196-8858(87)90012-1` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `Manning1971Axiom` | Axiom A diffeomorphisms have rational zeta functions; A. Manning | DOI `10.1112/blms/3.2.215` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `MeslizaNoorani1999FrobeniusMertens` | Teorem Mertens Bagi Orbit--Orbit Tertutup Subanjakan Mengikut Kelas Frobenius; Mesliza Mohamed | DOI `10.11113/matematika.v15.n.482` | **Unverified** | The official journal PDF confirms title, authors, volume, year, and pages, but DOI `10.11113/matematika.v15.n.482` returned no Crossref record; OpenAlex and Semantic Scholar requests were rate-limited, and Crossref title/author search found no match. DOI mapping unconfirmed. |
| `Noorani1995ChebotarevFiniteExtensions` | Teorem Chebotarev Untuk Perluasan Kumpulan Terhingga Bagi Anjakan Terhingga; M. S. M. Noorani | No DOI | **Unverified** | No DOI recorded. Exact title/author searches in Crossref returned no match; OpenAlex and Semantic Scholar were queried but rate-limited; an exact-title web search found no authoritative record. |
| `ArtinMazur1965PeriodicPoints` | On periodic points; M. Artin | DOI `10.2307/1970384` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `Parry1983PrimeOrbit` | An analogue of the prime number theorem for closed orbits of shifts of finite type and their suspensions; W. Parry | DOI `10.1007/bf02760669` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `Sharp1991Mertens` | An analogue of Mertens' theorem for closed orbits of Axiom A flows; R. Sharp | DOI `10.1007/bf01237365` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `MetropolisRota1983Necklaces` | Witt vectors and the algebra of necklaces; N. Metropolis | DOI `10.1016/0001-8708(83)90035-x` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `DressSiebeneicher1988BurnsideRing` | The Burnside ring of profinite groups and the Witt vector construction; A. W. M. Dress | DOI `10.1016/0001-8708(88)90055-x` | Verified | Crossref title/author; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `NooraniParry1992ChebotarevShifts` | A Chebotarev theorem for finite homogeneous extensions of shifts; M. S. M. Noorani | DOI `10.1007/bf02584816` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `Noorani1997HomogeneousExtensionsMarkov` | Ergodicity and weak-mixing of homogeneous extensions of measure-preserving transformations with applications to Markov shifts; M. S. M. Noorani | DOI `10.1007/bf01305969` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `Noorani2003ClosedOrbitsToral` | Closed orbits of ((G,tau))-extension of ergodic toral automorphisms; M. S. M. Noorani | DOI `10.1155/s0161171203208164` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `OHare2025FiniteDataRigidity` | Finite data rigidity for one-dimensional expanding maps; T. A. O'Hare | DOI `10.1017/etds.2024.83` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `NordinNoorani2021BouquetDyckOrbitGrowth` | Orbit growth of shift spaces induced by bouquet graphs and Dyck shifts; A. Nordin | DOI `10.3390/math9111268` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `NordinNooraniMohd2024OrbitGrowthSoficPFT` | Orbit growth of sofic shifts and periodic-finite-type shifts; A. Nordin | DOI `10.1007/s12346-024-01055-3` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `NordinNooraniMohd2025SoficDyckOrbitGrowth` | A certain class of sofic-Dyck shifts and its orbit growth; A. Nordin | DOI `10.1007/s00605-025-02094-x` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `Parry1999LivsicNonAbelian` | The Livsic periodic point theorem for non-abelian cocycles; W. Parry | DOI `10.1017/s0143385799146789` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `ParryPollicott1997LivsicCompactLie` | The Livsic cocycle equation for compact Lie group extensions of hyperbolic systems; W. Parry | DOI `10.1112/s0024610797005474` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `ParryPollicott1986Chebotarev` | The Chebotarov theorem for Galois coverings of Axiom A flows; W. Parry | DOI `10.1017/s0143385700003333` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `ParryPollicott1990Zeta` | Zeta Functions and the Periodic Orbit Structure of Hyperbolic Dynamics; W. Parry | No DOI | Verified | Semantic Scholar title; title and first author matched. |
| `ParryPollicott2008BauerSkewProducts` | An analogue of Bauer's theorem for closed orbits of skew products; W. Parry | DOI `10.1017/s0143385707000557` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `PollicottSharp2007Chebotarev` | Chebotarev-type theorems in homology classes; M. Pollicott | DOI `10.1090/s0002-9939-07-08923-x` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `PollicottSharp2008ArtinReciprocitySkewProducts` | Addendum: an analogue of Artin reciprocity for closed orbits of skew products; M. Pollicott | DOI `10.1017/s0143385707000569` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `Sharp1993ClosedOrbitsHomologyAnosov` | Closed orbits in homology classes for Anosov flows; R. Sharp | DOI `10.1017/s0143385700007434` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `Seneta2006NonnegativeMatrices` | Non-negative Matrices and Markov Chains; E. Seneta | DOI `10.1007/0-387-32792-4` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `Wielandt1950Unzerlegbare` | Unzerlegbare, nicht negative Matrizen; H. Wielandt | DOI `10.1007/bf02230720` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `Sunada1986LFunctionsGeometry` | $L$-functions in geometry and some applications; T. Sunada | DOI `10.1007/bfb0075662` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `Wehrhahn1990AperiodicRings` | Aperiodic rings, necklace rings, and Witt vectors; R. Wehrhahn | DOI `10.1016/0001-8708(90)90002-5` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `Ruelle1976ZetaExpanding` | Zeta-functions for expanding maps and Anosov flows; D. Ruelle | DOI `10.1007/bf01403069` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `AdamczewskiFaverjon2018MahlerSeveralVariablesII` | Mahler's method in several variables II: Applications to base change problems and finite automata; B. Adamczewski | No DOI | Verified | arXiv title/author; title and first author matched. |
| `Greuel2000ImplicitMahler` | Algebraic independence of the values of Mahler functions satisfying implicit functional equations; B. Greuel | DOI `10.4064/aa-93-1-1-20` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `Nishioka1982MahlerFunctionValues` | On a problem of Mahler for transcendency of function values; Kumiko Nishioka | DOI `10.1017/s1446788700018814` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `Nishioka1985AlgebraicSolutions` | Algebraic function solutions of a certain class of functional equations; Keiji Nishioka | DOI `10.1007/bf01235775` | **Bibliographic record verified; statement not verified** | Crossref and Springer metadata match. Original pages 330--335 are paywalled; Loxton's zbMATH review is only a secondary restatement. See `artifacts/oracle_nishioka_blocker.md`. |
| `Nishioka1996MahlerFunctions` | Mahler Functions and Transcendence; Kumiko Nishioka | No DOI | Verified | Crossref title/author; title and first author matched. |
| `Ostrowski1968AlgebraicSolutions` | Uber algebraische Losungen (Phi) der Funktionalgleichung (Phi(varphi(x))=g(x)Phi(x)), fur rationale (g(x)); A. Ostrowski | DOI `10.1007/bf01817565` | **Unverified** | DOI resolves in Crossref, but its metadata title is the Oberwolfach conference report rather than the cited article title; exact title/author searching did not give an unambiguous entry-level match, and Semantic Scholar was rate-limited. |
| `ChyzakDreyfusDumasMezzarobba2018MahlerSolutions` | Computing solutions of linear Mahler equations; F. Chyzak | DOI `10.1090/mcom/3359` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `ChyzakDreyfusDumasMezzarobba2025FirstOrderFactors` | First-order factors of linear Mahler operators; F. Chyzak | DOI `10.1016/j.jsc.2025.102424` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `ArrecheZhang2022MahlerResidues` | Mahler discrete residues and summability for rational functions; C. E. Arreche | DOI `10.1145/3476446.3536186` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `Pegis1996NonlinearMahler` | Rational solutions of a nonlinear functional equation related to Mahler's equation; C. Pegis | DOI `10.1006/jmaa.1996.0156` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `BellCoonsRowland2013MahlerDichotomy` | The rational-transcendental dichotomy of Mahler functions; J. P. Bell | No DOI | Verified | arXiv title/author; title and first author matched. |
| `PomeratStraub2024RootsPowerSeries` | Criteria for the integrality of $n$th roots of power series; J. Pomerat | DOI `10.4064/aa230425-4-4` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `Topfer1998ZeroOrderMahler` | Zero order estimates for functions satisfying generalized functional equations of Mahler type; T. Topfer | DOI `10.4064/aa-85-1-1-12` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `Lam2025ValuationProducts` | Transcendence and algebraic independence of a family of $p$-adic valuation generating functions; K. Lam | No DOI | Verified | arXiv title/author; title and first author matched. |
| `Stadlbauer2013KestenCriterionTMC` | An extension of Kestens criterion for amenability to topological Markov chains; M. Stadlbauer | DOI `10.1016/j.aim.2012.12.004` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `Ruelle1978Thermodynamic` | Thermodynamic Formalism; D. Ruelle | No DOI | Verified | Semantic Scholar title; title and first author matched. |
| `StarkTerras1996FiniteGraphsCoverings` | Zeta functions of finite graphs and coverings; H. M. Stark | DOI `10.1006/aima.1996.0050` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `StarkTerras2000FiniteGraphsCoveringsII` | Zeta functions of finite graphs and coverings, Part II; H. M. Stark | DOI `10.1006/aima.2000.1917` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `StarkTerras2007FiniteGraphsCoveringsIII` | Zeta functions of finite graphs and coverings, III; H. M. Stark | DOI `10.1016/j.aim.2006.03.002` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `Serre1977LinearRepresentations` | Linear Representations of Finite Groups; J.-P. Serre | DOI `10.1007/978-1-4684-9458-7` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `CavaleriDAngeliDonno2021BalanceGainGraphs` | A group representation approach to balance of gain graphs; M. Cavaleri | DOI `10.1007/s10801-020-00977-w` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `CavaleriDonno2022Cospectrality` | On cospectrality of gain graphs; M. Cavaleri | DOI `10.1515/spma-2022-0169` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `AbiadBelardoKhramova2024Switching` | A switching method for constructing cospectral gain graphs; A. Abiad | DOI `10.1016/j.disc.2023.113838` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `Zaslavsky1989BiasedGraphs` | Biased graphs. I. Bias, balance, and gains; T. Zaslavsky | DOI `10.1016/0095-8956(89)90063-4` | Verified | Crossref DOI; DOI resolved and the returned title matches, allowing for mathematical markup and diacritics. |
| `GrossTucker1987TopologicalGraphTheory` | Topological Graph Theory; J. L. Gross | No DOI | Verified | Semantic Scholar title; title and first author matched. |

The three unverified rows remain in the bibliography exactly as received. The
Mesliza--Noorani bibliographic record itself is supported by the official
journal PDF, but the DOI could not be validated in the required services. The
Ostrowski DOI may identify a containing conference report rather than an
article-level record; that ambiguity is reported rather than silently changed.
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
  outside that linear class. A secondary restatement attributes to Keiji
  Nishioka's 1985 paper a nonlinear class broad enough to cover
  `f(z^p) = f(z)^p/H(z)`. The original statement is not verified, so the new
  linear theorem quotes this exact implication as the assumption `(KN85)`.
- Springer keeps the cited 1985 pages 330--335 behind subscription, and
  Unpaywall reported no open-access copy; this audit does not record a
  first-hand check of the printed text.
- The paper's claimed Mahler contribution is limited to the input-only divisor
  estimates for the multiplicative certificate, the collision--jet
  inequality, the sharp lower-bound family and realizable transfer, and the
  supporting explicit height and fixed-base integer bit analysis. Bare
  existence and decidability are prior, and the Pade step is largely standard
  rational reconstruction after a degree cap is known. The headline remains
  the cross-base odd-Adams-invariant abelian-two-group dynamical inverse
  theorem with its `O(V log V)` radial budget.

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
one-way necessary condition. Additive solutions are determined only up to a
constant. After replacing `u` by its unique representative with `u(0)=0`, it
comes from a normalized `R in Q(z)` exactly when `u/z` is regular at zero,
has no polynomial part, and has only simple finite poles with integer
residues. Necessity
is the standard partial-fraction form of a rational logarithmic derivative.
For sufficiency, Galois invariance groups poles with the same integer residue
into rational irreducible factors; their normalized product gives
`R'/R=u/z` and `R(0)=1`.  Equation (1) then says that
`R(z^p)/(H(z)R(z)^p)` has zero logarithmic derivative.  Its value at zero is
one, so it is identically one.

Consequently, bare decidability of the multiplicative rational-solution
problem is already subsumed after this non-obvious transformation.  The
nontrivial surviving core is the input-only degree bound of sharp order
`D log D` for the multiplicative certificate itself, together with its lower-
bound family and dynamically realizable transfer. The explicit height and
fixed-`p` integer bit bounds are useful quantitative additions. The affine
Pade calculation is a direct implementation of standard rational
reconstruction once the degree cap is known, and exact rejection is necessary
for correctness rather than a separate novelty claim.
