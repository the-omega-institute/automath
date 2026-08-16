# Literature and novelty check: quadratic-Pisot Parry-rank folds

Checked: 2026-08-02 (Asia/Singapore).

## arXiv API query log

The required first-party Atom API was queried directly at
`https://export.arxiv.org/api/query` with the following searches:

- `all:(beta-expansion OR beta-numeration OR Pisot substitution)`, `max_results=50`;
- `au:Frougny`, `max_results=5`;
- `all:beta-expansion`, `max_results=10`.

Every request reached arXiv but returned HTTP `429` with
`cache-control: private, no-store` (Varnish edge: Singapore, upstream LGA).
Three delayed retries of the broad query returned the same status.  This is
recorded as an API availability limitation, not treated as a zero-result
novelty search.  To avoid a false novelty assertion, the audit was completed
against arXiv's first-party HTML search and abstract metadata, with DOI
metadata cross-checked through Crossref.

First-party arXiv exact-topic searches returned zero records for each of:

- `"finite-window beta fold"`;
- `"sliding-window beta normalization conjugacy"`;
- `"quadratic Pisot window threshold"`;
- `"Parry fold conjugacy"`;
- `"beta expansion sliding block conjugacy"`.

This supports only the narrow statement that no arXiv record located by these
queries states the paper's cyclic Parry-rank sliding-fold threshold.  It is
not proof that no unpublished or differently worded result exists.

## Closest beta-expansion and normalization literature

1. W. Parry, *On the beta-expansions of real numbers*, Acta Math. Acad. Sci.
   Hungar. **11** (1960), 401-416. DOI:
   `10.1007/BF02020954`. No arXiv record (publication predates arXiv).
   Used for the lexicographic admissibility criterion and `d_beta^*(1)`;
   the paper does not study cyclic finite-window folds or overlap thresholds.

2. C. Frougny, *Representations of numbers and finite automata*, Math.
   Systems Theory **25** (1992), 37-60. DOI:
   `10.1007/BF01368783`. No arXiv record located. Used only for the established
   finite-automaton normalization context; its automata are not presented as
   the cyclic rank-modulo-`Q_m` maps classified here.

3. C. Frougny and W. Steiner, *Minimal weight expansions in Pisot bases*,
   J. Math. Cryptology **2** (2008), 365-392. arXiv:`0803.2874`;
   DOI:`10.1515/JMC.2008.017`. It proves automaton recognizability for
   minimal-weight expansions in Pisot bases, not the present greedy
   Parry-rank fold or a sharp window threshold.

4. V. Berthe, C. Frougny, M. Rigo and J. Sakarovitch, *The carry propagation
   of the successor function*, Adv. Appl. Math. **120** (2020), 102062.
   arXiv:`1907.01464`; DOI:`10.1016/j.aam.2020.102062`. It studies amortized
   carry propagation in several numeration systems, including beta-numeration;
   it does not classify sliding-window conjugacy.

5. T. Hejda and W. Steiner, *Beta-expansions of rational numbers in quadratic
   Pisot bases*, Acta Arith. **183** (2018), 35-51.
   arXiv:`1411.2419`; DOI:`10.4064/aa8260-11-2017`. This is the closest
   full-quadratic-Pisot parameter comparison found. It studies purely periodic
   rational beta-expansions and computes `gamma(beta)`, not finite-window
   normalization or overlap injectivity.

6. B. Adamczewski, C. Frougny, A. Siegel and W. Steiner, *Rational numbers
   with purely periodic beta-expansion*, Bull. Lond. Math. Soc. **42** (2010),
   538-552. arXiv:`0907.0206`; DOI:`10.1112/blms/bdq019`. Relevant to
   periodic beta-expansions and Pisot-unit restrictions, but not to the cyclic
   fold threshold.

7. C. Kalle and W. Steiner, *Beta-expansions, natural extensions and multiple
   tilings associated with Pisot units*, Trans. Amer. Math. Soc. **364**
   (2012), 2281-2318. arXiv:`0907.2676`;
   DOI:`10.1090/S0002-9947-2012-05362-1`. It develops natural extensions and
   tilings arising from greedy beta-transformations; the abstract explicitly
   traces that geometric construction to Rauzy and Thurston. It does not
   contain the rank-modulo finite-window code studied here.

8. M. Minervino and W. Steiner, *Tilings for Pisot beta numeration*,
   arXiv:`1310.1277`. This treats Rauzy/beta tiles, weak finiteness, and purely
   periodic expansions for non-unit Pisot numbers; no DOI was exposed in the
   arXiv metadata checked. It supplies context for non-unit bases, not the
   claimed threshold.

## Thurston and Pisot-substitution boundary

W. Thurston's *Groups, tilings, and finite state automata* (AMS Colloquium
Lectures, 1989) is an unpublished lecture manuscript commonly cited for
beta-tiles; no arXiv ID or DOI was located.  The present manuscript therefore
does not assign it a fabricated identifier.  The traceable modern source used
for the Rauzy-Thurston statement is Kalle-Steiner, arXiv:`0907.2676`, DOI
`10.1090/S0002-9947-2012-05362-1`.

For the broader substitution interface, representative records are:

- M. Minervino and J. Thuswaldner, *The geometry of non-unit Pisot
  substitutions*, arXiv:`1402.2002`, Ann. Inst. Fourier **64** (2014),
  1373-1417, DOI:`10.5802/aif.2884`;
- V. Berthe, W. Steiner and J. Thuswaldner, *Geometry, dynamics, and
  arithmetic of S-adic shifts*, arXiv:`1410.0331`, Ann. Inst. Fourier **69**
  (2019), 1347-1409, DOI:`10.5802/aif.3273`;
- K. Nakaishi, *Pisot Substitution Conjecture and Rauzy Fractals*,
  arXiv:`2401.07771` (no DOI in the checked arXiv metadata).

These concern Rauzy fractals, substitutions, tilings, or spectral questions.
They are not predecessors of the cyclic finite-window rank fold.  Accordingly
the theorem is explicitly restricted to greedy quadratic beta-shifts and does
not claim a threshold for general Pisot substitutions.

## Novelty conclusion and limitation

The exact result not found in the checked records is the classification of the
least nontrivial aperture at which the cyclic Parry-rank fold from the full
digit shift is a conjugacy onto its SFT image, together with the two extremal
quadratic-Pisot loci.  Parry admissibility, Pisot normalization automata,
periodic expansions, beta-tiles, and Pisot-substitution geometry are cited as
prior results and are not claimed here. Because the Atom API itself was
rate-limited, the novelty conclusion remains a documented search conclusion,
not a claim of exhaustive bibliographic nonexistence.

## Follow-up API audit for the local-structure results

Checked: 2026-08-03 (Asia/Singapore).  The first-party Atom endpoint was
available for this audit.  Each request returned HTTP 200.  The exact query
`all:"cyclic rank recoding"` returned zero records.  The following broader
queries also returned zero records:

- `all:("quadratic Pisot" AND "sliding block")`;
- `all:("quadratic Pisot" AND "causal decoding")`;
- `all:("beta-expansion" AND "finite window" AND conjugacy)`;
- `all:("bounded coefficient" AND "polynomial multiple")`;
- `all:("Fischer cover" AND "full shift")`;
- `all:("Parry" AND "quadratic Pisot" AND language)`;
- `all:("beta-shifts" AND "same language")`.

The query `all:("near Markov" AND sofic)` returned one record,
Marcus--Meyerovitch--Wu, *A Krieger Embedding Theorem for Near Markov Sofic
Shifts*, arXiv:2606.25475.  It proves an embedding theorem for the established
near-Markov class; it does not contain the cyclic Parry-rank recoding, the
two-fixed-point extremal family, or its Fischer presentation.  The query
`au:Jankauskas_J AND all:Littlewood` returned Drungilas--Jankauskas--
Junevicius--Klebonas--Siurys, *On certain multiples of Littlewood and Newman
polynomials*, arXiv:1801.07179.  That paper studies divisibility between
Littlewood and Newman polynomials.  It does not identify a bounded multiple
degree with the causal inverse length of a sliding cyclic rank code.

These searches locate no arXiv predecessor for: the aperture-two
cross-chamber equality and aperture-three separation law; the exact causal
lengths two and three; the family-specific critical two-fixed-point normal
form; or the exact finite-block onset and Markov order.  The manuscript cites
Parry admissibility, bounded-polynomial-multiple terminology, near-Markov
terminology, and the general Fischer-cover criterion as prior framework and
claims only the parameter-specific deductions for its newly defined recoding.

## Follow-up API audit for the simple-Parry causal obstructions

Checked: 2026-08-03 (Asia/Singapore).  The first-party arXiv Atom endpoint
returned HTTP 200 for every query.  The following searches returned zero
records:

- `all:"cyclic language rank"`;
- `all:"bounded sliding congruence"`;
- `all:multinacci AND all:"sliding block"`;
- `all:Pisot AND all:"causal inverse"`;
- `all:"Littlewood multiple" AND all:Pisot`;
- `all:"restricted coefficient" AND all:"polynomial multiple"`;
- `all:"finite delay" AND all:"sliding block code"`;
- `all:"simple Parry" AND all:"language rank"`;
- `all:p-bonacci AND all:Pisot`.

The broader query `all:"multinacci number"` returned nine records.  The
closest was the established beta-numeration literature, including Kalle,
*Isomorphisms between positive and negative beta-transformations*,
arXiv:1203.4695, DOI `10.1017/etds.2012.127`; none studies rank reduction
modulo the legal-word count, the bounded sliding-congruence depth, or either
causal separation proved here.

Crossref bibliographic and OpenAlex full-text searches were also run for
`cyclic Parry rank recoding`, `bounded sliding congruence Pisot`, `multinacci
sliding block inverse`, `Pisot causal inverse symbolic dynamics`, `restricted
coefficient polynomial multiples`, `finite delay sliding block code inverse`,
`simple Parry language rank`, and `multinacci Pisot number`.  Their relevant
hits were the classical or established inputs, not predecessors of the
map-specific statements:

- K. Schmidt, *On Periodic Expansions of Pisot Numbers and Salem Numbers*,
  Bull. Lond. Math. Soc. **12** (1980), 269--278,
  DOI `10.1112/blms/12.4.269`;
- E. Charlier, C. Cisternino and M. Stipulanti, *A Full Characterization of
  Bertrand Numeration Systems*, 2022, arXiv:2202.04938,
  DOI `10.1007/978-3-031-05578-2_8`;
- P. Drungilas et al., *On Littlewood and Newman Polynomial Multiples of
  Borwein Polynomials*, Math. Comp. **87** (2018),
  DOI `10.1090/mcom/3258`, with preprint arXiv:1609.07295;
- D. Dombek, Z. Masakova and T. Vavra, *Confluent Parry numbers, their
  spectra, and integers in positive- and negative-base number systems*,
  J. Theor. Nombres Bordeaux **27** (2015), DOI `10.5802/jtnb.922`,
  arXiv:1402.4314.

Parry admissibility, Pisot eventual periodicity, multinacci bases, general
fiber-product collision graphs, and restricted-coefficient polynomial
multiples are therefore treated as published framework.  No checked record
states the exact Toeplitz obstruction formula for this cyclic language-rank
fold, the unbounded `p-2` separation, or the reverse cubic inequality.

## Independent refresh for the cubic upgrade and named nearest work

Checked: 2026-08-08 (Asia/Singapore).

The arXiv Atom API was queried for `"cyclic language rank"`, `"cubic
Pisot" AND "causal"`, `"Bertrand numeration" AND "sliding block"`,
`"finite delay" AND "beta-expansion"`, and the exact Bassino title.  The
endpoint returned HTTP 429 with `cache-control: private, no-store` through the
LGA/Singapore Varnish route.  This is an API availability failure, not a
zero-result search.  Google Scholar title/mechanism searches and Crossref
bibliographic searches were therefore used as independent discovery checks.

Crossref confirmed the following nearest-work records and DOI metadata:

- P. B. A. Lecomte and M. Rigo, *Numeration Systems on a Regular Language*,
  Theory Comput. Systems **34** (2001), 27--44,
  DOI `10.1007/s002240010014`.  Its published abstract introduces abstract
  numeration by ordering an arbitrary infinite regular language and studies
  finite-automaton recognizability.  It supplies the ordered-language stage,
  not cyclic reduction modulo a fixed-length language count or overlap
  injectivity.
- V. Bruyere and G. Hansel, *Bertrand numeration systems and
  recognizability*, Theoret. Comput. Sci. **181** (1997), 17--43,
  DOI `10.1016/S0304-3975(96)00260-5`.  Its 26-item Crossref reference trail
  includes Bertrand-Mathis, Parry, Frougny, Cobham, Shallit, and the classical
  automata/linear-numeration literature.  It concerns Bertrand systems and
  recognizable sets, not the manuscript's rank-modulo-`Q_m` sliding map.
- F. Bassino, *Beta-Expansions for Cubic Pisot Numbers*, LATIN 2002,
  pp. 141--152, DOI `10.1007/3-540-45995-2_17`.  The abstract states that the
  expansion of one is computed for every cubic Pisot number and that cubic
  simple beta-numbers are Pisot.  Its references include Akiyama, Boyd,
  Frougny--Solomyak, Hollander, Parry, Schmidt, and Solomyak.  Consequently,
  the Pisot/simple-Parry expansion data for the candidate cubic family are
  published input, not a novelty claim.

Exact Google Scholar searches for `"cyclic language rank" Pisot` and for the
polynomial string `"x^3-(n+2)x^2+2nx-n"` returned no matching scholarly
title.  The broader search `"cubic Pisot" "sliding block"` returned work on
beta-shifts/S-gap shifts and general automata material, not a cyclic
language-rank fold.  Crossref searches for `cubic Pisot causal inverse`,
`finite delay sliding block beta expansion`, and the exact polynomial found
Bassino and established beta-expansion/arithmetic papers but no causal-depth
or overlap-threshold predecessor.

The defensible novelty boundary is therefore narrow.  Ordered regular-
language numeration, Bertrand recognizability, cubic Pisot expansions, and
simple-Parry admissibility are prior art. The cubic statement is the
parameter-uniform modulus-`Q_m` collision-depth theorem.  Its required
all-parameter two-window carry exclusion and terminal-path induction are now
proved in the manuscript; no novelty is claimed for Bassino's expansion data.

The zbMATH Open API supplied the MathSciNet-style subject-index check.  Exact
title searches returned Lecomte--Rigo as Zbl `0969.68095`,
Bruyere--Hansel as Zbl `0957.11015`, and Bassino as Zbl `1152.11342`.
The Bassino query also returned Akiyama's *Cubic Pisot units with finite beta
expansions* (Zbl `1001.11038`) and the established periodic-expansion
literature.  Searches for `cubic Pisot causal inverse` and `cyclic language
rank Pisot` returned no zbMATH record.  These negative results have the same
query-language limitation as the other database searches and are not treated
as proof of bibliographic nonexistence.

## Deep-exploration refresh: causal completeness and aperture two

Checked: 2026-08-08 (Asia/Singapore).

The arXiv Atom API was queried for `right-closing`, `finite delay` together
with `symbolic dynamics`, `simple Parry`, `sliding block code`, and `cyclic
language rank`.  The exact mechanism queries returned no relevant record;
the broad `sliding block code` query returned general Curtis--Hedlund--Lyndon
and coding papers, not a cyclic rank-modulo-`Q_m` fold.  Crossref and Semantic
Scholar returned HTTP 429 on the fresh broad searches.  This is an API rate
limit, not a zero-result claim; the confirmed DOI metadata in this
file remains the Crossref evidence used for the named comparators.

The zbMATH Open API returned Nasu's *Textile systems for endomorphisms and
automorphisms of the shift* (Zbl `0845.54031`) and Ashley's *Resolving factor
maps for shifts of finite type with equal entropy* (Zbl `0741.54014`) as the
nearest general resolving-code framework.  Exact-title checks again returned
Bruyere--Hansel (Zbl `0957.11015`), Lecomte--Rigo (Zbl `0969.68095`), and
Bassino (Zbl `1152.11342`) for the numeration and cubic-expansion inputs.
These sources cover resolving codes, fiber-product/textile methods, ordered
regular-language numeration, and simple-Parry data.  None of the checked
records states that injectivity of this article's cyclic language-rank fold
forces a finite future-only inverse, supplies the map-specific state-count
and periodic-witness bounds, or classifies its aperture-two branch locus from
the second Parry digit.

## Tier-up refresh: unbounded cubic causal depth

Checked: 2026-08-10 (Asia/Singapore).

- The arXiv Atom API query for `"beta expansion"` together with Pisot,
  normalization, or transducer terms returned 15 records.  The closest
  mechanism-level results were Panju's *Beta Expansions for Regular Pisot
  Numbers* (arXiv:1103.2147), Kalle--Steiner's work on Pisot-unit natural
  extensions (arXiv:0907.2676), and the established cubic/multinacci
  literature.  The exact query combining `x^3`, Pisot, and beta expansion
  returned zero records.  This is only a query result, not a nonexistence
  proof.
- Crossref reconfirmed Bassino, Lecomte--Rigo, Bruyere--Hansel, and the
  standard Pisot beta-numeration literature as the nearest records.  A query
  containing the exact polynomial family returned no mathematically relevant
  item.
- Semantic Scholar's public Graph API search returned HTTP 429, and its public
  HTML search surface did not expose stable result metadata to the client.
  This is recorded as a rate-limited search, not as a zero-result claim.
- The zbMATH Open API exact-title search returned Bassino's record
  `Zbl 1152.11342` (document 2086225, DOI
  `10.1007/3-540-45995-2_17`).  Its classification is 11R06/11A67.  The
  earlier exact mechanism searches in this artifact returned no cyclic-rank
  or causal-depth predecessor.

Nearest prior work remains Fr\'ed\'erique Bassino, *Beta-Expansions for Cubic
Pisot Numbers*, LATIN 2002.  It supplies the cubic Pisot/simple-Parry
expansion data.  Lecomte--Rigo and Bruyere--Hansel supply the nearest ordered-
language and Bertrand-numeration frameworks.  None of these sources states
the parameter-uniform rank-modulo-`Q_m` two-window carry exclusion, the exact
terminal collision paths, or the unbounded causal-depth conclusion proved
here.

## Tier-2 audit: externally posed open problems and actual interfaces

Checked: 2026-08-14 (Asia/Singapore).

### Search record and open status

The arXiv Atom API was queried for Salem-number beta expansions, purely
periodic Pisot expansions, weak finiteness, Property (F), and the Pisot
substitution conjecture.  Primary sources arXiv:1411.2419, arXiv:1912.10386,
arXiv:1810.03500, arXiv:2206.06675, and arXiv:2603.19554 were inspected in
full text.  Crossref and OpenAlex returned HTTP 429 and are recorded as
rate-limited, not as zero-result searches.  Semantic Scholar returned the
records for DOI `10.4064/aa8260-11-2017`, `10.1112/blms/12.4.269`, and
`10.1017/etds.2016.44`; its citation graph lists only two citations of
Hejda--Steiner, neither claiming a solution of the questions below.  The
zbMATH Open API was searched for `purely periodic Pisot`, `Pisot substitution
conjecture`, and `Salem Parry Schmidt`.  Its post-2018 real-base results do
not report a resolution of the Hejda--Steiner questions.  Its review of E.
Miyanohara, *A note on non-periodic greedy expansions in Salem base*, Res.
Number Theory **10** (2024), DOI `10.1007/s40993-024-00507-8`, still calls
Salem eventual periodicity an open question.  The 2022 result arXiv:2206.06675
proves that a positive-density set of powers of a Salem number are Parry,
not that the Salem number itself is Parry.  These checks support the open
status assertions below as of the audit date.

### Four printed questions

1. **Schmidt's Salem--Parry conjecture.**  K. Schmidt, *On periodic
   expansions of Pisot numbers and Salem numbers*, Bull. Lond. Math. Soc.
   **12** (1980), 269--278, DOI `10.1112/blms/12.4.269`.  Stockton's explicit
   statement of Schmidt's conjecture in *On the co-factors of degree 6 Salem
   number beta expansions*, Int. J. Number Theory **17** (2021), 1175--1200,
   DOI `10.1142/S1793042121500317`, arXiv:1912.10386, reads: "Schmidt
   conjectured that the same was true for
   Salem numbers," where "the same" is that `beta` is a Parry number, i.e.
   `d_beta(1)` is eventually periodic.  Stockton adds: "it is still not known
   for any degree greater than 4."

2. **Hejda--Steiner Question (A).**  T. Hejda and W. Steiner,
   *Beta-expansions of rational numbers in quadratic Pisot bases*, Acta Arith.
   **183** (2018), 35--51, DOI `10.4064/aa8260-11-2017`, arXiv:1411.2419,
   Section 5, final open-problems list: "Prove or disprove that
   $\gamma(\beta)=1$ for quadratic Pisot number
   $\beta>1$, a root of $\beta^2=a\beta+b$, if and only if
   $a/b\in\mathbb Z$ and $a\ge b^2$ or
   $(a,b)\in\{(24,6),(30,6)\}$."

3. **Hejda--Steiner Question (B).**  Same citation and open-problems list:
   "For which
   quadratic $\beta$ we have that $\gamma(\beta)=0$? Can we drop the
   restrictions on $a$ and $b$ in Theorem 2? More specifically, is it true
   that $a<\frac{1+\sqrt5}{2}b$ implies $\gamma(\beta)=0$?"

4. **Hejda--Steiner Question (C).**  Same citation and open-problems list:
   "What is the
   structure of the prefixes of $\beta$-adic expansions of integers for a
   general quadratic $\beta$?"

### Machinery-to-problem map

- **Schmidt.**  The finite Parry word and recurrence used in
  `thm:simple-parry-causal-collision` exist only after the desired eventual
  periodicity (and, in the paper, the stronger simple-Parry property) is
  known.  The collision graph can analyze a Salem base already known to be
  simple Parry, but it supplies no bounded orbit for `T_beta(1)`.  The missing
  step is exactly the conjecture, so applying the graph would be circular.
- **Question (A).**  `prop:parry-rank-bijection` and
  `thm:full-quadratic-pisot-threshold` cover precisely the roots
  `beta^2=a beta+b` and give their legal languages and count recurrence.
  However, `gamma(beta)` is defined by equality of real beta-values and the
  beta-natural-extension domain.  The paper reduces an integer language rank
  modulo `Q_m`.  A bridge would have to identify these congruence fibers with
  beta-adic/natural-extension fibers or establish the required tile-boundary
  inclusion; no such identity is present, and the paper gives an explicit
  example showing rank congruence does not preserve beta-value.
- **Question (B).**  The nearest-multiple separation lemma controls multiples
  of the integer word count `Q_m`, not the conjugate-coordinate extrema that
  determine `gamma(beta)`.  What is missing is a uniform beta-tile boundary
  estimate in the parameter range `a<phi b`.  None of the sliding congruence
  estimates has that geometric conclusion.
- **Question (C).**  The closest objects are the standard Parry language,
  its colex rank, and the prefix counts `Q_m`.  The paper's cyclic rank fold
  discards the compatible inverse-system data needed for a beta-adic integer.
  A canonical map would require compatibility of the residues as `m` varies;
  the current moduli `Q_m` do not divide one another, and no bonding maps are
  proved.  Thus the finite-window results do not determine beta-adic prefix
  structure.

### A/B/C/D assessment and selected route

- **(A):** no named problem above is honestly touched beyond sharing the
  Parry language.  The numerical-value, natural-extension, or substitution
  geometry needed by each is absent.
- **(B):** the input full shift, greedy beta-language, Parry word, language
  counts, and colex ordered-language rank are standard.  The reduction modulo
  `Q_m` is bespoke.  Above threshold the image is canonically conjugate back
  to a full shift, so it does not yield an additional invariant of a standard
  beta-system.  There is no canonical map to numerical beta-normalization.
- **(C):** the Pisot hypothesis in the exact collision criterion, causal
  completeness, bounded-multiple order, and aperture-two trichotomy is an
  artifact: their proofs use only simple-Parry language/rank data and finite
  congruence graphs.  The simple-Parry hypothesis itself is real because it
  supplies the finite recurrence and positional colex rank used by the graph.
- **(D):** the negative-conjugate conjecture `ell_cau(beta,m)=2` for `m>=4`
  remains plausible, but a proof would sharpen only the bespoke decoder and
  the current carry analysis does not exhaust the nonzero constant-carry
  branches.  No plausible converse links overlap injectivity to a standard
  beta-expansion property.

Route **(C)** was selected as the best product of feasibility and impact.
Proposition `prop:nonpisot-simple-parry-scope` removes Pisot from the four
general simple-Parry results.  Strictness is proved using the irreducible
non-Pisot simple-Parry polynomial `x^4-2x^3-2`, for which
`d_beta(1)=2002 0^infinity` and `ell_cau(beta,2)=2`.  This is a genuine
hypothesis removal, but it does not solve a named problem and does not by
itself move the paper to Tier 2.

## Full bibliography identity audit

Checked: 2026-08-15 (Asia/Singapore).

The 40 cited entries in `sections/bibliography.tex`, together with 25 sources
used in the novelty searches above, were parsed individually. For every
printed DOI, the Crossref work record was fetched by DOI and its title and lead
author were compared with the entry. For every item without a DOI, Crossref
was searched by full bibliographic citation and then, where the top hit was
not exact, by title and lead author. Exact arXiv Atom records and zbMATH Open
records were used for the remaining preprints and non-Crossref items. A hit
counted as verified only when both title and lead author agreed.

| Key | Identifier checked or found | Title/lead-author result |
|---|---|---|
| `Akiyama2000` | Crossref `10.1515/9783110801958.11` | Exact: *Cubic Pisot units with finite beta expansions* / Akiyama |
| `AmorosoPatt1972` | printed DOI `10.1016/S0022-0000(72)80013-8` | Exact / Amoroso |
| `AlloucheShallit2003` | Crossref `10.1017/CBO9780511546563` | Exact: *Automatic Sequences* / Allouche |
| `Ashley1991` | Crossref `10.1017/S0143385700006118` | Exact / Ashley |
| `Ashley1988` | printed DOI `10.1109/18.6020` | Exact / Ashley |
| `Ashley1996` | printed DOI `10.1109/18.556684` | Exact / Ashley |
| `BaakeGrimm2013` | Crossref `10.1017/CBO9781139025256` | Exact: *Aperiodic Order* / Baake |
| `BaakeRobertsYassawi2018` | Crossref `10.3934/dcds.2018036` | Exact / Baake |
| `BanksOprochaStanley2015` | Crossref `10.3934/dcds.2015.35.4743` | Exact / Banks |
| `Bassino2002` | printed DOI `10.1007/3-540-45995-2_17` | Exact / Bassino |
| `Berstel2001` | Crossref `10.1051/ita:2001127` | Exact / Berstel |
| `Berthe2001Ostrowski` | Crossref `10.36045/bbms/1102714170` | Exact / Berthe |
| `BertheRigo2010` | Crossref `10.1017/CBO9780511777653` | Exact / Berthe (editor) |
| `BertheFrougnyRigoSakarovitch2019` | printed DOI `10.1016/j.aam.2020.102062` | Exact / Berthe |
| `BertheSteinerThuswaldner2019` | Crossref `10.5802/aif.3273` | Exact / Berthe |
| `BertrandMathis1986` | Crossref `10.24033/bsmf.2058` | Exact / Bertrand-Mathis |
| `BertrandMathis1989` | printed DOI `10.1007/BF01952053` | Exact / Bertrand-Mathis |
| `BerendFrougny1994` | Crossref `10.1007/BF01578846` | Exact / Berend |
| `Blanchard1989` | Crossref `10.1016/0304-3975(89)90038-8` | Exact / Blanchard |
| `Boyle1983` | Crossref `10.1017/S0143385700002133` | Exact / Boyle |
| `BoyleKitchensMarcus1985` | Crossref `10.1090/S0002-9939-1985-0806078-7` | Exact / Boyle |
| `BruyereHansel1997` | printed DOI `10.1016/S0304-3975(96)00260-5` | Exact / Bruyere |
| `CharlierCisterninoStipulanti2022` | printed DOI `10.1007/978-3-031-05578-2_8` | Exact / Charlier |
| `CartonSudberyYassawi2026` | arXiv `2606.30496v2` | Exact / Carton; no DOI in the checked record |
| `CoverThomas2006` | Crossref `10.1002/047174882X` | Exact: *Elements of Information Theory* / Cover |
| `DrmotaTichy1997` | Crossref `10.1007/BFb0093404` | Exact / Drmota |
| `DrungilasEtAl2018` | zbMATH document `6982157` | Exact / Drungilas; printed DOI was invalid and was removed |
| `Fischer1975` | Crossref `10.1007/BF01319913` | Exact / Fischer |
| `Frougny1992` | Crossref `10.1007/BF01368783` | Exact / Frougny |
| `FrougnySakarovitch1991` | printed DOI `10.1007/BFb0020787` | Exact / Frougny |
| `FrougnySolomyak1992` | Crossref `10.1017/S0143385700007057` | Exact / Frougny |
| `FrougnySteiner2008` | printed DOI `10.1515/JMC.2008.017` | Exact / Frougny |
| `HejdaSteiner2018` | printed DOI `10.4064/aa8260-11-2017` | Exact / Hejda |
| `Gray2011` | Crossref `10.1007/978-1-4419-7970-4` | Exact / Gray |
| `Hedlund1969` | Crossref `10.1007/BF01691062` | Exact / Hedlund |
| `Head1989` | zbMATH document `4197448` | Exact / Head; no DOI in the checked record |
| `HieronymiTerry2018` | Crossref `10.1215/00294527-2017-0027` | Exact / Hieronymi |
| `ItoTakahashi1974` | Crossref `10.2969/jmsj/02610033` | Exact / Ito |
| `Jagannathan2021` | Crossref `10.1103/RevModPhys.93.045001` | Exact / Jagannathan |
| `Kalle2014` | printed DOI `10.1017/etds.2012.127` | Exact / Kalle |
| `Johansen2011` | Crossref `10.4171/DM/328` | Exact / Johansen |
| `Kitchens1998` | Crossref `10.1007/978-3-642-58822-8` | Exact: *Symbolic Dynamics* / Kitchens |
| `Koshy2001` | Crossref `10.1002/9781118033067` | Exact / Koshy |
| `Krieger1984` | Crossref `10.1007/BF02760631` | Exact / Krieger |
| `Krieger1987` | Crossref `10.1007/BF02790789` | Exact / Krieger |
| `KuipersNiederreiter1974` | zbMATH document `3440485` | Exact / Kuipers; Open Library also matched both authors |
| `LindMarcus1995` | Crossref `10.1017/CBO9780511626302` | Exact / Lind |
| `LecomteRigo2001` | printed DOI `10.1007/s002240010014` | Exact / Lecomte |
| `Loraud1995` | Crossref `10.5802/jtnb.153` | Exact / Loraud |
| `Lothaire2002` | Crossref `10.1017/CBO9781107326019` | Exact / Lothaire |
| `MarcusMeyerovitchWu2026` | arXiv `2606.25475v1` | Exact / Marcus; no DOI in the checked record |
| `Moody2000` | Crossref `10.1007/978-3-662-04253-3_6` | Exact / Moody |
| `MorseHedlund1940` | Crossref `10.2307/2371431` | Exact / Morse |
| `Nasu1995` | Crossref `10.1090/memo/0546` | Exact / Nasu |
| `Nasu1977` | printed DOI `10.1007/BF01768485` | Exact / Nasu |
| `Ostrowski1922` | Crossref `10.1007/BF02940581` | Exact / Ostrowski |
| `Parry1960` | printed DOI `10.1007/BF02020954` | Exact / Parry |
| `Queffelec2010` | Crossref `10.1007/978-3-642-11212-6` | Exact / Queffelec |
| `Renyi1957` | Crossref `10.1007/BF02020331` | Exact / Renyi |
| `Richardson1972` | printed DOI `10.1016/S0022-0000(72)80009-6` | Exact / Richardson |
| `Schmidt1980` | printed DOI `10.1112/blms/12.4.269` | Exact / Schmidt |
| `Shechtman1984` | Crossref `10.1103/PhysRevLett.53.1951` | Exact / Shechtman |
| `Stanley2012` | Crossref `10.1017/CBO9781139058520` | Exact / Stanley |
| `Walters1982` | Crossref `10.1007/978-1-4612-5775-2` | Exact / Walters |
| `Zeckendorf1972` | zbMATH document `3397597` | Exact / Zeckendorf; no DOI in the checked record |

### Corrections and limitations

- The bibliography originally printed `10.4134/BKMS.b170831` for
  `DrungilasEtAl2018`.  Crossref returned HTTP 404, the DOI registration-
  agency endpoint said `DOI does not exist`, and direct resolution returned
  HTTP 404.  zbMATH document `6982157` independently confirms the title,
  authors, journal, volume, year, and pages, so only the invalid DOI was
  removed; the genuine article was retained.
- An earlier paragraph in this artifact attached `10.1007/BF01305290` to
  Frougny's 1992 article.  Crossref shows that DOI belongs to V. Kurylev's
  1983 paper on a shortwave source and the Laplace operator.  The correct
  Crossref record for Frougny is `10.1007/BF01368783`, and the paragraph above
  has been corrected.
- The active bibliography contains only the 40 cited entries. Every DOI in
  that bibliography matches Crossref title and lead-author metadata; entries
  without a DOI have exact title and lead-author confirmation from Crossref,
  arXiv, or zbMATH.
- OpenAlex returned HTTP 429 for the attempted secondary checks of the
  Drungilas, Head, Kuipers--Niederreiter, Queffelec, and Zeckendorf records.
  Semantic Scholar likewise returned HTTP 429 for the Drungilas, Head,
  Kuipers--Niederreiter, and Zeckendorf searches.  Thus the intended
  Crossref/OpenAlex/Semantic-Scholar redundancy was not achieved for those
  records.  The exact zbMATH, Crossref book, Open Library, or arXiv checks
  identified in the table are the successful alternative sources.

## Post-revision orphan-reference cleanup

Checked: 2026-08-16 (Asia/Singapore).

After the consequences supplement and seven section files were removed, the
literal `thebibliography` still printed 41 entries although the surviving
sources cited only 25 distinct keys.  The following 16 entries were removed
from `sections/bibliography.tex`; none was re-cited because its supporting
claim left the manuscript in the revision:

| Key | Disposition and reason |
|---|---|
| `Ashley1988` | Removed.  It supported the deleted discussion of quantitative decoder-window theory; the surviving pair-graph paragraph does not make that claim. |
| `Ashley1996` | Removed for the same reason as `Ashley1988`. |
| `BaakeGrimm2013` | Removed.  It supported the deleted model-set geometry section. |
| `Berstel2001` | Removed.  It supported a deleted remark connecting the finite Fibonacci calculation to automaton normalization. |
| `BertheFrougnyRigoSakarovitch2019` | Removed.  It supported a deleted comparison with numerical normalization and carry propagation. |
| `DrmotaTichy1997` | Removed.  It supported a deleted discrepancy estimate in the certificates section. |
| `Frougny1992` | Removed.  It supported deleted Fibonacci-normalization and numerical-transducer comparisons.  The corrected DOI remains recorded in the identity audit above and in `references.bib`. |
| `FrougnySteiner2008` | Removed.  It supported the deleted numerical-normalization comparison. |
| `Gray2011` | Removed.  It supported deleted information-rate limits in the measurement-theory section. |
| `Kalle2014` | Removed.  It supported a deleted secondary comparison involving multinacci expansions. |
| `KuipersNiederreiter1974` | Removed.  It supported the deleted discrepancy estimate in the certificates section. |
| `Moody2000` | Removed.  It supported the deleted model-set geometry section. |
| `MorseHedlund1940` | Removed.  It supported deleted Sturmian-readout claims. |
| `Queffelec2010` | Removed.  It supported deleted Sturmian-readout claims. |
| `Schmidt1980` | Removed.  It supported a deleted contextual statement on eventual periodicity for Pisot bases; the surviving text assumes the stronger simple-Parry property directly. |
| `Walters1982` | Removed.  It supported a deleted variational-principle argument in the measurement-theory section. |

No entry was re-cited.  After cleanup and a clean rebuild, `main.aux` contains
25 printed bibliography keys and the manuscript sources contain 25 distinct
citation keys.  Both set differences are empty: there is no printed-but-
uncited entry and no cited-but-missing entry.  `references.bib` was left
unchanged as the directory's bibliographic record.
