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
   `10.1007/BF01305290`. No arXiv record located. Used only for the established
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
prior results and are not reproved as new.  Because the Atom API itself was
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
