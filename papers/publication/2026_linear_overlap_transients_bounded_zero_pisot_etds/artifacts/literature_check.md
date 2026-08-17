# Literature check

All fourteen entries in `references.bib` have exact title and lead-author
verification recorded here or in the companion paper's
`artifacts/literature_check.md`. Those audits identify the Crossref, arXiv,
zbMATH, or local companion-manuscript record used for each comparison.

Checked: 2026-08-16 (Asia/Singapore).

| Key | Identifier checked or found | Title/lead-author result |
|---|---|---|
| `CartonSudberyYassawi2026` | arXiv `2606.30496v2` | Exact: *From some Pisot numerations to topological groups* / Carton. The v2 abstract identifies preservation of zeros with Condition F for beta-numerations, supporting the manuscript's limited framework comparison. Submitted 2026-06-29; v2 dated 2026-08-08. |
| `MaZhang2026ExactOverlap` | Companion `main.tex` | Exact: *Exact overlap thresholds and future-only inverse depth for cyclic ranks of quadratic and simple-Parry beta-languages* / Ma; unpublished companion manuscript, 2026. |

## Eventual-acyclicity novelty search

Checked: 2026-08-17 (Asia/Singapore).

OpenAlex was searched for `cyclic rank recoding Pisot injectivity`, `bounded
zero representations Pisot automata`, `Pisot normalization transducer delay`,
`injective cellular automata inverse radius`, `sliding block code decoder
window`, `Pisot numeration overlap`, `cyclic rank modulo numeration`, and
`language rank modulo numeration`.  The exact-mechanism queries returned no
relevant work.  The closest records were Frougny's normalization and
synchronized-relation papers, Ashley's decoder-window papers, work on
parallel addition and representations of zero, and the standard cellular-
automata surveys.  None treats the moving family of rank-modulo-$u_m$
recodings or proves eventual acyclicity as the aperture tends to infinity.

The official arXiv search returned no results for either `"Pisot numeration"
injectivity` or `"representations of zero" Pisot`.  The zbMATH Open API was
searched for `cyclic rank Pisot injectivity`, `bounded zero representation
Pisot`, `sliding block decoder window`, `Pisot normalization automata`, and
`rational relations bounded delay`.  Its nearest records were Frougny,
*Representations of numbers and finite automata*; Frougny--Sakarovitch,
*Synchronized rational relations of finite and infinite words* and
*Rational relations with bounded delay*; and Ashley, *A linear bound for
sliding-block decoder window size* and its sequel.  The first group concerns
finite recognition or already synchronized relations, while Ashley's bound
is in the size of a presenting graph rather than in this aperture.

The full texts of Charlier--Cisternino--Masakova--Pelantova, *Spectrum,
algebraicity and normalization in alternate bases* (arXiv `2202.03718`), and
Frougny--Pelantova--Svobodova, *Parallel addition in non-standard numeration
systems* (arXiv `1102.5683`), were also searched for representations of zero,
Pisot contraction, delay, injectivity, and overlap.  They establish finite
automata for zero representations or local parallel arithmetic; they do not
contain an aperture-indexed acyclicity or inverse-depth theorem.  Semantic
Scholar and several broad Crossref requests returned HTTP 429 and are
recorded as rate-limited, not as zero-result searches.

The companion manuscript was searched separately.  It gives exact
quadratic thresholds, a general simple-Parry collision criterion, and an
exponential state-count bound, but no eventual injectivity theorem for all
Pisot systems.  Across these searches, no source states that the zero loop is
the only cycle for all sufficiently large apertures, that every fixed Pisot
cyclic rank recoding is eventually injective, or that the universal
asymptotic future-only inverse coefficient is one.
