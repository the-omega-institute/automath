# DOI integrity audit of every bibliography in papers/publication

Scope: all 34 `.bib` files under `papers/publication/`, 1176 entries, 517 distinct DOIs.
Each DOI was queried against the Crossref REST API; every DOI that Crossref did not return
was then resolved a second time through `doi.org` content negotiation, so that no entry is
reported as broken on the strength of a single lookup. arXiv, LIPIcs, Zenodo and figshare
DOIs are registered with DataCite rather than Crossref and are absent from Crossref by
design; the `doi.org` pass separates those from genuine failures.

Two defect classes were found. They are independent, and the second is not detectable by
any check that only asks whether a DOI resolves.

## Class A - the DOI resolves, but to a different work

The reference itself is a real paper. The DOI attached to it belongs to something else,
so a reader who follows the link arrives at an unrelated article. In one case
(`BrownFullerPittsReznikoff2024` and `JreisLefevre2024`, both in the JST paper) the two
DOIs are each other's: the entries were swapped.

| paper | key | DOI as printed | what that DOI actually is |
|---|---|---|---|
| `2026_auditable_theory_to_paper_pipeline` | `WillisEtAl2022WholeTale` | `10.1145/3491418.3530296` | A Framework to capture and reproduce the Absolute State - Wannipurage, Marru, Pierce (2022) |
| `2026_coefficient_sup_radial_homotopy_monomial_forms_jdde` | `DupontBook1978` | `10.1007/bfb0065193` | Locally finite simple groups - Kegel (None) |
| `2026_cubical_stokes_inverse_boundary_readout_jdsgt` | `DupontBook1978` | `10.1007/bfb0065193` | Locally finite simple groups - Kegel (None) |
| `2026_deterministic_telescoping_fold_truncation_defects_dynamical_systems` | `BaratGrabner2014` | `10.5802/jtnb.859` | Groupe de Brauer non ramifie d’espaces homogenes de tor - Colliot-Thélène (2015) |
| `2026_deterministic_telescoping_fold_truncation_defects_dynamical_systems` | `DrmotaSteiner2002` | `10.1007/s006050200022` | Calculation of Improper Integrals Using (nα)-Sequences - Baxa, Schoißengeier (2002) |
| `2026_deterministic_telescoping_fold_truncation_defects_dynamical_systems` | `Frougny1991` | `10.1109/18.75260` | 2-D quasi m-arrays and Gold code arrays - Kuo, Rigas (1991) |
| `2026_deterministic_telescoping_fold_truncation_defects_dynamical_systems` | `MillerWang2012` | `10.1016/j.jcta.2012.04.008` | A Fisher type inequality for weighted regular t-wise ba - Xiang (2012) |
| `2026_fibonacci_folding_zeckendorf_normalization_gauge_anomaly_spectral_fingerprints` | `BowerInsoftLiMillerTosteson2015` | `10.1016/j.jcta.2015.04.006` | The γ-positivity of basic Eulerian polynomials via grou - Lin, Zeng (2015) |
| `2026_fibonacci_folding_zeckendorf_normalization_gauge_anomaly_spectral_fingerprints` | `GrabnerTichy1990` | `10.1016/0022-314x(90)90047-u` | On two additive problems - Erdős, Freiman (1990) |
| `2026_fibonacci_folding_zeckendorf_normalization_gauge_anomaly_spectral_fingerprints` | `MillerWang2012` | `10.1016/j.jcta.2012.03.008` | On the homology of the real complement of the k-parabol - Severs, White (2012) |
| `2026_fibonacci_folding_zeckendorf_normalization_gauge_anomaly_spectral_fingerprints` | `SidorovVershik1998` | `10.1007/pl00004373` | A contact condition for  p  -codimensional submanifolds - Bolle (1998) |
| `2026_finite_parts_dynamical_zeta_shifts_finite_type_etds` | `Ostrowski1968AlgebraicSolutions` | `10.1007/bf01817565` | Die vierte Tagung uber Funktionalgleichungen Oberwolfac - von Kuczma (1968) |
| `2026_folded_histograms_sampling_certificates_parry_mismatch_etds` | `Berthe2001Ostrowski` | `10.36045/bbms/1102714038` | Premiers espaces de la cohomologie de l algebre de Lie - Poncin (2001) |
| `2026_fredholm_determinants_cyclic_block_spectral_rigidity_jst` | `BrownFullerPittsReznikoff2024` | `10.1007/s00020-023-02742-7` | Some Operator Ideal Properties of Volterra Operators on - Jreis, Lefèvre (2023) |
| `2026_fredholm_determinants_cyclic_block_spectral_rigidity_jst` | `Horn1954DoublyStochastic` | `10.2307/2032173` | The Reciprocal of a Continued Fraction - Scott (1952) |
| `2026_fredholm_determinants_cyclic_block_spectral_rigidity_jst` | `JreisLefevre2024` | `10.1007/s00020-023-02753-4` | Regular Ideals, Ideal Intersections, and Quotients - Brown, Fuller, Pitts, Reznikoff (2024) |
| `2026_fredholm_determinants_cyclic_block_spectral_rigidity_jst` | `VanNulandSkripka2022` | `10.4171/jst/431` | Inertia of Kraus matrices - Sano, Takeuchi (2023) |
| `2026_gluing_failure_visible_quotients_pure_ext_blind_spots_apal` | `AbramskyBarbosa2021` | `10.46298/lmcs-17(4:14)2021` | On Supergraphs Satisfying CMSO Properties - Oliveira (2021) |
| `2026_prefix_scan_error_boundary_rates_dynamical_systems` | `PollicottKempton2016` | `10.1090/proc/12974` | The minimal base size for a p-solvable linear group - Halasi, Maróti (2015) |
| `2026_recursive_addressing_prefix_sites_tac` | `StatonUijlen2018EffectAlgebras` | `10.23638/lmcs-14(3:18)2018` | Categorical structures for type theory in univalent fou - Ahrens, Lumsdaine, Voevodsky (2018) |
| `2026_scan_projection_address_semantics_sigma_nonexpansion_etds` | `HarithaAgarwal2019` | `10.3934/dcds.2019245` | Reflected solutions of backward doubly SDEs driven by B - Karouf (2019) |
| `2026_self_dual_synchronisation_kernel_completed_determinant_cyclotomic_twists` | `Ruelle1976` | `10.1007/bf01403062` | Variations sur un th�me de Mahler - Lachaud (1979) |
| `2026_zeckendorf_stable_arithmetic_fibonacci_congruence_online` | `Fraenkel1985` | `10.2307/2322658` | 6438 - Brenner, Netuka, Vesely (1985) |
| `submitted_2026_quartic_cover_37a1_regular_s4_closure_jnt` | `BrumerKramer2019` | `10.1090/tran/7457` | Groups of central-type, maximal connected gradings and - Ginosar, Schnabel (2019) |
| `submitted_2026_quartic_cover_37a1_regular_s4_closure_jnt` | `KaniRosen1989` | `10.1007/bf01442834` | Notiz �ber die algebraischen Minimumsfl�chen - Geiser (1871) |

## Class B - the DOI does not exist

Neither Crossref nor `doi.org` resolves these. The cited works are real and, in almost
every case, the correct DOI was located by a bibliographic search on title and author;
the failure is confined to the identifier string. The shape of the errors is consistent:
a correct publisher prefix followed by a suffix that is close to a real one but wrong.

| paper | key | DOI as printed | correct DOI |
|---|---|---|---|
| `2026_auditable_theory_to_paper_pipeline` | `ZimmermannEtAl2018SageMath` | `10.1137/1.9781611975461` | `10.1137/1.9781611975468` |
| `2026_coefficient_sup_radial_homotopy_monomial_forms_jdde` | `CostabelMcIntosh2010` | `10.1007/s00209-009-0588-5` | not established - see below |
| `2026_coefficient_sup_radial_homotopy_monomial_forms_jdde` | `Gillette2016` | `10.1007/s00211-015-0774-4` | `10.5802/smai-jcm.14` |
| `2026_coefficient_sup_radial_homotopy_monomial_forms_jdde` | `Grieser2006` | `10.1007/s00013-006-1784-5` | `10.1007/s00013-005-1623-4` |
| `2026_coefficient_sup_radial_homotopy_monomial_forms_jdde` | `IwaniecLutoborski1993` | `10.1007/bf00375001` | `10.1007/bf00411477` |
| `2026_cubical_stokes_inverse_boundary_readout_jdsgt` | `CostabelMcIntosh2010` | `10.1007/s00209-009-0588-5` | not established - see below |
| `2026_cubical_stokes_inverse_boundary_readout_jdsgt` | `Grieser2006` | `10.1007/s00013-006-1784-5` | `10.1007/s00013-005-1623-4` |
| `2026_cubical_stokes_inverse_boundary_readout_jdsgt` | `IwaniecLutoborski1993` | `10.1007/bf00375001` | `10.1007/bf00411477` |
| `2026_deterministic_telescoping_fold_truncation_defects_dynamical_systems` | `BertheRigo2007` | `10.1017/s0305004106000219` | `10.1007/s00224-005-1215-5` |
| `2026_deterministic_telescoping_fold_truncation_defects_dynamical_systems` | `Frougny1996Successor` | `10.1016/s0304-3975(96)00064-1` | `10.1007/3-540-60922-9_44` |
| `2026_deterministic_telescoping_fold_truncation_defects_dynamical_systems` | `Frougny1997Sequential` | `10.1051/ita:1997170605131` | `10.1006/inco.1997.2650` |
| `2026_deterministic_telescoping_fold_truncation_defects_dynamical_systems` | `FrougnySakarovitch1999` | `10.1016/s0304-3975(98)00324-2` | `10.1142/s0218196799000230` |
| `2026_deterministic_telescoping_fold_truncation_defects_dynamical_systems` | `Steiner2005` | `10.1007/s00605-005-0283-2` | `10.1080/00150517.2005.12428393` |
| `2026_fibonacci_folding_zeckendorf_normalization_gauge_anomaly_spectral_fingerprints` | `BerendFrougny1994` | `10.1007/bf01192620` | `10.1007/bf01578846` |
| `2026_fibonacci_folding_zeckendorf_normalization_gauge_anomaly_spectral_fingerprints` | `Blanchard1989` | `10.1016/0304-3975(89)90129-0` | `10.1016/0304-3975(89)90038-8` |
| `2026_fibonacci_folding_zeckendorf_normalization_gauge_anomaly_spectral_fingerprints` | `Frougny1988` | `10.1016/0890-5401(88)90032-1` | `10.1016/0890-5401(88)90050-8` |
| `2026_fibonacci_folding_zeckendorf_normalization_gauge_anomaly_spectral_fingerprints` | `FrougnyConfluent1992` | `10.1016/0304-3975(92)90031-k` | `10.1016/0304-3975(92)90249-f` |
| `2026_fibonacci_folding_zeckendorf_normalization_gauge_anomaly_spectral_fingerprints` | `GrabnerKirschenhoferTichy2002` | `10.1017/s0963548302005280` | `10.1007/s004930200011` |
| `2026_fibonacci_folding_zeckendorf_normalization_gauge_anomaly_spectral_fingerprints` | `GrabnerTichyNemesPetho1996` | `10.62091/fq/1996/34.2.y4` | `10.1080/00150517.1996.12429083` |
| `2026_fibonacci_folding_zeckendorf_normalization_gauge_anomaly_spectral_fingerprints` | `Griffiths2010` | `10.62091/fq/2010/48.2.y8` | `10.1080/00150517.2010.12428118` |
| `2026_fibonacci_folding_zeckendorf_normalization_gauge_anomaly_spectral_fingerprints` | `Heuberger2004` | `10.1023/b:mahu.0000047545.59892.0f` | `10.1007/s10998-004-0523-x` |
| `2026_fibonacci_folding_zeckendorf_normalization_gauge_anomaly_spectral_fingerprints` | `Idziaszek2021` | `10.4230/lipics.spire.2021.15` | not established - see below |
| `2026_finite_parts_dynamical_zeta_shifts_finite_type_etds` | `DressSiebeneicher1988BurnsideRing` | `10.1016/0001-8708(88)90055-x` | `10.1016/0001-8708(88)90052-7` |
| `2026_finite_parts_dynamical_zeta_shifts_finite_type_etds` | `MeslizaNoorani1999FrobeniusMertens` | `10.11113/matematika.v15.n.482` | not established - see below |
| `2026_finite_window_zeckendorf_thermodynamics_jnt` | `Sanna2025` | `10.19086/da.137601` | `10.19086/da./13760` |
| `2026_fredholm_determinants_cyclic_block_spectral_rigidity_jst` | `GesztesyMakarov2007` | `10.1007/s00020-006-1461-8` | not established - see below |
| `2026_gluing_failure_visible_quotients_pure_ext_blind_spots_apal` | `Galliani2021` | `10.1016/j.ic.2021.104657` | `10.1016/j.ic.2020.104593` |
| `2026_gluing_failure_visible_quotients_pure_ext_blind_spots_apal` | `OkaySheinbaum2021` | `10.1007/s00220-021-04046-2` | `10.1007/s00023-020-00993-3` |
| `2026_joukowsky_elliptic_godel_lorentz_mahler_capacity` | `Trefethen2013` | `10.1137/1.9781611972405` | `10.1137/1.9781611975949` |
| `2026_prefix_scan_error_boundary_rates_dynamical_systems` | `Verbitskiy2011` | `10.1007/s11005-010-0426-z` | `10.1017/cbo9780511819407.010` |
| `2026_scan_projection_address_semantics_sigma_nonexpansion_etds` | `ColletMartinezSanMartin2013` | `10.1007/978-3-642-32742-0` | not established - see below |
| `2026_scan_projection_address_semantics_sigma_nonexpansion_etds` | `FroylandStancevic2011` | `10.3934/dcds.2010.28.1315` | `10.3934/dcdsb.2010.14.457` |
| `2026_self_dual_synchronisation_kernel_completed_determinant_cyclotomic_twists` | `Apostol1970` | `10.1090/s0002-9939-1970-0252347-4` | `10.1090/s0002-9939-1970-0251010-x` |
| `2026_self_dual_synchronisation_kernel_completed_determinant_cyclotomic_twists` | `FoataZeilberger1999` | `10.1090/s0002-9947-99-02142-1` | not established - see below |
| `2026_zeckendorf_stable_arithmetic_fibonacci_congruence_online` | `BerendFrougny1994Pisot` | `10.1007/bf01192620` | `10.1007/bf01578846` |
| `2026_zeckendorf_stable_arithmetic_fibonacci_congruence_online` | `HieronymiTerry2018OstrowskiAddition` | `10.1215/00294527-2017-0040` | `10.1215/00294527-2017-0027` |
| `submitted_2026_quartic_cover_37a1_regular_s4_closure_jnt` | `BGK2003` | `10.4153/cjm-2003-022-0` | `10.2748/tmj/1277298644` |
| `submitted_2026_quartic_cover_37a1_regular_s4_closure_jnt` | `LangeOrtega2011` | `10.1007/s10711-010-9510-x` | `10.1007/s10711-010-9512-9` |
| `submitted_2026_quartic_cover_37a1_regular_s4_closure_jnt` | `LangeRodriguez2022` | `10.1007/978-3-031-11364-6` | `10.1007/978-3-031-10145-8` |

### Entries whose correct DOI was not established

For these the bibliographic search returned no confident match. That is not evidence that
the work does not exist - several are conference papers, book chapters or non-English
journal articles that are poorly indexed - but the printed DOI is wrong in every case and
must not be shipped.

- `CostabelMcIntosh2010` in `2026_coefficient_sup_radial_homotopy_monomial_forms_jdde`, printed `10.1007/s00209-009-0588-5`, cited as: On Bogovski     and Regularized  P oincar  e Integral Operators for de
- `CostabelMcIntosh2010` in `2026_cubical_stokes_inverse_boundary_readout_jdsgt`, printed `10.1007/s00209-009-0588-5`, cited as: On Bogovski     and Regularized  P oincar  e Integral Operators for de
- `Idziaszek2021` in `2026_fibonacci_folding_zeckendorf_normalization_gauge_anomaly_spectral_fingerprints`, printed `10.4230/lipics.spire.2021.15`, cited as: Efficient Algorithm for Multiplication of Numbers in  Z eckendorf Repr
- `MeslizaNoorani1999FrobeniusMertens` in `2026_finite_parts_dynamical_zeta_shifts_finite_type_etds`, printed `10.11113/matematika.v15.n.482`, cited as: Teorem  Mertens  Bagi Orbit--Orbit Tertutup Subanjakan Mengikut Kelas
- `GesztesyMakarov2007` in `2026_fredholm_determinants_cyclic_block_spectral_rigidity_jst`, printed `10.1007/s00020-006-1461-8`, cited as: The  J ost Function and the  F redholm Determinant for
- `ColletMartinezSanMartin2013` in `2026_scan_projection_address_semantics_sigma_nonexpansion_etds`, printed `10.1007/978-3-642-32742-0`, cited as: Quasi-Stationary Distributions:  M arkov Chains, Diffusions and Dynami
- `FoataZeilberger1999` in `2026_self_dual_synchronisation_kernel_completed_determinant_cyclotomic_twists`, printed `10.1090/s0002-9947-99-02142-1`, cited as: A combinatorial proof of  B ass s evaluations of the

## Reproducing this

```
curl -A "mailto:<address>" https://api.crossref.org/works/<doi>
curl -A "mailto:<address>" -H "Accept: application/vnd.citationstyles.csl+json" https://doi.org/<doi>
```

A DOI is sound only when the second command returns metadata whose title and lead author
match the bibliography entry. Resolution alone is not sufficient, as Class A shows.

## Entries carrying no DOI (386 distinct works)

Checked separately, by bibliographic search on title and author. 200 have an indexed record and
could carry a DOI; 84 return no Crossref match at all. **None of the 84 shows any sign of
fabrication.** They are Zeckendorf 1972 in the Bulletin de la Societe Royale des Sciences de Liege,
Lekkerkerker 1952 in Simon Stevin, Parry-Pollicott's Asterisque volume, Denjoy 1932, Renyi's 1961
Berkeley Symposium paper, Milne's Etale Cohomology, Horn-Johnson, SGA 4 1/2, technical reports and
workshop proceedings - works that are absent from Crossref because of what they are, not because
they do not exist. Absence from an index is only evidence about the index.

## arXiv identifiers

Fifteen entries carry an arXiv identifier. One is wrong:

| paper | key | identifier | cited as | what it actually is |
|---|---|---|---|---|
| `2026_gluing_failure_visible_quotients_pure_ext_blind_spots_apal` | `Caru2018` | `arXiv:1805.06735` | Towards a Complete Cohomology Invariant for Non-Locality and Contextuality | Properties of ferromagnetic Josephson junctions for memory applications - Caruso, Massarotti et al. |

The remaining fourteen could not be checked: `export.arxiv.org` began returning HTTP 429 to this
address partway through and did not recover. **They are unverified, not verified** - the check must
be repeated before submission. Absence of a result here means the lookup failed, nothing more.
