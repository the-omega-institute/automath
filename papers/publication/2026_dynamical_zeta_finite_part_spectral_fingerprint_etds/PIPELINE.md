# Pipeline: Dynamical Zeta Finite Part / Spectral Fingerprint (ETDS)
Target: Ergodic Theory and Dynamical Systems (ETDS)
Status: P5 complete, P6--P7 pending

## Stage Progress

| Stage | Status | Date | Notes |
|---|---|---|---|
| P0 Scope and journal fit | completed | pre-2026-03-30 | ETDS primary, JEMS stretch, Nonlinearity fallback |
| P1 Traceability | completed | 2026-03-30 | 48 labelled claims, 39 theorem-level, all proved. Lean coverage: 0.4% |
| P2 Research Extension | completed | 2026-03-30 | Three packages: finite-part, cyclic reconstruction, non-abelian determinant calculus. Scope cuts: syntax/operator/online_kernel sections excluded |
| P3 Journal-Fit Rewrite | completed | 2026-03-30 | Abstract ~150 words; intro rewritten (Thm A/B/C); conclusion expanded; 15 uncited bib entries removed; style pass done |
| P4 Editorial Review | completed | 2026-03-30 | Decision: PASS TO P5. No blockers. Twisted spectral-gap remark expanded; S3 example verifies eta < lambda |
| P5 Internal Review | completed | 2026-03-30 | PASS. Metadata fixed, cross-refs clean, style clean, bib balanced, all files under 800 lines |
| P6 Lean Audit | not started | -- | 0.4% coverage. Priority: abstract thm:finite-part needs real-analysis infrastructure |
| P7 Submission | not started | -- | MSC 37B10, 37D35, 11M41, 20C15. Submission metadata fixed in P5 |

### Open Issues

- G4: S3 numerical values are decimal approximations of well-defined infinite series; exact algebraic formulas are given. A Python verification script would strengthen reproducibility but is not a blocker for ETDS submission. (P7 nice-to-have)
- ~~G6: Submission metadata placeholder in main.tex~~ Closed in P5

## Theorem Inventory

### Package A: Finite-Part Primitive Calculus (Section 3)

- `thm:finite-part-primitive-closed-form`: Closed-form FP(A) at the Perron pole via primitive-orbit formula
- `cor:finite-part-mertens-asymptotic`: Orbit-Mertens asymptotic

### Package B: Cyclic Reconstruction (Section 3)

- `thm:finite-part-cyclic-lift-spectrum-identifiability`: Full cyclic data determine non-Perron spectrum
- `thm:finite-part-cyclic-lift-single-q-torsion-reconstruction`: One root-of-unity layer (q >= d) suffices

### Package C: Non-Abelian Primitive Determinant Calculus (Sections 4--5)

- `cor:class-function-adams-mobius`: Adams-Mobius primitive inversion
- `cor:primitive-peter-weyl-determinant`: Irreducible-channel determinant formula
- `thm:class-mertens-explicit`: Explicit class Mertens theorem under twisted spectral gap
- `thm:class-mertens-fourier`: Non-abelian Fourier reconstruction of class constants
- `thm:abelian-shadow-defect` + `thm:cyclic-detection-boundary`: Abelian shadow / non-abelian defect decomposition with exact boundary of cyclic detection

### S3 Model

- `prop:s3-example-channels`, `prop:s3-example-primitive-channels`, `cor:s3-example-profile`: Concrete demonstration of genuinely non-abelian phenomena

### Appendices (A--C)

15 additional results: holomorphic variation, truncation bounds, Parseval/aliasing, Dirichlet-Gauss expansion, growing-family rigidity.

**Total:** 39 theorem-level claims, all proved. 14 main theorems, 10 propositions, 12 corollaries, 2 lemmas.

## Source Map

- Parent chapter: `zeta_finite_part/finite_part/` (27 files, 5149 lines)
- `sec_introduction.tex` (276 lines): Theorems A/B/C; ETDS tradition connections
- `sec_preliminaries.tex` (194 lines): Primitive orbits, finite-part constants
- `sec_finite_part.tex` (418 lines): Finite-part formula, cyclic reconstruction
- `sec_chebotarev.tex` (626 lines): Class functions, Adams operations, finite-group extensions
- `sec_shadows.tex` (664 lines): Quotient shadows, cyclic detection, S3 model
- `sec_conclusion.tex` (72 lines): Three open problems
- `sec_appendices.tex` (718 lines): Apps A-C (holomorphic variation, arithmetic, growing families)

**Excluded:** `sec_syntax_zeta.tex` (DFA/Zeckendorf), `sec_operator.tex` (Fredholm-Witt/CLT), `sec_online_kernel.tex` (synchronisation kernel)

## Stage Notes

### P2 Research Extension

Three independent but interlocking packages. The key new mechanism: primitive extraction from finite-group extension data requires Adams operations intertwined with Mobius inversion, not bare Mobius inversion alone. This is structural and appears absent from the Chebotarev literature for SFTs (Parry-Pollicott 1986, Noorani-Parry 1992, Pollicott-Sharp 2007).

**Gaps:**
1. Twisted spectral-gap hypothesis (eta < lambda): assumed, not derived for broad classes. Closed in P4 (remark expanded, S3 verifies explicitly).
2. Adams decomposition: no general formula for coefficients. Acceptable for ETDS.
3. FP(A) as spectral invariant: independence discussion brief. Add 1-2 sentences.
4. S3 numerical values: no error bound or verification script. Open.
5. No Python verification script. Open (reproducibility risk).

### P3 Journal-Fit Rewrite

Abstract ~150 words, opens with SFT/primitive matrix context. Introduction: Theorem A (finite-part), B (cyclic reconstruction), C (Adams-Mobius + class Mertens + shadows). Connections to ETDS tradition explicit (Parry-Pollicott 1986, Boyle-Schmieding 2017, Baladi, Lind-Marcus). 15 uncited bib entries removed, 15 retained. Conclusion expanded with three open problems. All files under 800 lines. No AI-voice issues.

### P4 Editorial Review

Decision: PASS TO P5. No blockers. Manuscript is coherent, 36 pages, no undefined references. Expanded twisted spectral-gap remark in sec_chebotarev for ETDS framing. S3 example now verifies eta < lambda explicitly. Remaining watchlist: placeholder submission metadata, S3 decimal values lack verification script, Appendix B condensation if referee requests.

### P5 Internal Review

Decision: PASS. Six-point quality gate completed.

1. **Submission metadata** (G6): Fixed. Author set to "The Omega Project", address to "The Omega Institute for Mathematical Research". Email line removed per instructions. main.tex now 99 lines.
2. **Cross-reference integrity**: All referenced labels are defined in the included files. No undefined \ref/\Cref/\eqref detected. 45 orphan labels (definitions, equations, remarks serving as implicit anchors -- standard for a paper of this size). Theorem A/B/C in the introduction correctly point to their proof locations in Sections 3--5.
3. **Style quality gate**: No revision-trace language, no AI-voice markers, no informal tone in technical sections. All 39 theorem-level claims have complete proofs (3 introduction restatements correctly defer to body proofs).
4. **P4 watchlist**: G4 (S3 numerical values) -- the decimal approximations are of well-defined infinite series with exact algebraic formulas given; adequate for ETDS. G6 closed.
5. **Bibliography**: All 15 bib entries are cited; all citations have bib entries. No orphan or missing references.
6. **File sizes**: All files under 800 lines. Largest: sec_appendices.tex (718), sec_shadows.tex (664), sec_chebotarev.tex (626).

**Remaining items for P6/P7:**
- G4: Optional Python verification script for S3 decimal values (nice-to-have, not blocker)
- P6 Lean audit: 0.4% coverage, priority for abstract finite-part theorem
- P7: Final submission formatting (ETDS LaTeX class if required by journal)

### P6 Lean Sync

0.4% coverage (17/4524 parent labels). Lean covers golden-mean concrete model (`fredholmGoldenMean_det`, trace values, Cayley-Hamilton) and cyclic permutation determinants. No abstract theorems (finite-part formula, cyclic reconstruction, Adams-Mobius) formalized.

### Backflow to Core

| Result | Core target section | Status |
|---|---|---|
| `thm:finite-part-reduced-determinant-group-inverse-gradient` | `zeta_finite_part/` | pending |
| `thm:logM-holomorphic-variation` | `zeta_finite_part/` | pending |
| `thm:logM-truncation-bound` | `zeta_finite_part/` | pending |
| `thm:finite-part-nyquist-parseval-aliasing` | `zeta_finite_part/` | pending |
| `cor:finite-part-nyquist-error-exp` | `zeta_finite_part/` | pending |
| `prop:finite-part-dirichlet-torsion-gauss-expansion` | `zeta_finite_part/` | pending |
| `thm:finite-part-dirichlet-character-inversion-prime` | `zeta_finite_part/` | pending |
| `cor:finite-part-near-rh-q-axis-envelope` | `zeta_finite_part/` | pending |
| `thm:finite-part-boundary-multiplicity-qaxis-energy` | `zeta_finite_part/` | pending |
| `prop:finite-part-torsion-table-galois-covariance` | `zeta_finite_part/` | pending |
| `cor:finite-part-torsion-table-galois-certificate` | `zeta_finite_part/` | pending |
| `thm:finite-part-single-layer-torsion-near-rh` | `zeta_finite_part/` | pending |
| `thm:finite-part-cyclic-lift-polylog-dirichlet-xi` | `zeta_finite_part/` | pending |
| `prop:finite-part-residue-constant-rh-squeeze` | `zeta_finite_part/` | pending |
| `thm:finite-part-residue-drift-trichotomy` | `zeta_finite_part/` | pending |
| `prop:class-indicator-expansion` | `zeta_finite_part/` | pending |
| `prop:kernel-peter-weyl-block-diagonalisation` | `zeta_finite_part/` | pending |
| `thm:class-function-linearisation` | `zeta_finite_part/` | pending |
| `cor:class-function-adams-mobius` | `zeta_finite_part/` | pending |
| `lem:adams-coefficients-bounded` | `zeta_finite_part/` | pending |
| `cor:primitive-peter-weyl-determinant` | `zeta_finite_part/` | pending |
| `cor:primitive-peter-weyl-trace` | `zeta_finite_part/` | pending |
| `thm:class-primitive-decomposition` | `zeta_finite_part/` | pending |
| `cor:class-artin-mobius-trace` | `zeta_finite_part/` | pending |
| `thm:class-mertens-explicit` | `zeta_finite_part/` | pending |
| `thm:class-mertens-fourier` | `zeta_finite_part/` | pending |
| `thm:finite-part-primitive-closed-form` | `zeta_finite_part/` | pending |
| `prop:finite-part-residue-reduced-determinant` | `zeta_finite_part/` | pending |
| `cor:finite-part-mertens-asymptotic` | `zeta_finite_part/` | pending |
| `thm:finite-part-cyclic-lift-reduced-constant-closed` | `zeta_finite_part/` | pending |
| `prop:finite-part-cyclic-lift-dirichlet-multiple-sum` | `zeta_finite_part/` | pending |
| `prop:finite-part-cyclic-lift-mobius-inversion` | `zeta_finite_part/` | pending |
| `thm:finite-part-cyclic-lift-spectrum-identifiability` | `zeta_finite_part/` | pending |
| `thm:finite-part-cyclic-lift-single-q-torsion-reconstruction` | `zeta_finite_part/` | pending |
| `cor:finite-part-cyclic-lift-zeta-torsion-determines-spectrum` | `zeta_finite_part/` | pending |
| `cor:finite-part-single-layer-square-root-test` | `zeta_finite_part/` | pending |
| `cor:finite-part-gap-positive` | `zeta_finite_part/` | pending |
| `thm:intro-finite-part` | `zeta_finite_part/` | pending |
| `thm:intro-cyclic-reconstruction` | `zeta_finite_part/` | pending |
| `thm:intro-finite-group` | `zeta_finite_part/` | pending |
| `prop:sync-kernel-spectrum` | `zeta_finite_part/` | pending |
| `prop:sync-hatdelta-completion` | `zeta_finite_part/` | pending |
| `prop:sync-hatdelta-quotient` | `zeta_finite_part/` | pending |
| `prop:sync-hatdelta-double-cover` | `zeta_finite_part/` | pending |
| `prop:sync-hatdelta-galois-s6-generic` | `zeta_finite_part/` | pending |
| `thm:sync-cyclotomic-degree-law` | `zeta_finite_part/` | pending |
| `cor:rho-m2-closed-form` | `zeta_finite_part/` | pending |
| `prop:sync-endpoint-jet` | `zeta_finite_part/` | pending |
| `thm:rho-gap-m12` | `zeta_finite_part/` | pending |
| `prop:cyclic-lift-primitive-asymptotics` | `zeta_finite_part/` | pending |
| `thm:fredholm-witt-bridge` | `zeta_finite_part/` | pending |
| `thm:cyclic-fredholm-realisation` | `zeta_finite_part/` | pending |
| `thm:clt-spectral` | `zeta_finite_part/` | pending |
| `prop:prelim-trace-primitive` | `zeta_finite_part/` | pending |
| `lem:primitive-orbit-asymptotic` | `zeta_finite_part/` | pending |
| `thm:quotient-functoriality` | `zeta_finite_part/` | pending |
| `cor:abelian-cyclic-shadow` | `zeta_finite_part/` | pending |
| `thm:abelian-shadow-defect` | `zeta_finite_part/` | pending |
| `thm:cyclic-detection-boundary` | `zeta_finite_part/` | pending |
| `thm:quadratic-adams-obstruction` | `zeta_finite_part/` | pending |
| `prop:s3-example-channels` | `zeta_finite_part/` | pending |
| `prop:s3-example-primitive-channels` | `zeta_finite_part/` | pending |
| `cor:s3-example-profile` | `zeta_finite_part/` | pending |
| `thm:dfa-density-dichotomy` | `zeta_finite_part/` | pending |
| `cor:dfa-prime-symmetric-diff` | `zeta_finite_part/` | pending |
| `cor:dfa-prime-recall-precision` | `zeta_finite_part/` | pending |
| `thm:zeckendorf-regular-powerlaw` | `zeta_finite_part/` | pending |
| `cor:zeckendorf-prime-language-not-regular` | `zeta_finite_part/` | pending |
| `thm:zeckendorf-primes-not-sofic` | `zeta_finite_part/` | pending |
| `thm:euler-product-natural-boundary` | `zeta_finite_part/` | pending |
| `prop:finite-zeta-imaginary-periodicity` | `zeta_finite_part/` | pending |
