# TRACK_BOARD: Dynamical zeta Finite Part and Spectral Fingerprint (ETDS)

**Paper**: H -- Dynamical zeta-Function Finite Part and Spectral Fingerprint
**Target**: Ergodic Theory and Dynamical Systems (ETDS)
**Last updated**: 2026-03-30

---

## Pipeline stages

| Stage | Name | Status | Date | Notes |
|---|---|---|---|---|
| P0 | Scope & journal fit | DONE | pre-2026-03-30 | README.md written; ETDS primary, JEMS stretch, Nonlinearity fallback |
| P1 | Traceability | DONE | 2026-03-30 | SOURCE_MAP.md and THEOREM_LIST.md created. 48 labelled claims, 39 theorem-level, all proved. Lean coverage: 0.4% (17/4524 labels in parent chapter) |
| P2 | Research extension | DONE | 2026-03-30 | P2_EXTENSION_NOTE_2026-03-30.md created. Three theorem packages identified. Five gaps flagged. Scope cuts confirmed (syntax, operator, online_kernel sections excluded) |
| P3 | Journal-fit rewrite | DONE | 2026-03-30 | P3_REWRITE_NOTE_2026-03-30.md created. Abstract rewritten (~150 words). Introduction rewritten (Theorem A/B/C style, ETDS tradition connections). Conclusion expanded (3 open problems, transfer-operator connections). Bibliography cleaned (15 uncited entries removed, 15 cited entries retained). Style pass done. All files under 800 lines |
| P4 | Writing polish | DONE | 2026-03-30 | ETDS-style P4 pass completed. Added literature-facing clarification to Remark 4.14, made the `S3` example verify `eta < lambda` explicitly, and checked the current build artifact (`main.pdf`) at 36 pages. No P4 blockers; ready for P5 |
| P5 | Internal review | NOT STARTED | -- | Pre-submission quality gate per Omega charter: verify new axioms/assumptions explicit, conclusions traceable, results reproducible, scope/failure modes recorded |
| P6 | Lean audit gate | NOT STARTED | -- | Current Lean coverage 0.4%. Priority targets: `fredholmGoldenMean_det` (done), cyclic permutation det (done), trace recurrence (done). Next: abstract `thm:finite-part-primitive-closed-form` requires real-analysis Lean infrastructure not yet available |
| P7 | Submission | NOT STARTED | -- | Target: ETDS via Editorial Manager. AMS subject classification 37B10, 37D35, 11M41, 20C15 already in main.tex. Submission metadata is still placeholder |

---

## Gap tracker

| ID | Description | Severity | Owner | Status |
|---|---|---|---|---|
| G1 | Twisted spectral-gap hypothesis: no dynamical criteria given for eta < lambda | Low | -- | Closed in P4. Remark 4.14 expanded and the `S3` example now records `eta=1<2=lambda` explicitly |
| G2 | Adams decomposition: no general formula for a_{rho,sigma}^{(m)} | Low | -- | Acceptable for ETDS; coefficients are standard rep-theory |
| G3 | FP(A) as spectral invariant: independence discussion missing | Low | -- | Add 1--2 sentences to discussion |
| G4 | S3 numerical values: no formal error bound or verification script | Medium | -- | Open. Not a P4 blocker, but still a P5/P7 reproducibility risk |
| G5 | Appendix B bulk: Dirichlet/Gauss material may be too number-theoretic for ETDS | Low | -- | Accepted in P4. Current build is 36pp, so no pre-emptive cut is needed |
| G6 | Submission metadata still placeholder in `main.tex` (`[Author]`, `[Affiliation]`, `[email]`) | Low | -- | Open. Not a P4 blocker, but a real P7 submission blocker |

---

## Section-level status

| Section | File | Lines | Status |
|---|---|---|---|
| Title / Abstract | main.tex | 100 | P3: Abstract rewritten (~150 words, ETDS style) |
| 1. Introduction | sec_introduction.tex | 276 | P3: Rewritten. Theorems A/B/C. ETDS tradition. Comparison table. Section roadmap |
| 2. Preliminaries | sec_preliminaries.tex | 194 | Written. Notation fixed |
| 3. Finite parts + cyclic reconstruction | sec_finite_part.tex | 418 | Written, all proofs complete |
| 4. Class functions + finite-group extensions | sec_chebotarev.tex | 619 | Written, all proofs complete. P4: twisted spectral-gap remark expanded for ETDS framing |
| 5. Shadows + S3 model | sec_shadows.tex | 653 | Written, all proofs complete. P4: S3 example now verifies `eta < lambda` explicitly |
| 6. Discussion + open problems | sec_conclusion.tex | 72 | P3: Expanded. Three open problems (spectral gap, non-abelian arithmetic, transfer operators) |
| App A. Holomorphic variation | sec_appendices.tex (A) | ~100 | Written. Opener cleaned (P3) |
| App B. Arithmetic consequences | sec_appendices.tex (B) | ~240 | Written. Opener cleaned (P3). Consider condensing (P4) |
| App C. Growing families | sec_appendices.tex (C) | ~90 | Written. Opener cleaned (P3) |
| References | references.bib | 151 | P3: 15 entries, all cited. Uncited entries removed |

**Excluded files** (in directory, not in main.tex):
- sec_syntax_zeta.tex (314 lines) -- DFA/Zeckendorf material
- sec_operator.tex (197 lines) -- Fredholm--Witt / CLT
- sec_online_kernel.tex (358 lines) -- synchronisation kernel

---

## Dependencies

| Direction | Paper | Relationship |
|---|---|---|
| Upstream | F (POM core) | Strong: primitive matrix formalism, Perron--Frobenius, reduced determinant |
| Downstream | J (zeta-completion) | Strong: H is a necessary precursor for J |

---

## Quality gate checklist (pre-submission)

- [ ] New axioms/assumptions explicit? (twisted spectral gap eta < lambda: YES, explicitly stated)
- [ ] Key conclusions traceable to base layer? (YES: all via Perron--Frobenius + Mobius inversion + character theory)
- [ ] Results reproducible? (PARTIAL: proofs are self-contained; numerical S3 values need script)
- [ ] Scope and failure modes recorded? (YES: conclusion states three open problems; twisted spectral-gap role delineated in Remark 4.14)
