# P4 Editorial Review R2 -- 2026-04-04

**Manuscript:** "Two detector-defined shells from stationary Unruh--DeWitt click records in static KMS spacetimes"

**Target journal:** Journal of Physics Communications

**Reviewer role:** Gate 3 verification review (round 2)

**Prior review:** P4_EDITORIAL_REVIEW_2026-04-04.md (MINOR_REVISION, 7 items)

---

## 1. Decision

**ACCEPT**

All R1 mathematical and editorial blockers have been resolved. One new minor discrepancy was introduced (author list mismatch between main.tex and cover_letter.tex). This is a pre-submission housekeeping item, not a content blocker. The manuscript is ready for submission after the author list is reconciled and figures are generated.

---

## 2. Fix Verification (item by item)

### R1 Issue 2.2 -- O(rho^2) error in supplementary line 419

**Status: FIXED.**

supplementary.tex line 419 now reads:

```
2\pi\Omega\rho\,\bigl(1+O(\rho)\bigr),
```

This matches the correct remainder. The downstream proper-distance ratio (line 426) still reads $O(\rho_\varphi + \rho_{\mathrm{mem}})$, which is consistent.

### R1 Issue 2.3 -- Remark 5.6 overstatement

**Status: FIXED.**

main.tex line 560 now reads "fails in particular when" instead of "fails precisely when." The supplementary proof for Theorem 5.5 (line 451) uses identical language: "degenerates in particular when." The two files are internally consistent.

### R1 Issue 3.1 -- Gamma_+ vs Gamma notation inconsistency

**Status: FIXED.**

main.tex line 185 now contains the explicit equivalence statement:

> "Throughout this section and the remainder of the paper, we write $\Gamma\equiv\Gamma_+$ for the excitation rate when no confusion with other rates arises."

This appears exactly where Section 3.2 begins, which is where the notation switch occurs. All subsequent uses of plain $\Gamma$ are now covered. The TikZ diagram (line 124) and Table 1 (line 148) use $\Gamma_+=\Gamma_c$, which correctly means "the excitation rate equals the critical rate" and is not confused by the equivalence statement.

### R1 Issue 3.3 -- Missing proof for Theorem 5.5

**Status: FIXED.**

supplementary.tex line 451 contains a self-contained paragraph applying the implicit function theorem to the system $F_1(\theta)=F_2(\theta)=0$. It identifies the Jacobian nondegeneracy condition, states local uniqueness, notes the codimension-one degeneracy at $C_1=C_2$, and confirms self-calibration (no dependence on $\lambda_c^2\mathcal{S}(\Omega)$). The argument is correct and matches the main text theorem statement.

### R1 Issue 3.5 -- Missing author names / double-blind note

**Status: PARTIALLY FIXED.**

- Author name "Haobo Ma" with affiliation "CHRONOAI PTE. LTD., Singapore" now appears on main.tex lines 55-57. Good.
- The double-blind note is gone. The acknowledgements section (line 585) reads "The author thanks the anonymous referees for their comments." Good.
- However, the cover letter (cover_letter.tex) lists two authors: "Haobo Ma and Wenlin Zhang," while main.tex lists only one. See new issue below.

### R1 Issue 3.2 -- Missing figure PDFs

**Status: ACKNOWLEDGED (build step, not content).**

The generated/ directory still contains only tab_worked_example.tex. The three figure PDFs (fig_hazard_cov.pdf, fig_spectrum_fano.pdf, fig_shell_radii.pdf) remain absent. The generation script (scripts/generate_figures.py) exists. This is a build step to be executed before submission, not a content blocker.

### R1 Issue 3.6 -- Cross-reference compilation warnings

**Status: ACKNOWLEDGED (build step).**

Same status as R1. Running pdflatex twice after figure generation will resolve.

---

## 3. New Issues Introduced by Fixes

### 3.1 Author list mismatch between main.tex and cover_letter.tex (MINOR)

**Location:** main.tex line 55 vs cover_letter.tex lines 16, 50

**Problem:** main.tex lists a single author (Haobo Ma, CHRONOAI). The cover letter lists two authors (Haobo Ma and Wenlin Zhang) and states "All authors have approved the submission." The acknowledgements in main.tex use singular "The author." A journal editor receiving both documents would flag this inconsistency immediately.

**Fix:** Either add the second author to main.tex, or remove the second author from the cover letter. This must be consistent across all submission files.

### 3.2 No new mathematical issues

No new mathematical errors were introduced by any of the fixes. The supplementary proof for Theorem 5.5 is correct. The O(rho) correction does not propagate to any other result. The weakened Remark 5.6 is logically sound.

### 3.3 No new structural issues

The equivalence statement at the start of Section 3.2 does not create any downstream inconsistency. All later uses of $\Gamma$ are covered by the stated convention, and all uses in Section 3.1, the abstract, Table 1, and the TikZ diagram correctly use $\Gamma_+$.

---

## 4. Residual Items from R1 (not claimed as fixed)

### R1 Issue 3.4 -- Abstract length (~220 words)

**Status: UNCHANGED.** The abstract remains a single dense paragraph. This was flagged as optional in R1 and does not block submission.

### R1 Issue 3.7 -- Bibliography strengthening

**Status: UNCHANGED.** The bibliography remains at 29 entries. The optional suggestions (modern dead-time review, explicit novelty statement) were not implemented. These do not block submission.

### R1 Issue 4.7 -- TikZ node $\Gamma_+=\Gamma_c$

**Status: RESOLVED BY OTHER FIX.** With the $\Gamma\equiv\Gamma_+$ equivalence statement now in main.tex line 185, the TikZ node notation $\Gamma_+=\Gamma_c$ is unambiguous. No separate fix needed.

---

## 5. Summary Assessment

| R1 Item | Description | Status |
|---------|-------------|--------|
| 2.2 | O(rho^2) -> O(rho) in supplementary | FIXED |
| 2.3 | Remark 5.6 overstatement | FIXED |
| 3.1 | Gamma_+/Gamma notation | FIXED |
| 3.2 | Figure PDFs | Build step (acknowledged) |
| 3.3 | Theorem 5.5 proof | FIXED |
| 3.4 | Abstract length | Optional (unchanged) |
| 3.5 | Author names / double-blind | FIXED (with new minor discrepancy) |
| 3.6 | LaTeX compilation | Build step (acknowledged) |
| 3.7 | Bibliography | Optional (unchanged) |
| 4.7 | TikZ node notation | Resolved by 3.1 fix |

**New issues:** 1 (author list mismatch, minor, pre-submission housekeeping)

---

## 6. Verdict

**ACCEPT.**

The manuscript is content-complete and mathematically sound. All R1 blockers have been addressed correctly. The single new issue (author list discrepancy between main.tex and cover_letter.tex) is a mechanical pre-submission fix, not a content or structural problem.

**Pre-submission checklist (non-blocking):**

- [ ] Reconcile author list: main.tex vs cover_letter.tex
- [ ] Run `python scripts/generate_figures.py` to produce figure PDFs
- [ ] Run pdflatex twice to resolve cross-references
- [ ] Verify final PDF compiles cleanly with no warnings
