# P4 Editorial Review 2026-03-30

**Paper**: H -- Dynamical zeta-Function Finite Part and Spectral Fingerprint  
**Journal lens**: ETDS referee / editorial polish pass  
**Decision**: PASS TO P5

---

## Decision

From an ETDS referee perspective, the manuscript is now coherent enough
to pass a P4 editorial-review gate. The introduction states a clean
theorem package, the finite-part and finite-group sections match the
advertised claims, and the \(S_3\) example reads as a genuine worked
example rather than as an informal add-on.

I do **not** see a remaining P4-level blocker that would justify
holding the paper back from an internal P5 review. The main remaining
risks are either submission-metadata issues or reproducibility issues
that are outside a pure editorial-polish pass.

---

## Evidence Checked

- Existing local build artifacts indicate a clean compiled manuscript:
  `main.pdf` is 36 pages, with no undefined references.
- Remaining TeX warnings are typographic only:
  small underfull/overfull box warnings, concentrated in the
  introduction comparison table and a few displayed numeric lines in the
  \(S_3\) section.
- The page budget is currently acceptable for ETDS; Appendix B is no
  longer a length blocker at the present 36-page size.

---

## Editorial Findings

### Blockers

- None for P4.

### Must-fix

- None remaining after this pass.

### Should-fix / Watchlist

1. `main.tex` still contains placeholder submission metadata:
   `[Author]`, `[Affiliation]`, `[email]`. This is not a P4 blocker, but
   it is a real P7 submission blocker.
2. The numerical constants in the \(S_3\) example are stated as final
   decimal values without a paper-local verification script. The proof
   chain is mathematically self-contained, so this is not a P4 blocker,
   but it remains a P5/P7 reproducibility risk.
3. If ETDS later requests further compression, Appendix B
   (`app:arithmetic`) is still the first place to shorten. At the
   current 36-page length, however, I would not cut it pre-emptively.
4. The introduction comparison table still produces minor box warnings.
   This is typographic, not structural.

---

## Small Fixes Applied In This Pass

1. Expanded the remark on the twisted spectral-gap hypothesis in
   `sec_chebotarev.tex` so the role of `eta < lambda` is framed more
   naturally for ETDS readers and explicitly tied to the existing
   ETDS-facing literature.
2. Added an explicit `eta < lambda` verification to the \(S_3\) worked
   example in `sec_shadows.tex`, so the example now certifies the
   hypothesis of the class-Mertens theorem in-text instead of leaving it
   implicit.

---

## Recommendation For Next Stage

- Advance the paper to P5 internal review.
- Do not spend more time on broad stylistic rewriting unless a later
  review finds a concrete mathematical or structural issue.
- Before P7, fill in submission metadata and decide whether the \(S_3\)
  decimal evaluations need a paper-local reproducibility artifact.
