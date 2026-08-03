# Sharp Spectral-Cohomology Classification Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: execute inline with test-driven development. No subagent dispatch and no git commit are permitted for this task.

**Goal:** Replace the inverse-rigidity open interface by the strongest rigorous classification supported by the mathematics: an exact finite full-spectrum cohomological multiplicity criterion, a closed-form sharp finite-abelian bouquet theorem, and an explicit proof that Perron-peripheral data alone cannot support the requested classification.

**Architecture:** Identify continuous Livsic cohomology of one-step finite-group edge cocycles with vertex-gauge cohomology. Encode each class by the Wedderburn characteristic-polynomial coordinate of its group-algebra adjacency matrix, and define the spectral cohomology multiplicity as the cardinality of that coordinate fiber. Compute this invariant exactly by spanning-tree normalization; specialize it by finite Fourier inversion on an abelian bouquet, where it becomes a multinomial coefficient.

**Tech Stack:** LaTeX/amsart, Python 3.10, SymPy 1.13.1, arXiv Atom API, Crossref/OpenAlex metadata, latexmk/XeLaTeX.

---

### Task 1: Mathematical Classification

**Files:**
- Modify: `sec_chebotarev_inverse_rigidity.tex`

- [ ] Prove that every continuous transfer between one-step cocycles on an essential edge shift descends, by memory reduction, to a vertex transfer.
- [ ] Identify the quotient with `Hom(pi_1(|Gamma|),G)/G` by spanning-tree normalization.
- [ ] Define the intrinsic Wedderburn spectral coordinate and its cohomological fiber multiplicity.
- [ ] Prove that multiplicity one is necessary and sufficient for determinant rigidity and that the invariant is finite and exactly computable.
- [ ] Prove the abelian bouquet formula
  `mu(tau)=m!/prod_g n_g(tau)!` by Fourier inversion, including the explicit transposition collision when `tau` is nonconstant.
- [ ] Prove that every primitive nontrivial finite-abelian bouquet extension is non-rigid.
- [ ] Exhibit fixed graph/group primitive examples showing that Perron-peripheral spectrum alone cannot determine rigidity.

### Task 2: Red Tests and Exact Verifier

**Files:**
- Modify: `artifacts/test_verify_twisted_determinant_rigidity.py`
- Modify: `artifacts/verify_twisted_determinant_rigidity.py`
- Regenerate: `artifacts/verify_twisted_determinant_rigidity_output.txt`

- [ ] Add failing tests for Fourier recovery of bouquet label multiplicities, the multinomial determinant-fiber formula, the transposition necessity witness, and equal Perron-peripheral data with different rigidity multiplicities.
- [ ] Run `python -m unittest artifacts.test_verify_twisted_determinant_rigidity -v` and confirm failure because the new APIs are absent.
- [ ] Implement exact count recovery, predicted multiplicity, collision construction, determinant-fiber auditing, and Perron-peripheral comparison.
- [ ] Re-run the focused suite and require zero failures.
- [ ] Extend the 327-cocycle report with full-three-shift abelian cases and a complete necessity audit over every nonconstant bouquet cocycle in the added cases.

### Task 3: Literature and Citation Audit

**Files:**
- Create: `artifacts/literature_check.md`
- Modify: `references.bib`

- [ ] Record the arXiv API queries and returned counts/IDs, including arXiv:1503.02050 and the recent adjacent arXiv works already cited by the manuscript.
- [ ] Record exact DOI metadata for Parry's nonabelian Livsic theorem, Parry--Pollicott compact-group Livsic theory, Atiyah--Tall and Knutson on Adams operations, Seneta and Wielandt on Perron--Frobenius/primitivity, and the no-DOI status of Astérisque 187--188.
- [ ] Correct the erroneous Atiyah--Tall DOI, add Knutson and Wielandt DOI data, and cite Boyle--Schmieding where the manuscript distinguishes periodic-data and conjugacy classifications.
- [ ] State novelty conservatively: no exact fixed-presentation Livsic fiber-multiplicity or abelian-bouquet formula was located; database searches support but cannot prove absolute priority.

### Task 4: Verification and Compile Gate

**Files:**
- Verify: `main.tex` and all included sources

- [ ] Run the complete unittest suite for the verifier.
- [ ] Run the verifier and inspect its deterministic output.
- [ ] Run `latexmk -pdfxe -interaction=nonstopmode -halt-on-error main.tex`.
- [ ] Search the log for undefined references/citations and inspect overfull-box warnings involving the changed section.
- [ ] Inspect the scoped git diff and confirm no commit was created.
