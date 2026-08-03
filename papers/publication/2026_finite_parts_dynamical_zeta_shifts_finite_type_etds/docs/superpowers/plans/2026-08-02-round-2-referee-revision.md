# Round-2 Referee Revision Implementation Plan

> **For agentic workers:** Execute this plan inline in the current manuscript tree. Do not create a git commit.

**Goal:** Close every blocker, medium, and low issue in `artifacts/oracle_review_r2.md`, produce a clean archival manuscript, and verify the exact certificates and XeLaTeX PDF.

**Architecture:** Keep Sections 1--4 as the mathematical correction note. Put the general boundary construction, periodic-data dictionary, switching criterion, and certificate specification in short appendices. Treat the Mohamed--Noorani convention and hypothesis defects as independent corrections.

**Tech Stack:** AMS-LaTeX, BibTeX, Python/SymPy exact rational arithmetic, `latexmk -pdfxe`, Poppler PDF rendering.

---

### Task 1: Framework and conventions

**Files:**
- Modify: `sec_refocused_framework.tex`
- Create: `sec_refocused_boundary_appendix.tex`

- [ ] Insert the Perron-weighted block norm before any use of `rad(A_rho) <= lambda` and state `|Tr(A_rho^n)| <= |V| dim(rho) lambda^n`.
- [ ] Add a two-sided/one-sided convention lemma with `tau(e)=alpha(e)^{-1}`, `g_gamma=h_gamma^{-1}`, inverse classes, conjugate characters/representations, determinant blocks, and radial logarithm branches.
- [ ] Define `eta=0` when `G` is trivial.
- [ ] Attribute primitive/Euler versus ghost-coordinate inversion to necklace/Witt calculus and delimit the fixed-label contribution.
- [ ] Move the unused general peripheral-boundary construction to an appendix.

### Task 2: Corrected theorem and consequences

**Files:**
- Modify: `main.tex`
- Modify: `sec_refocused_introduction.tex`
- Modify: `sec_refocused_product_correction.tex`
- Modify: `sec_refocused_conclusion.tex`

- [ ] State that primitive base mixing alone implies neither uniform Frobenius density nor the strict twisted gap.
- [ ] Restate the formal correction theorem with both required repairs and the radial branch convention.
- [ ] Add the full two-shift/trivial-`C_2`-cocycle counterexample.
- [ ] State and prove the union-of-classes homogeneous-extension constant.
- [ ] Explain exactly which later class-Mertens results use the exponent and which use the erroneous explicit constant.

### Task 3: Self-contained S3 certificate

**Files:**
- Modify: `sec_refocused_s3_witness.tex`
- Verify: `certificates/s3_log_certificates.py`
- Modify: `REPRODUCE.md`

- [ ] Print rational logarithm brackets and tail comparisons proving `-381/1000 < F_epsilon(1/2) < -380/1000` without relying on code.
- [ ] Describe the displayed standard representation as a non-orthonormal real model similar to a unitary realization.
- [ ] Run the deposited exact-arithmetic certificate and record its stable repository URL.

### Task 4: Background appendices

**Files:**
- Modify: `sec_refocused_inverse_background.tex`
- Modify: `main.tex`

- [ ] Compress the determinant/periodic-data equivalence and switching criterion to a short background appendix.
- [ ] Formally double every marked directed edge, define reverse gains, and define fundamental-cycle products in the doubled graph.
- [ ] Retain only qualifications needed to prevent inverse-rigidity overclaim.

### Task 5: Exactness, references, and archival prose

**Files:**
- Modify: `sec_refocused_exactness.tex`
- Modify: `references.bib`
- Modify: `main.tex`
- Modify: `REPRODUCE.md`

- [ ] Specify the fixed real embedding, compatible splitting-field embedding, conjugate-root pairing, positive isolating data for every `lambda^2-alpha alphabar`, and Perron-root multiplicity record.
- [ ] Add and discuss Bowen--Lanford, Parry--Pollicott, Parry, Metropolis--Rota, Noorani 1995, Nordin--Noorani/post-1999 work, and Stark--Terras.
- [ ] Supply full institutional affiliation, correspondence address, and a content-addressed public repository URL.
- [ ] Remove all revision-history and referee-process language from compiled manuscript prose.

### Task 6: Verification

**Files:**
- Verify: all compiled `.tex` files, `references.bib`, `REPRODUCE.md`, `main.pdf`

- [ ] Run exact certificate scripts and require their success markers.
- [ ] Search the active source and extracted PDF text for prohibited revision-process phrases.
- [ ] Run `latexmk -pdfxe -interaction=nonstopmode -halt-on-error main.tex`.
- [ ] Check the log for undefined references/citations and overfull boxes.
- [ ] Render the final PDF to PNG and inspect page layout, section transitions, references, and equations.
