# Twisted-Determinant Inverse Rigidity Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove and machine-check the exact kernel and sharp failure of inverse rigidity for twisted determinants of finite-group SFT extensions.

**Architecture:** Add a self-contained inverse section after the open-disc forward machinery, then promote its theorem in the introduction and abstract.  Use an exact SymPy enumerator as an independently checkable finite certificate.

**Tech Stack:** LaTeX/amsart, Python 3, SymPy, latexmk/XeLaTeX.

---

### Task 1: Red tests for the finite certificate

**Files:**
- Create: `artifacts/test_verify_twisted_determinant_rigidity.py`
- Create: `artifacts/verify_twisted_determinant_rigidity.py`

- [ ] Write tests asserting gauge invariance, the Z/2 two-loop collision,
  non-cohomology by a marked fixed point, and absence of a smaller collision.
- [ ] Run the tests before the implementation exists and confirm the expected
  import or missing-function failure.
- [ ] Implement exact group representations, twisted matrices, determinant
  signatures, gauge enumeration, marked periodic witnesses, and search.
- [ ] Run the focused tests and require zero failures.

### Task 2: Exact inverse theorem

**Files:**
- Create: `sec_chebotarev_inverse_rigidity.tex`
- Modify: `sec_chebotarev.tex`

- [ ] Define Livsic/vertex gauge, determinant equivalence, and unmarked
  Frobenius equivalence with the manuscript's existing conventions.
- [ ] Prove the determinant/periodic-class/primitive-class equivalences by
  logarithmic coefficient comparison, character orthogonality, and the
  existing Adams--Mobius inversion.
- [ ] Prove the marked-orbit and semisimple gauge-certificate injectivity
  clauses, explicitly separating them from bare semisimplicity.
- [ ] Prove and minimize the Z/2 full-two-shift counterexample.

### Task 3: Promote the theorem

**Files:**
- Modify: `main.tex`
- Modify: `sec_introduction_core.tex`
- Modify: `sec_introduction_scalar_and_plan.tex`
- Modify: `sec_conclusion.tex`

- [ ] Make inverse rigidity the title/abstract/introduction headline.
- [ ] Add the inverse theorem as Main Theorem A and retain the existing
  Adams--Mobius/Perron package as forward Main Theorems B--C.
- [ ] State the precise limitation: mixing, primitive skew products, and
  semisimple twisted blocks do not alone imply injectivity.

### Task 4: Generate and verify evidence

**Files:**
- Create: `artifacts/verify_twisted_determinant_rigidity_output.txt`

- [ ] Run the exact verifier and write its deterministic table.
- [ ] Cross-check every numerical count and displayed determinant in the
  manuscript against the output.
- [ ] Run `latexmk -pdfxe -interaction=nonstopmode -halt-on-error main.tex`.
- [ ] Inspect git diff, new labels, undefined references, and report any open
  interface without overclaiming it.

No commit step is included because the user explicitly prohibited commits.
