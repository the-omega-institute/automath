# Monatshefte fuer Mathematik submission metadata

Journal: Monatshefte fuer Mathematik

Article type: Original research article

Title: Prime support and multiple-context-free languages in recurrent numeration

Authors:

1. Haobo Ma, AELF PTE LTD., Singapore, auric@aelf.io
2. Wenlin Zhang, National University of Singapore, Singapore,
   e1327962@u.nus.edu

## Mandatory referee package

The package is incomplete unless every item below is delivered to the
editorial office and made accessible to referees.

1. `main.pdf`: primary manuscript.
2. `supplement.pdf`: separately compiled finite-state companion, with its own
   abstract, dependency statement, and Shen--Dubbe priority comparison.
3. `source.zip`: `main.tex`, `supplement.tex`, `preamble.tex`, every
   `sec_*.tex` file, `references.tex`, `README.md`, and `REPRODUCE.md`.
4. `reproducibility.zip`: `artifacts/verify_pisot_pumping.py`,
   `artifacts/test_verify_pisot_pumping.py`,
   `artifacts/pisot_pumping_output.txt`, `artifacts/unittest_output.txt`,
   `artifacts/literature_check.md`, `artifacts/SHA256SUMS`, and
   `REPRODUCE.md`.
5. `submission_metadata.md`: this manifest, uploaded with the source or as
   an administrative attachment so file roles are unambiguous.

If the portal accepts individual supplementary files rather than archives,
upload every file listed inside items 3 and 4 individually. A source archive
does not replace the referee-facing `supplement.pdf`, and a script does not
replace its archived output or unit-test transcript.

## Dependency and journal-policy gate

The primary manuscript is mathematically self-contained and contains the
Zeckendorf affine block lemma used by its Theorem 2.2. The separate supplement
contains independent finite-state results and is not used in the recurrent
MCFL theorem chain. It is nevertheless part of this submission because the
article describes it and the package claims reproducibility credit for it.

Before submission, obtain written confirmation that the journal accepts the
supplement and reproducibility archive. If it does not, do not leave any
supplement pointer or computational claim in the article: remove the companion
claims from this submission or resubmit to a route that accepts the complete
package.

## Preflight checks

- Build both PDFs from the submitted sources with the commands in
  `REPRODUCE.md`.
- Confirm that the article contains no `\suppref` dependency.
- Run the verifier and artifact-local unit tests; compare their full outputs
  with both archived transcripts.
- Verify every digest in `artifacts/SHA256SUMS`.
- Confirm the verifier archive says 6 systems, 2282 affine cases, zero
  failures, and `OVERALL: PASS`; confirm the test archive says 19 tests and
  `OK`.
- Open every uploaded attachment through the editorial portal's referee view,
  rather than relying on the author upload view.
- Do not complete the final legal submission step without author review.
