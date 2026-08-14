# Monatshefte fuer Mathematik submission metadata

Journal: Monatshefte fuer Mathematik

Article type: Original research article

Title: Prime support and multiple-context-free languages in recurrent numeration

Authors:

1. Haobo Ma, AELF PTE LTD., Singapore, auric@aelf.io
2. Wenlin Zhang, National University of Singapore, Singapore,
   e1327962@u.nus.edu (corresponding author)

## Referee-facing upload set

The submission is incomplete unless every item below is delivered to the
editorial office and visible in the referee view.

1. `main.pdf`: primary manuscript.
2. `supplement.pdf`: Supplementary Information, designated Online Resource 1.
3. `reproducibility.zip`: scripts, unit tests, archived outputs, literature
   audit, checksums, and `REPRODUCE.md`, designated Online Resource 2.
4. `source.zip`: all LaTeX sources required to compile both PDFs, plus
   `README.md`, `REPRODUCE.md`, and `references.tex`.
5. `cover_letter.txt`: journal-specific cover letter.
6. `submission_metadata.md`: this upload manifest.

The unpacked `artifacts/` directory is also present in `submission_bundle/`
so that each script and each readable text output can be uploaded separately
if the portal does not expose files inside an archive to referees.

## Supplement policy

Checked 2026-08-15 against the official journal instructions:
https://link.springer.com/journal/605/submission-guidelines

The Monatshefte instructions contain a dedicated "Supplementary Information
(SI)" section. They accept supplementary PDFs, specialized formats including
`.tex`, and collections in `.zip` or `.gz` format. They require a specific
mention in the article using the designation "Online Resource". The article
therefore names the supplement Online Resource 1, and the reproducibility
archive is Online Resource 2. No content needs to be migrated back into the
main manuscript.

## Dependency statement

The primary manuscript is mathematically self-contained. It repeats the
Zeckendorf affine block lemma needed by its theorem chain and has no numbered
`\suppref` pointer. Online Resource 1 contains independent finite-state,
Zeckendorf, and analytic results. It is part of the upload because the article
mentions it and because the reproducibility package verifies computations
associated with the submitted project.

## Verified expected results

- `main.pdf`: clean XeLaTeX build, no undefined references or citations, no
  multiply defined labels.
- `supplement.pdf`: same clean-build standard.
- Verifier: 6 systems, 2282 affine cases, zero failure counters, final line
  `OVERALL: PASS`.
- Unit tests: 19 tests, final result `OK`.
- Integrity: every digest in `artifacts/SHA256SUMS` matches.

Before completing the portal submission, open every attachment through the
referee-facing file list and confirm that Online Resources 1 and 2 are visible.
