# Monatshefte fuer Mathematik submission metadata

Journal: Monatshefte fuer Mathematik

Article type: Original research article

Title: Context-free rigidity in recurrent numeration: prime support and a Cobham theorem

Authors:

1. Haobo Ma, AELF PTE LTD., Singapore, auric@aelf.io
2. Wenlin Zhang, National University of Singapore, Singapore,
   e1327962@u.nus.edu (corresponding author)

## Referee-facing upload set

1. `main.pdf`: primary manuscript.
2. `reproducibility.zip`: scripts, unit tests, archived outputs, literature
   record, checksums, and `REPRODUCE.md`, designated Online Resource 1.
3. `source.zip`: the LaTeX sources required to compile the primary manuscript,
   together with `README.md`, `REPRODUCE.md`, and `main_references.tex`.
4. `cover_letter.txt`: journal-specific cover letter.
5. `submission_metadata.md`: this upload manifest.

The unpacked `artifacts/` directory is also present in `submission_bundle/`
so that each script and readable text output can be uploaded separately if
the portal does not expose files inside an archive to referees.

## Dependency statement

The primary manuscript is mathematically self-contained. Online Resource 1
contains deterministic consistency checks and archived outputs; no theorem
uses a finite computation as a substitute for proof.

## Expected checks

- `main.pdf`: clean XeLaTeX build, no undefined references or citations, and
  no multiply defined labels.
- Verifier: 6 systems, 2282 affine cases, zero failure counters, final line
  `OVERALL: PASS`.
- Unit tests: 21 tests, final result `OK`.
- Integrity: every digest in `artifacts/SHA256SUMS` matches.
