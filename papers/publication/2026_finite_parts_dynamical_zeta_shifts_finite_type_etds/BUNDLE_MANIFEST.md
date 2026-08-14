# Submission bundle manifest

Target journal: Ergodic Theory and Dynamical Systems

## Upload as primary and administrative files

- `main.pdf` - primary manuscript
- `cover_letter.txt` - ETDS cover letter
- `submission_metadata.md` - metadata and upload-role manifest
- `source.zip` - complete editable source for article and supplement

## Upload as referee-visible supplementary files

- `supplement.pdf` - separately compiled Supplementary Material
- `reproducibility.zip` - all verification code, tests, certificates, readable
  outputs, literature audit, checksums, and reproduction instructions

If the portal permits individual supplementary files, also upload the unpacked
`artifacts/` and `certificates/` files. The two PDFs and the readable output
records must remain visible to referees; archives alone are not assumed to be
expanded by the portal.

## Pointer audit

The article identifies the separately submitted Supplementary Material in the
introduction and data/code statement. It contains no hardcoded numbered
supplement pointer. The named companion PDF exists in this bundle.

## Required referee-readable conclusions

- `artifacts/verify_a5_results_output.txt` ends with `STATUS: PASS`.
- `artifacts/verify_twisted_determinant_rigidity_output.txt` ends with
  `STATUS: PASS`.
- `artifacts/unittest_output.txt` reports 37 tests and `OK`.
- `certificates/s3_log_certificates.run.txt` ends with
  `fixed-label windows verified`.
- `artifacts/literature_check.md` states the narrow Ostrowski/Nishioka priority
  boundary used by the current article.
- `artifacts/SHA256SUMS` verifies the submitted scripts and text records.
