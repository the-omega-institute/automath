# Submission bundle manifest

Target journal: Monatshefte fuer Mathematik

## Upload as primary and administrative files

- `main.pdf` - primary manuscript
- `cover_letter.txt` - cover letter
- `submission_metadata.md` - metadata and upload-role manifest
- `source.zip` - complete editable source for article and supplement

## Upload as referee-visible Online Resources

- `supplement.pdf` - Online Resource 1, Supplementary Information
- `reproducibility.zip` - Online Resource 2, complete verification package

If the portal permits individual supplementary files, also upload the unpacked
`artifacts/` files. In particular, a script is not a substitute for its
archived output, and the source archive is not a substitute for
`supplement.pdf`.

## Pointer audit

The article points generally to Online Resource 1 in its introduction and
conclusion. It contains no numbered `\suppref` pointer. The Supplementary
Information contains internal plain hyperlinks with the following checked
targets: Section 1; Lemma 1.3; Lemmas 1.16 and 1.17; Theorem 1.18; and
Corollary 1.19. Each number and environment type matches the final supplement.

## Required referee-readable conclusions

- `artifacts/pisot_pumping_output.txt` ends with `OVERALL: PASS`.
- `artifacts/unittest_output.txt` reports 21 tests and `OK`.
- `artifacts/literature_check.md` records the priority boundary.
- `artifacts/SHA256SUMS` verifies the submitted scripts and text records.
