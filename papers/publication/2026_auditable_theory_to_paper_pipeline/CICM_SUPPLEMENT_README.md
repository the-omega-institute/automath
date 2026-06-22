# CICM 2026 Presentation-Only Supplement README

This archive supports the presentation-only paper
`submission_abstract.pdf`.

## Operative Short Paper

- `submission_abstract.pdf`: the CICM presentation-only paper.
- `submission_abstract.tex`: source for the presentation-only paper.
- `references.bib`: bibliography used by both the short paper and the longer note.

The short paper's claim is limited to the publication-coordinate audit interface
and bounded checker contract. It does not claim full semantic correctness of all
imported source objects, a clean-machine rebuild of the complete source tree, or
venue acceptance.

## Operative Support Records

The bounded checker-contract support material is:

- `main.pdf` / `main.tex`: longer technical note and detailed exposition.
- `source_interface_record.json`: source-surface and interface record.
- `stage_a_manifest.json`: declared Stage-A source and evidence surface.
- `stage_a_horn_schema.json`: finite Horn-style coordinate schema.
- `stage_a_horn_audit_certificate.json`: audit certificate for the finite record gate.
- `stage_a_replay_report.json`: replay report for the bounded Stage-A record gate.
- `review_bundle/REVIEW_BUNDLE_MANIFEST.json`: inventory of review-bundle support files.
- `review_bundle/FINAL_DIGESTS_SHA256.md`: digest table for the support bundle.
- `review_bundle/verify_certificate_records.py`: certificate-record verifier entry point.
- `review_bundle/verify_primary_claim_inventory.py`: primary-claim inventory verifier.
- `review_bundle/verify_source_interface_record.py`: source-interface verifier.
- `review_bundle/verify_stage_a_audit.py`: Stage-A audit verifier.
- `review_bundle/verify_theorem_inventory_sync.py`: theorem-inventory synchronization verifier.

The recorded verification logs in `review_bundle/` document previous local
checks. They are support evidence, not a claim that EasyChair reviewers must
rerun the full pipeline.

## Source Locator

- Public source locator: `https://github.com/the-omega-institute/newmath`
- Pinned commit named in the paper: `3fb3d6a0641767388a401883062aa522ea0b397b`
- `newmath` is the public source surface for the BEDC material.
- `automath` is the local automation and publication-pipeline workspace used to
  prepare, review, and package this submission.

## Context-Only Material

Files under `case_snapshots/`, historical review notes, and stale intermediate
logs are context unless explicitly named above as operative support records.
They should not be read as additional publication claims.
