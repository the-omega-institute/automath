# CICM 2026 Presentation-Only Submission Memo

- Paper: `2026_auditable_theory_to_paper_pipeline`
- Route: CICM 2026 presentation-only paper
- Prepared: 2026-06-20 Asia/Singapore
- Official CFP: `https://cicm-conference.org/2026/cicm.php?event=&menu=cfp`
- EasyChair: `https://easychair.org/conferences/?conf=cicm2026`

## Official Requirement Check

The CICM 2026 CFP currently states:

- presentation-only papers describe ongoing research;
- length is 2 pages plus bibliography;
- review is light-weight;
- presentation-only papers do not appear in the Springer proceedings;
- accepted presentation-only papers are showcased in a presentation session and poster session;
- submission deadline is 2026-06-25, extended from 2026-06-15;
- submissions use EasyChair and Springer LNCS style files;
- if software or data is relevant, an access link should be provided.

## Files To Upload

Primary presentation-only paper:

- `submission_abstract.pdf`
  - current build: 3 PDF pages
  - body fits within the 2-page presentation-only budget; bibliography follows on page 3
  - built with LNCS class and `splncs04` bibliography style
  - latest LaTeX log has no undefined citations and no overfull/underfull warnings
  - rebuilt on 2026-06-20 after replacing the earlier overlong draft

Short-paper review queue:

- `CICM_SHORT_REVIEW_QUEUE.json`
  - 2026-06-20: the earlier `submission_abstract.pdf` rebuilt to 11 pages and was blocked locally as `needs_shortening`
  - 2026-06-20: `submission_abstract.tex` was compressed into a true CICM presentation-only note
  - current short-review task:
    `review_2026_auditable_theory_to_paper_pipeline_CICM_short_fresh_1781963031295411200`
  - review target is only `submission_abstract.pdf`; `main.pdf` is supplement/background only
  - NyxID/Oracle returned `Minor revision` with no two-page claim-boundary blocker
  - 2026-06-21 closure: clarified roles versus coordinates in the short PDF, added `CICM_SUPPLEMENT_README.md`, and rebuilt the supplement zip
  - status after closure: ready for human EasyChair metadata/supplement check

Supplementary material:

- `cicm_supplement_2026_auditable_theory_to_paper_pipeline.zip`
  - curated supplement archive, rebuilt 2026-06-21
  - excludes `__pycache__`, `.pyc`, `.codex`, `_tmp`, and cache entries
  - includes:
    - `CICM_SUPPLEMENT_README.md`
    - `submission_abstract.tex`
    - `submission_abstract.pdf`
    - `main.tex`
    - `main.pdf`
    - `references.bib`
    - `SOURCE_MAP.md`
    - `THEOREM_LIST.md`
    - `ARTIFACT_INVENTORY.md`
    - `BIB_SCOPE.md`
    - `VENUE_CHECK.md`
    - `P4_REVIEW.md`
    - `source_interface_record.json`
    - `stage_a_manifest.json`
    - `stage_a_horn_schema.json`
    - `stage_a_horn_audit_certificate.json`
    - `stage_a_replay_report.json`
    - selected `review_bundle/` records, manifests, source snapshots, case snapshots, and verification scripts/logs

Public source link:

- `https://github.com/the-omega-institute/newmath`
- Pinned source commit used in the submission materials:
  `3fb3d6a0641767388a401883062aa522ea0b397b`

## EasyChair Form Fields

Title:

```text
Auditable Theory-to-Paper Pipelines for AI-Assisted Formal Mathematics
```

Authors:

```text
Haobo Ma
AELF PTE LTD.
auric@aelf.io

Wenlin Zhang
National University of Singapore
e1327962@u.nus.edu
```

Abstract:

```text
AI-assisted formalization is often presented as a local loop: a model proposes Lean code and a proof assistant accepts or rejects it. That loop is necessary, but it is not enough for sustained mathematical research. A project also needs to know whether a generated object is source theory, a checked interface, a finite artifact witness, an advisory search result, a publication claim, or a human decision. We describe a theory-to-paper pipeline, developed across the newmath and automath workspaces, that makes these roles explicit. The pipeline routes generated material through six records: source object, formal interface, finite evidence row, advisory agent action, deterministic gate, and human promotion boundary. This gives agents room to search, repair, and criticize, while certification remains in typed records, mechanical gates, and human review. The contribution is a portable audit interface for AI-assisted formal mathematics: a generated object is promoted only to the strongest claim whose required record coordinates are present.
```

Suggested keywords:

```text
formal mathematics; AI-assisted formalization; proof assistants; mathematical knowledge management; research automation; artifact audit; Lean; publication pipeline
```

Suggested category/type:

```text
presentation-only paper / work-in-progress
```

Software/data/artifact link:

```text
https://github.com/the-omega-institute/newmath
```

Supplement note, if the form has a text box:

```text
The public source surface is the newmath repository at commit 3fb3d6a0641767388a401883062aa522ea0b397b. The supplementary archive contains the longer technical note, source-interface records, theorem-inventory records, digest manifests, and case-evidence rows. These materials support bounded finite-record claims and do not claim a fresh clean-machine rebuild of all source files or a dynamic rerun of every artifact.
```

Competing interests:

```text
The authors declare no competing interests.
```

AI disclosure, if requested:

```text
AI-assisted tools were used for editorial review, language polishing, formatting, and consistency checks. Mathematical claims and final content were reviewed and are the responsibility of the authors.
```

## Evidence Boundary

The paper and supplement should not be described as claiming:

- a new theorem prover;
- automatic mathematical novelty judgment;
- automatic venue acceptance;
- complete verification of all BEDC declarations;
- a fresh clean-machine rebuild of the full `newmath` source tree;
- a fresh dynamic rerun of every artifact;
- whole-program implementation soundness of the publication pipeline.

The safe claim is:

```text
The submission describes a portable six-role audit interface for AI-assisted formal mathematics, supported by bounded finite-record evidence and a public source locator.
```

## Human Confirmation Required Before Final Submit

- Confirm the author order:
  `Haobo Ma` first, `Wenlin Zhang` second.
- Confirm the affiliation and email block exactly as above.
- Confirm that `submission_abstract.pdf` is visually acceptable.
- Confirm that the supplementary archive may be uploaded as-is.
- Confirm that the source link should be the public `newmath` repository rather than a DOI archive.
- Confirm no final source-command rerun is claimed.
- Confirm final EasyChair category is `presentation-only` or equivalent.

Do not click the final EasyChair submit button until these items are confirmed.
