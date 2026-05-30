# Promotion Checklist: BEDC Automation Pipeline

This checklist governs the move from intake seed to active paper.  Passing this
checklist does not itself promote the seed; promotion requires a human command
and creation of a `papers/publication/2026_*` directory.

## Intake Completeness

- [x] `seed_packet.md` states the paper unit and candidate claim.
- [x] `source_map.md` pins `D:/omega/newmath` to source commit
  `3fb3d6a0641767388a401883062aa522ea0b397b`.
- [x] `artifact_inventory.md` lists the core scripts and required tables.
- [x] `venue_ladder.md` lists primary and journal routes.
- [x] `risk_register.md` lists overclaim risks and kill criteria.
- [x] `scope_contract.md` separates this paper from Rule 110 and finite-kernel
  paper units.
- [x] `gate_table.md` records gate/source/failure/recovery rows.
- [x] `failure_modes.md` records concrete failure-mode classes.
- [x] `submission_memo.md` records first-route strategy and blockers.
- [x] `case_studies.md` records six concrete candidate cases from current
  automath/newmath evidence.
- [x] `cicm_promotion_brief.md` reduces the case/gate material to a CICM
  two-page presentation-only shape.
- [x] `case_evidence_note.md` records exact evidence for the four CICM brief
  case studies.

## Promotion Requirements Still Open

- [x] Select three to six concrete case studies with exact source paths,
  observed failures, and recovery commits or notes.
- [x] Verify that cited newmath and automath source paths exist at the pinned
  source/workspace state; see `source_verification_note.md`.
- [x] Re-run or explicitly defer the source verification commands from
  `gate_table.md`.  Decision: defer for CICM presentation-only and use a
  narrowed claim; see `promotion_decision_memo.md`.
- [x] Re-check the official page for the first venue.  CICM 2026
  presentation-only was verified open on 2026-05-31 with a 2026-06-15
  deadline.
- [ ] Re-check the official page again immediately before actual submission.
- [ ] Decide whether the promoted manuscript uses the pinned newmath commit or
  a documented source update.
- [x] Copy exact machine-board/log evidence for the four CICM brief case
  studies into a manuscript working note.
- [x] Record the post-promotion active creation dry run in
  `active_creation_dry_run.md`.
- [ ] Reduce `case_evidence_note.md` into a compact table after promotion.
- [ ] Choose active paper slug, suggested:
  `2026_auditable_theory_to_paper_pipeline`.
- [ ] Human approves promotion.

## Hard Prohibitions Before Promotion

- Do not create a `papers/publication/2026_*` directory for this seed.
- Do not add `main.tex` to this seed directory.
- Do not add `PIPELINE.md` to this seed directory.
- Do not run P0-P7 or Stage A/C publication automation against this seed
  directory.
