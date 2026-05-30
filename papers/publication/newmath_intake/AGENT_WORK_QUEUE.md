# Newmath Intake Agent Work Queue

This queue records safe work for agents before any seed is promoted into an
active `2026_*` paper.  It is not a daemon queue and must not be parsed as an
active paper list.

## Global Rules

- Work inside `papers/publication/newmath_intake/` unless a human explicitly
  approves promotion or source-side work.
- Do not create `papers/publication/2026_*` directories from this queue.
- Do not add `main.tex` or `PIPELINE.md` to any seed.
- Do not run publication daemon stages against seed directories.
- Run `python papers\publication\newmath_intake\check_intake.py` after edits.
- Use `P0_GATE_AUDIT.md` to distinguish safe intake work from promotion,
  source-side theorem work, and artifact reruns.
- Use `PROMOTION_HANDOFF.md` to see what becomes active-paper work only after
  an explicit human promotion command.
- If `D:/omega/newmath` source changes, use
  `SOURCE_UPDATE_NOTE_TEMPLATE.md` before editing a seed source map.

## P0 Queue

| Seed | Safe automath-only work | Requires human approval | Current stop condition |
|---|---|---|---|
| `bedc_automation_pipeline` | Refine `bibliography_scope_seed.md`; refine non-claims; keep `case_table_seed.md`, the active creation dry run, and `source_decision_note.md` current | Promotion as `2026_auditable_theory_to_paper_pipeline`; final live CICM check | Stop before active file creation |
| `bedc_finite_kernel_calculus` | Refine exact theorem-spine summaries; maintain `current_declaration_map.md`; keep `groundcompiler_placement_decision.md` aligned with the theorem spine; draft source-update note shell without changing source commit | Source-side work in `D:/omega/newmath`; later journal/workshop promotion | Stop before editing Lean/source files or claiming a packaging theorem exists |
| `bedc_rule110_finite_witness` | Refine rerun result tables; maintain `current_static_status_map.md`; record toolchain prerequisites | Installing/using build toolchain; running Rule110 dynamic suite; later promotion | Stop before treating static evidence as artifact validation |

## Dispatch Order

1. `bedc_automation_pipeline`: highest near-term value because it already has a
   CICM presentation-only packet and only needs a human promotion decision.
2. `bedc_finite_kernel_calculus`: next once source-side theorem work is
   approved or a matching theorem is found in a newer source snapshot.
3. `bedc_rule110_finite_witness`: next once a Unix-like `make` plus C compiler
   environment is available.

## Evidence Expectations

Agents should produce compact, checkable artifacts:

- tables tied to exact source paths;
- notes that distinguish verified facts from proposed claims;
- source update notes with old and new commits;
- guard output from `check_intake.py`;
- no generated manuscript files before promotion.

## Current Human Decisions Needed

1. Approve or defer promotion of `bedc_automation_pipeline` for CICM
   presentation-only.
2. Approve or defer source-side finite-kernel packaging theorem work in
   `D:/omega/newmath`.
3. Approve or defer Rule110 dynamic artifact rerun in a toolchain-equipped
   environment.
