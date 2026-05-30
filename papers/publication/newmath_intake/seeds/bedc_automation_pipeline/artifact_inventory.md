# Artifact Inventory: BEDC Automation Pipeline

## Scripts

| Artifact | Kind | What to cite |
|---|---|---|
| `bedc_ci.py` | audit script | marker, inventory, closurestatus, axiom-purity checks |
| `critical_path.py` | scheduler | global priority function and dispatch windows |
| `phase_d_lint.py` | hard gate | parameter echo, shallow growth, anchor rejection |
| `codex_formalize.py` | orchestrator | worktree-based Lean rounds |
| `codex_revise.py` | orchestrator | worktree-based paper rounds |
| `auto_heal_base.py` | daemon | duplicate labels, propext leaks, gate storms, stuck dirt |
| `pipeline_auto.py` | publication scheduler | paper stage detection and agent prompt generation |
| `pub_check.py` | manuscript gate | citations, refs, style, proof completeness, pipeline metadata |

## Required Tables

- Gate table: gate name, checked file/script, failure caught, recovery action.
- Case-study table: paper/track, issue found, source-map or theorem-list
  correction, resulting stage.
- Comparison table: Lean-auto / ProofWala / Physics-as-Code / BEDC-Automath
  complementarity.

## Intake Tables Now Drafted

- `gate_table.md` drafts the gate-by-gate architecture table.
- `failure_modes.md` drafts the failure taxonomy and case-study requirements.
- `submission_memo.md` drafts the route strategy and promoted-draft outline.
- `case_studies.md`, `case_evidence_note.md`, and `case_table_seed.md` record
  concrete intake-stage case rows for the CICM presentation-only shape.
- `bibliography_scope_seed.md` records the comparison buckets and live
  literature-pass rules that must become `BIB_SCOPE.md` only after promotion.
- `cicm_two_page_packet.md` and `cicm_promotion_brief.md` reduce the artifact
  inventory into a two-page presentation-only route.

## Still Open Before Promotion

- Human approval naming the seed and active slug.
- Immediate live re-check of the official CICM page before any submission.
- Decision to use the pinned source commit or a documented source update.
- Active-paper files such as `BIB_SCOPE.md`, `SOURCE_MAP.md`,
  `ARTIFACT_INVENTORY.md`, `PIPELINE.md`, and `main.tex`; these are forbidden
  in the seed directory and must be created only after promotion.
- Any command reruns or source updates that the promoted route chooses to make
  load-bearing.
