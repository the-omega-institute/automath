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

## Missing Before Promotion

- Concrete case-study rows with exact track names and source paths.
- Re-run status or explicit deferral notes for the verification commands.
- Venue-specific formatting constraints after official CFP re-check.
- A comparison matrix against current AI-for-math/formalization systems.
