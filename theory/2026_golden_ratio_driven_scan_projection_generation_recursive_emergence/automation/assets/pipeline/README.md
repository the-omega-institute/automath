# Publication Pipeline Assets

This directory keeps the publication automation declarative.

The guiding rule is:

- `paper-dev` contributes primarily through direct manuscript edits and structural refinement.
- `lean4-dev` contributes primarily through small, auditable theorem increments.
- The automation layer should therefore generate work orders, profiles, and prompts, not bury the research process in heavyweight Python logic.

## Layout

- `journal_profiles/` stores venue-facing guidance in editable Markdown.
- `prompt_templates/` stores reusable Codex/editorial prompts.

## Intended Workflow

1. `publication_sync.py` aligns the external publication workspace with `automath`.
2. `publication_journal_fit.py` computes venue fit, bibliography gaps, and manuscript metrics.
3. The same command renders prompt workboards from the templates in this directory.
4. The actual mathematical and editorial improvement still happens in the paper directories through focused `.tex`, `.md`, and bibliography edits.

The automation layer should remain thin: prefer changing these assets over adding more orchestration code unless a repeated manual step cannot be captured declaratively.
