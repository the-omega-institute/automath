# 2026 Golden Ratio Driven Scan-Projection Generation (Recursive Emergence)

This directory contains the paper `main.tex` and its reproducible experiment pipeline.

Part of the [Omega Project](../../README.md) — a zero-axiom mathematical formalization effort.

## Paper Overview

This paper develops a theory of scan-projection generation driven by the golden ratio, exploring recursive emergence phenomena in algebraic and combinatorial structures built from Zeckendorf representations and the golden-mean shift. The paper contains ~10,588 theorem-level statements across 21 body chapters and 13 appendix chapters.

## Directory Structure

- **Root entry points**
  - `main.tex` — Full build entry point
  - `sections/frontmatter/fm__titlepage_meta.tex` — Title and author metadata; update this file when the author list changes
  - `references.bib` — Bibliography database
  - `AUTHORSHIP.md` — Authorship rules, submission checklist, and contribution record template
- **sections/**
  - `sections/frontmatter/main.tex` — Front matter (independently compilable)
  - `sections/body/main.tex` — Body (independently compilable)
  - `sections/appendix/main.tex` — Appendix (independently compilable, handles `\appendix`)
  - `sections/backmatter/main.tex` — Back matter (independently compilable, includes bibliography)
  - `sections/generated/` — Script-generated LaTeX fragments (write-only, never hand-edit)
- **automation/** — Research automation, journal reconnaissance, and reproducibility gates
- **scripts/** — Reproducible experiment scripts (orchestrated by `scripts/run_all.py`)
- **artifacts/** — Exported audit artifacts (CSV/PNG/JSON etc.)

## Build

Run experiments first, then compile. New experiment scripts must be added to `scripts/run_all.py`.

Build for export:

```bash
latexmk -pdfxe -interaction=nonstopmode -halt-on-error -file-line-error main.tex
```

Section-level build (for local testing): enter any directory with a `main.tex` and compile directly:

```bash
cd sections/body
latexmk -pdfxe -interaction=nonstopmode -halt-on-error -file-line-error main.tex
```

Note: section-level builds are for syntax/typesetting/local derivation chain verification. Cross-directory references (`\ref`/`\cite`) may require compiling the root `main.tex` first to generate complete aux data.

## Reproduce Experiments

Install dependencies:

```bash
python3 -m pip install -r requirements.txt
```

Run the full pipeline:

```bash
python3 scripts/run_all.py
```

This generates:

- `sections/generated/*.tex` — LaTeX fragments for figures/tables (directly `\input{}`-able)
- `artifacts/export/*` — CSV/PNG exports for audit and review
- `artifacts/export/run_all_manifest.json` — pipeline manifest with step status, signatures, and expected outputs
- `artifacts/export/run_all_contract_report.json` — machine-readable contract result
- `artifacts/export/run_all_contract_report.md` — human-readable contract summary

Validate the contract artifacts after a run:

```bash
python3 automation/pipeline_contract.py validate
```

The higher-level automation commands live under `automation/`, while `python3 scripts/run_all.py` remains the canonical experiment entry point used by the paper.

## Research Cycle

To turn one paper slice into a reusable workflow packet for writing, formalization, literature review, journal targeting, and verification:

```bash
python3 automation/research_cycle.py create --section body/folding --slug folding_cycle
python3 automation/research_cycle.py create --sections body/folding body/emergent_arithmetic --slug folding_arith_pair
python3 automation/research_cycle.py validate artifacts/export/research_cycles/folding_cycle
python3 automation/research_cycle.py batch --sections body/folding body/spg --slug pilot_batch
python3 automation/research_cycle.py seed-paper artifacts/export/research_cycles/folding_cycle --slug folding_note_seed
python3 automation/journal_recon.py run --journal "Journal of Pure and Applied Algebra" --journal-short JPA --max-papers 6 --years-back 3 --slug jpa
python3 automation/research_cycle.py journal-pack artifacts/export/paper_seeds/folding_note_seed --journal "Journal of Pure and Applied Algebra" --journal-short JPA --batch-dashboard artifacts/export/research_cycles/_batch/body_batch_all --slug jpa_folding_note
python3 automation/research_cycle.py validate-journal-pack artifacts/export/journal_packs/jpa_folding_note
python3 automation/publication_sync.py sync --publication-root /path/to/the-omega/docs/papers/auric-golden-phi/publication --slug auric_publication_sync
python3 automation/publication_sync.py validate artifacts/export/publication_sync/auric_publication_sync
```

This generates a cycle directory under `artifacts/export/research_cycles/<slug>/` containing:

- `slice_manifest.json` — transitive TeX closure, headings, claims, citation keys
- `paper_slice.md` — human-readable slice summary
- `formalization_backlog.json` — exact missing Lean labels plus local theorem search suggestions
- `literature_survey_seed.md` — cited bibliography plus suggested external survey queries
- `workflow_next_steps.md` — concrete follow-up commands for the next formalization / verification pass
- `cycle_report.json` — compact quantitative summary of the slice

Batch mode writes a dashboard under `artifacts/export/research_cycles/_batch/<slug>/`:

- `dashboard.json` — machine-readable summary across the selected sections
- `dashboard.md` — human-readable section ranking by missing Lean coverage
- `cycles/<section-slug>/...` — one full cycle packet per section

`seed-paper` creates a standalone draft scaffold under `artifacts/export/paper_seeds/<slug>/`:

- `main.tex` — compilable draft entry point
- `sections/source_slice.tex` — slice summary and anchor claims
- `sections/formalization_frontier.tex` — first missing claims plus suggested Lean anchors
- `sections/literature_seed.tex` — resolved bibliography subset plus survey queries
- `sections/verification_plan.tex` — concrete next verification steps
- `references.bib` — copied subset of locally resolved bibliography entries when available
- `seed_manifest.json` — machine-readable seed metadata

`journal-pack` creates a submission-oriented prompt bundle under `artifacts/export/journal_packs/<slug>/`:

- `journal_profile.json` — source statistics, journal target, and pack metadata
- `journal_brief.md` — concise dossier for the target journal
- `deep_revision_prompt.md` — full-manuscript restructuring and rewrite prompt
- `research_extension_prompt.md` — prompt focused on new publishable conclusions only
- `editorial_review_prompt.md` — hard editorial gate prompt with accept / reject framing
- `boundary_profile.json` — inferred include / exclude themes for the target journal
- `boundary_report.md` — automatic keep / merge / split / rewrite report against the full batch dashboard
- `keep_drop_matrix.json` — machine-readable section-level boundary decisions
- `split_strategy.md` — recommended split and merge strategy, including a concrete merged-packet command
- `boundary_gate_prompt.md` — hard scope-fit prompt asking whether the current manuscript boundary should be sent out for review
- `workflow.md` — ordered revision loop for journal-targeted iteration
- `submission_checklist.md` — final submission checklist
- `recent_paper_notes_template.md` — template for notes from recently accepted papers
- `editorial_notes_template.md` — template for venue-specific editorial constraints

If recent-paper notes are missing, `journal-pack` first looks for an existing reconnaissance directory under `artifacts/export/journal_recon/<journal-short>/`. If no local recon notes exist, it will attempt an online reconnaissance pass automatically unless `--skip-auto-recon` is given. Successful auto recon is copied into the journal pack as:

- `recent_paper_notes.md` — auto-filled recent-paper notes consumed by the prompts
- `recon_profile.json` — machine-readable recon metadata
- `recent_papers.json` — sampled recent-paper metadata
- `style_summary.md` — extracted title / abstract style signals

`automation/journal_recon.py` can also be run independently to prebuild a reconnaissance cache under `artifacts/export/journal_recon/<slug>/`:

- `recon_profile.json` — query parameters and sample counts
- `recent_papers.json` — paper metadata plus computed style summary
- `recent_paper_notes.md` — prompt-ready notes for recent papers
- `style_summary.md` — compact style summary for the venue

## Publication Workspace Sync

If publication planning already lives in another repository, `automation/publication_sync.py`
builds a program-level sync report instead of creating new paper skeletons locally:

```bash
python3 automation/publication_sync.py sync \
  --publication-root /path/to/the-omega/docs/papers/auric-golden-phi/publication \
  --slug auric_publication_sync
python3 automation/publication_sync.py audit \
  --publication-root /path/to/the-omega/docs/papers/auric-golden-phi/publication \
  --slug auric_publication_sync
python3 automation/publication_sync.py validate \
  artifacts/export/publication_sync/auric_publication_sync
```

This writes `artifacts/export/publication_sync/<slug>/` with:

- `sync_manifest.json` — workspace path, counts by publication phase, and unmapped sections
- `publication_inventory.json` — one record per publication directory, including target journal and covered source sections
- `section_status.json` — one record per `sections/body/<section>` directory with publication status and recommended program action
- `lean_linkage.json` — publication-to-Lean linkage via `SOURCE_MAP.md`, `THEOREM_LIST.md`, or section-level fallback labels
- `publication_audit.json` — contract audit summary and per-directory issues for missing `README.md`, `main.tex`, `SOURCE_MAP.md`, `THEOREM_LIST.md`, and submission status markers
- `publication_audit_report.md` — human-readable audit report suitable for gating the external publication workspace
- `publication_sync_report.md` — human-readable dashboard showing which sections are already submitted, planned, frozen, or still unmapped

Use this when publication splitting is managed elsewhere and `automath` only needs to stay aligned with that external submission program.
`audit` exits nonzero on hard contract violations; `audit --strict` also fails on mapping gaps and missing submission metadata.

## Writing Conventions

### Authorship Maintenance

### Label addressing

- If the paper's author list changes, update `sections/frontmatter/fm__titlepage_meta.tex`.
- If authorship qualification, ordering rules, or pre-submission checks change, update `AUTHORSHIP.md`.
- `main.tex` only references the shared title/author metadata and should not hard-code individual author information anymore.

- **Primary label:** Each content file provides a `\label{...}` at its first anchor point, serving as the file's unique address identifier (globally unique).
- **Filename mapping:** File basenames are deterministically derived from the primary label:
  - Replace `:` with `__`
  - Keep other characters (including `-`)
  - Extension is always `.tex`
- **Examples:** `sec:folding` → `sec__folding.tex`, `app:unit-circle-phase-gate` → `app__unit-circle-phase-gate.tex`

### Atomization and hierarchy

- **File size limit:** Single `.tex` files must not exceed 800 lines. Files exceeding this limit must be split by subsection/topic, aggregated via a directory-level `main.tex`.
- **Files per level:** Manually maintained directories should have ≤ 30 `.tex` files (excluding `sections/generated/`). Beyond this, split into subdirectories with independently compilable `main.tex` entry points.

### Path conventions

- **Generated directory:** `sections/generated/` is script-generated; never hand-edit. References use `\input{sections/generated/...}`.
- **`\input` base path:** TeX resolves `\input{...}` relative to the compilation entry `main.tex` directory and `subfiles` search paths, not the current included file's directory.
- **subfiles path correction:** If section-level builds encounter "file not found" from bibtex or similar, use `\subfix{...}` or relative paths from the current directory to root.

## Adding Scripts

New experiment scripts must be added to `scripts/run_all.py`'s steps list. `automation/run_all.py` is an alternate automation entry point that forwards to the canonical script pipeline.
