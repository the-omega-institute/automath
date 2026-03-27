# 2026 Golden Ratio Driven Scan-Projection Generation (Recursive Emergence)

This directory contains the paper `main.tex` and its reproducible experiment pipeline.

Part of the [Omega Project](../../README.md) — a zero-axiom mathematical formalization effort.

## Paper Overview

This paper develops a theory of scan-projection generation driven by the golden ratio, exploring recursive emergence phenomena in algebraic and combinatorial structures built from Zeckendorf representations and the golden-mean shift. The paper contains ~10,588 theorem-level statements across 21 body chapters and 13 appendix chapters.

## Directory Structure

- **Root entry points**
  - `main.tex` — Full build entry point
  - `main_fast.tex` — Fast build entry point (defines `\FASTBUILD`, reuses `main.tex`)
  - `references.bib` — Bibliography database
- **sections/**
  - `sections/frontmatter/main.tex` — Front matter (independently compilable)
  - `sections/body/main.tex` — Body (independently compilable)
  - `sections/appendix/main.tex` — Appendix (independently compilable, handles `\appendix`)
  - `sections/backmatter/main.tex` — Back matter (independently compilable, includes bibliography)
  - `sections/generated/` — Script-generated LaTeX fragments (write-only, never hand-edit)
- **scripts/** — Reproducible experiment scripts (orchestrated by `scripts/run_all.py`)
- **artifacts/** — Exported audit artifacts (CSV/PNG/JSON etc.)

## Build

Run experiments first, then compile. New experiment scripts must be added to `scripts/run_all.py`.

Fast build:

```bash
latexmk -pdfxe -interaction=nonstopmode -halt-on-error -file-line-error main_fast.tex
```

Full build (for final export):

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

## Writing Conventions

### Label addressing

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

New experiment scripts must be added to `scripts/run_all.py`'s steps list.
