# Submission Compile Rerun Log

- date: 2026-06-01
- source commit: `1afbc01f7`
- workspace state: uncommitted submission-interface edits present after this source commit
- environment: Windows PowerShell; MiKTeX LaTeX engines; cwd `D:/omega/automath/papers/publication/2026_auditable_theory_to_paper_pipeline`
- log path: `submission_compile_rerun_log.md`

## Commands

| Command | Exit code | Output log |
|---|---:|---|
| `bibtex main` | 0 | console output in current session; bibliography output `main.blg` |
| `xelatex -interaction=nonstopmode main.tex` | 0 | `main.log` |
| `xelatex -interaction=nonstopmode main.tex` | 0 | `main.log` |
| `xelatex -interaction=nonstopmode submission_abstract.tex` | 0 | `submission_abstract.log` |
| `pdflatex -interaction=nonstopmode -halt-on-error submission_abstract.tex` | 0 | `submission_abstract.log` |
| `pdflatex -interaction=nonstopmode -halt-on-error submission_abstract.tex` | 0 | `submission_abstract.log` |

## Recorded Outputs

- `main.log`: `Output written on main.pdf (18 pages).`
- `submission_abstract.log`: `Output written on submission_abstract.pdf (2 pages).`

## Evidence Boundary

This log records only the LaTeX/BibTeX compilation commands above. It is not a
full-source rebuild, publication-daemon run, or Rule110 dynamic artifact rerun.
