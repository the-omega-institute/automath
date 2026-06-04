# Submission Compile Rerun Log

- date: 2026-06-04
- source state: Git `HEAD` `bae95b1de5fdbdd4ecf88b294e93fac99a3670d7` with working-tree bytes recorded by root-source digests in `review_bundle/FINAL_DIGESTS_SHA256.md`
- workspace state at recording: see `git status --short`
- environment: Windows PowerShell; XeTeX/MiKTeX 24.1; BibTeX 0.99d; cwd `D:/omega/automath/papers/publication/2026_auditable_theory_to_paper_pipeline`
- digest manifest: `review_bundle/FINAL_DIGESTS_SHA256.md` (`fa4a66d37554db9761dc3d603b3af5cb27b16a45d32abb5f0c4085828ab58711`)
- log path: `submission_compile_rerun_log.md`

## Source Digests Used For This Compile

| SHA-256 | Relative path |
|---|---|
| `d93890ba5229592725e6f197954fa7a0ff4a2c54096dce5e9f5284c058c58fc6` | `main.tex` |
| `f85aba8b2ecd9053c52a2545268ce4d409234073e3e7c1e7c017fb6723a643a5` | `submission_abstract.tex` |
| `6e9a1bf10edad9ff0bfaf8b4440fcdb19e9dd3cb1e4bef5f9c35e70638e521c1` | `references.bib` |

## Commands

| Command | Exit code | Output log/artifact |
|---|---:|---|
| `bibtex main` | 0 | `main.blg`; regenerated `main.bbl` |
| `xelatex -interaction=nonstopmode main.tex` | 0 | `main.log`; refreshed bibliography/cross-references |
| `xelatex -interaction=nonstopmode main.tex` | 0 | `main.log`; final compile pass |

## Recorded Outputs

| SHA-256 | Relative path |
|---|---|
| `a388b83a0dd7085c8f64a71c2cc7ea6312bcbdffbcdd4cab50e1e0178c7f1991` | `main.log` |
| `48da96c8c01df79e152e9bac37f9de8d067fcd8c68ba2e3d5a8f5e423dc23cf2` | `main.pdf` |
| `f160a902a64c7599ba0774a696090dcd6755654debb9deb65d734618ed4db2f1` | `main.bbl` |

## Verification Notes

- Final `xelatex` exit code: 0.
- Final PDF output: `main.pdf` (67 pages, as reported by `main.log`).
- Expected LaTeX diagnostics remain layout warnings only: overfull/underfull boxes and the existing hyperref PDF-string warning.
- No `LaTeX Warning: Label(s) may have changed` rerun request remains after the final pass.

## Git Status Snapshot

```text
M main.tex
 M review_bundle/FINAL_DIGESTS_SHA256.md
 M review_bundle/primary_claim_inventory_freshness_2026-06-04.md
 M submission_compile_rerun_log.md
```
