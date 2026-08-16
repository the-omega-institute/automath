# Does every paper build from its own checked-in sources?

Every document root under `papers/publication` was rebuilt from scratch: `latexmk -C`, auxiliaries
deleted, then `latexmk -pdfxe` with no arguments beyond the file name — no command-line macro
definitions, no environment overrides, no `latexmkrc`. 70 documents across 53 directories.

This check had never been run. It was prompted by one paper where a green build turned out to
depend on a macro supplied on the command line, which makes a document look sound to whoever runs
that exact invocation and broken to everyone else, including a journal's production desk.

## Seven documents produce no PDF at all

| paper | document | undefined macros | undefined citations | undefined refs |
|---|---|--:|--:|--:|
| `2026_projection_ontological_mathematics_core_tams` | main | 17 | 36 | 143 |
| `submitted_2026_finite_window_rigidity_fibonacci_numeration_fq` | main | 33 | 15 | 111 |
| `submitted_2026_resolution_folding_core_symbolic_dynamics_jnt` | main | 33 | 15 | 111 |
| `submitted_2026_sharp_three_window_threshold_fibonacci_conjugacy_nonlinearity` | main | 1 | 42 | 144 |
| `submitted_2026_tilt_dynamics_cylinder_information_parry_measure_qtds` | main | 15 | 37 | 100 |
| `submitted_2026_zero_jitter_information_clocks_parry_gibbs_rigidity_jtp` | main | 15 | 37 | 100 |
| `2026_auditable_theory_to_paper_pipeline` | appendix_full_technical_ledger | 4 | 63 | 313 |

Five of the six failing `main.tex` files are in directories marked as already submitted.

The undefined macro is `\leanverified` in every case but one. It is a house convention: five other
papers define it identically as `\newcommand{\leanverified}[1]{}`, a one-argument no-op that records
a Lean declaration name in the source without typesetting anything. The papers above use it and
never define it. The failing appendix in the auditable-pipeline paper is a different macro,
`\ScriptOK`, and that document is a standalone ledger rather than the paper itself.

The large undefined-reference counts are consequences, not separate defects: once the macro error
aborts the run, no `.aux` is written and every cross-reference and citation in the document reports
as unresolved on the following pass.

## Three more build, but print unresolved citations

| paper | pages | undefined citations |
|---|--:|--:|
| `2026_zeckendorf_folds_sturmian_rigidity_parry_divergence_etds` | 31 | 31 |
| `submitted_2026_folded_histograms_sampling_certificates_parry_mismatch_siads` | 36 | 41 |
| `submitted_2026_folded_rotation_histogram_etds` | 31 | 31 |

These exit 0 and produce a full-length PDF, which is why nothing caught them. The citations print
as `[?]`. A static scan of `\cite` keys against the bibliography agrees with the compiler in all
three cases, so this is not a log-parsing artifact.

## What this does not say

`sn-article.tex` in the tilt-dynamics and zero-jitter directories also fails. That is the Springer
Nature template shipped alongside the manuscript, not the manuscript, and its failure is expected.
The `cover_letter` failure in the fibonacci-moduli directory is likewise not the paper.

A checked-in `main.pdf` exists for several of the failing papers, and `papers/publication/.gitignore`
excludes `*.pdf`. That is precisely how a document can stop building without anyone noticing: the
PDF on disk stays valid and untracked while the sources that produced it drift away from it.

## Reproducing

```
cd papers/publication/<paper>
latexmk -C main && latexmk -pdfxe -interaction=nonstopmode main
```

Any invocation that needs more than this is not a reproducible build.
