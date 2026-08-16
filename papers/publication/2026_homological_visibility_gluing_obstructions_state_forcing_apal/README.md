# Finite-Site Component Gerbes, Terminal Rigidity, and Prescribed Realization

## Current Position

- Working directory: `papers/publication/2026_homological_visibility_gluing_obstructions_state_forcing_apal`.
  The directory name is a legacy identifier; it is not the current title, scope,
  or journal target and must not be renamed as part of documentation maintenance.
- Target journal: Cahiers de Topologie et Geometrie Differentielle Categoriques.
- Article: `main.pdf`, 26 pages.
- Supplement: `supplement.pdf`, 6 pages.
- Current structural authority: `submission_checklist.md`, checked against both
  built documents on 2026-08-17.

## Article Scope

The article studies abelian-banded prestack lifts of a presheaf on a finite
site with a terminal object. The site, presheaf, band, prestack lift, and
component classes are supplied inputs. The paper does not claim that these
data arise canonically from a bare empirical model.

The principal results are:

1. Terminal rigidity for representative-rigid prestack lifts under slice
   separatedness and an `H^1`-vanishing hypothesis.
2. An explicit finite-good-cover construction realizing prescribed maps
   `H_2(N, Z) -> A` as component-gerbe evaluations while controlling the
   component presheaf, terminal fibre, and neutrality pattern.
3. A two-component realization criterion on selected open-star covers of
   wedges of 2-spheres.

The article also records the boundary with empirical-model obstructions and
naturality along specified presentation comparisons. Standard component-gerbe
and gerbe-classification inputs are credited to the classical literature; the
paper-specific priority boundary is recorded in `artifacts/literature_check.md`.

## Current Source Structure

The article inputs, in order:

- `sec_introduction.tex`
- `sec_preliminaries.tex`
- `sec_gerbe_obstruction.tex`
- `sec_homological_visibility.tex`
- `sec_homological_visibility_intrinsic.tex`
- `sec_branch_aggregation.tex`
- `sec_branch_contextuality.tex`
- `sec_conclusion.tex`
- `sec_presentation_appendix.tex` as Appendix A

The supplement inputs only `sec_appendix.tex`, which contains Appendices A--C.

## Package Status

- Both built documents compile and have resolved citations and cross-references.
- Both authors, affiliations, and email addresses are present in the article and
  supplement.
- `cover_letter_cahiers.txt` is the cover letter currently present in the
  repository.
- `submission_checklist.md` records 10 of 11 checks as passing. The remaining
  source-hygiene item is 29 unused entries in `references.bib`; it does not
  create undefined citations or add those entries to the generated bibliography.
- No repository record establishes an external submission date, handling editor,
  or journal decision. Those fields remain unknown.
