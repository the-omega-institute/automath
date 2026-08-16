# Pipeline: Finite-Site Component Gerbes

Target: Cahiers de Topologie et Geometrie Differentielle Categoriques

Repository package status: prepared, with one recorded source-hygiene item

External submission status: unknown

## Current Stage Status

| Stage | Status | Evidence | Notes |
|---|---|---|---|
| Research and theorem development | completed | finished manuscript and supplement | Earlier research directives are no longer active. |
| Cahiers reframing | completed | current title, abstract, section structure, and `cover_letter_cahiers.txt` | The article is framed around finite-site component gerbes, terminal rigidity, and prescribed realization. |
| Article build | completed | `submission_checklist.md`, 2026-08-17 | `main.pdf` builds successfully at 26 pages. |
| Supplement build | completed | `submission_checklist.md`, 2026-08-17 | `supplement.pdf` builds successfully at 6 pages. |
| Submission pack | prepared | checklist, author metadata, declarations, and Cahiers cover letter are present | The checklist records 10/11 checks passing; the remaining item is unused bibliography data. |
| External submission | unknown | no repository record | Submission date, handling editor, and decision are not inferred. |

There is no author-metadata blocker. Both built documents list Haobo Ma and
Wenlin Zhang with affiliations and email addresses.

## Principal Results

| Role | Label | Current statement |
|---|---|---|
| Theorem A | `thm:canonical-lift-rigidity` | For a representative-rigid abelian-banded prestack lift, terminal essential surjectivity forces surjectivity of the terminal sheafification unit; with `H^1` vanishing, the converse holds and unique amalgamation is equivalent under the stated separatedness hypotheses. |
| Theorem B | `thm:prescribed-component-image-construction` | On the stated finite good-cover site, one prestack explicitly realizes a prescribed finite family of maps `H_2(N, Z) -> A` while controlling its component presheaf, terminal fibre, neutrality pattern, and matching behavior. |
| Corollary C | `thm:wedge-sphere-two-component-label-loss` | On the selected open-star covers of a wedge of `beta` 2-spheres, two complementary nonzero component images realize exactly the finite abelian groups satisfying the stated generator and non-prime-power-cyclic criterion. |

## Supporting Results

- `prop:finite-site-semantic-interface`: matching families, sheafification,
  stackification, and terminal fibres on the supplied finite site.
- `prop:standard-component-gerbe-package`: the standard Giraud component-gerbe
  and neutrality package used by the paper.
- `thm:terminal-torsor-obstruction` and `thm:marked-terminal-torsor-form`:
  terminal-fibre control before the rigidity theorem.
- `thm:gerbe-null-semantics`: matching without amalgamation versus non-neutral
  component gerbes under the stated lift hypotheses.
- `prop:finite-site-comparison`: the connected-overlap Cech/simplicial
  comparison used by the realization theorem.
- `prop:uct-aggregate-package`: UCT evaluation images and aggregate quotients.
- `thm:empirical-model-boundary` and `prop:equivariant-no-selection`: the
  boundary with empirical-model obstruction data.
- `prop:presentation-comparison-naturality`: naturality along specified
  presentation comparisons.

## Current Source Map

### Article

1. `sec_introduction.tex` - Introduction.
2. `sec_preliminaries.tex` - The finite-site interface.
3. `sec_gerbe_obstruction.tex` - Component gerbes and terminal rigidity.
4. `sec_homological_visibility.tex` - Finite good-cover sites and prescribed realization.
5. `sec_homological_visibility_intrinsic.tex` - Homological images and aggregate quotients.
6. `sec_branch_aggregation.tex` - The wedge-of-spheres realization corollary.
7. `sec_branch_contextuality.tex` - Boundary with empirical-model obstructions.
8. `sec_conclusion.tex` - Conclusion.
9. `sec_presentation_appendix.tex` - Appendix A, naturality for specified presentation comparisons.

### Supplement

- `sec_appendix.tex` - Appendices A--C: presentation-comparison bookkeeping,
  finite calculations, and a narrow lower-language separation example.

No deleted section file is part of either built document.

## Submission Pack

Current repository evidence:

- `cover_letter_cahiers.txt` is present. This establishes the current cover
  letter file, but not that it has been sent.
- `submission_checklist.md` records successful clean XeLaTeX builds for both
  documents, correct 26-page and 6-page outputs, resolved references, and
  present author metadata.
- The checklist records 17 cited entries out of 46 bibliography entries. The
  29 unused entries are a source-hygiene issue, not an undefined-citation error.
- Competing-interest and AI-use declarations are present in the article; any
  additional submission-system requirements remain unknown until recorded.

Repository package status is therefore `prepared_with_source_hygiene_item`.
The repository does not establish whether the package has been submitted.

## Priority and Sourcing Record

Do not infer priority, sourcing completeness, or acceptance probabilities from
this pipeline summary. The dated records remain authoritative:

- `artifacts/literature_check.md` states the narrow priority boundary, including
  the standard Giraud and Cech/UCT inputs and the limited paper-specific claims.
- The same record identifies three unverified bibliography entries and documents
  the service-access limitations of that audit.
- `artifacts/oracle_sprint_A9_*.md` contains historical assessments and
  probabilities for the manuscript versions or proposed extensions examined at
  those dates. They are not current submission events or decisions.

## Superseded Pipeline Record

Earlier versions of this file described a different manuscript architecture,
deleted source files, a 37-page build, a different bibliography count, an empty
author field, and a different cover letter. Those entries are superseded by the
2026-08-17 bidirectional build check in `submission_checklist.md`; they must not
be used as current package status.
