# P7 Submission Note -- 2026-03-30

Paper: `2026_conservative_extension_chain_state_forcing_apal`
Target journal: `Annals of Pure and Applied Logic (APAL)`
Stage: `P7 Submission Pack Hardening`

## Current status

`not_submission_ready_yet`

The paper-local submission pack is internally verified, but the package is
still blocked on title-page author metadata in `main.tex`.

## Real blocker

1. `main.tex` still has an empty `\author{}` field.
   - Location: `main.tex:59`
   - Local fact: no author names, affiliations, or corresponding-author
     details are present anywhere on the manuscript title page.
   - External policy check completed on 2026-03-30: APAL's current Guide for
     Authors states that the journal uses single anonymized review and
     requires all authors to be listed in the manuscript and entered in the
     submission system.
   - Practical consequence: do not upload the manuscript until the definitive
     author list and corresponding-author metadata are inserted.

## Local verification

- Ran `pdflatex -interaction=nonstopmode -halt-on-error -file-line-error main.tex`
- Ran `bibtex main`
- Ran `pdflatex -interaction=nonstopmode -halt-on-error -file-line-error main.tex` twice more
- Result: `main.pdf` built successfully at 37 pages
- `main.tex` inputs 9 section files plus appendix; all inputs resolved
- `main.tex` does not input any file from `sequel/`
- All submission-root `.tex` files are below the 800-line cap; max is
  `sec_null_decomposition.tex` at 580 lines
- Bibliography resolved successfully through BibTeX; the built `main.bbl`
  contains 15 `\bibitem` entries
- No undefined citation or dangling cross-reference warnings were observed in
  the local final build

## Materials hardened in this pass

- Corrected `cover_letter_apal.txt` page count from "approximately 45 pages"
  to the current locally verified `37` pages
- Corrected `submission_checklist.md` so that missing author metadata is
  recorded as a blocker rather than as an anonymous-review advisory
- Updated `TRACK_BOARD.md` so P7 reflects the true blocked state and links to
  this note

## Non-blocking local issue

- One overfull `\hbox` remains in `sec_introduction.tex` at lines 34--36 in
  the current local build. This is a typesetting warning, not a submission
  blocker.

## Author-side risks not decidable from this directory alone

- If generative AI or AI-assisted technologies were used in manuscript
  preparation, APAL currently requires a disclosure section before the
  references on first submission. The manuscript does not currently contain
  such a section.
- Competing-interest and funding declarations are submission-system artifacts,
  not verifiable from this paper-local directory.
