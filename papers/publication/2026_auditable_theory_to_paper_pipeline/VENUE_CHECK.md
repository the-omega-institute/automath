# Venue Check

- historical check date: 2026-06-01
- final near-submission verification date: 2026-06-03
- venue: CICM 2026, 19th Conference on Intelligent Computer Mathematics
- official page:
  `https://cicm-conference.org/2026/cicm.php?event=&menu=cfp`

## Confirmed Route

The official CICM 2026 call was rechecked on 2026-06-03 and still lists a
work-in-progress presentation-only route:

- presentation-only papers describe ongoing research;
- length is 2 pages plus bibliography;
- review is light-weight;
- accepted presentation-only papers do not appear in the Springer proceedings,
  although they may be published jointly with workshop proceedings;
- accepted presentation-only papers are showcased in a dedicated presentation
  session and a poster session.

## Dates

| Item | Date |
|---|---|
| Presentation-only submission deadline | 2026-06-15 |
| Conference | 2026-09-21 to 2026-09-25 |

## Submission And Style

The call points formal submissions to EasyChair and the Springer LNCS style
files.  Before submission, use the same style unless the presentation-only
submission form gives separate instructions.

## Final Verification Record

The 2026-06-03 near-submission check verified the live CICM 2026 call page and
the bibliography records used by `references.bib`.  The route remains suitable
for the current paper as a CICM presentation-only / mathematical software
workshop submission: the manuscript is framed as ongoing workflow and evidence
architecture, not as a proceedings-length theorem-proving system paper.

Bibliography verification status on 2026-06-03:

- `deMouraKADR2015Lean`: DOI `10.1007/978-3-319-21401-6_26` verified.
- `YangEtAl2023LeanDojo`: NeurIPS/OpenReview and arXiv `2306.15626` record
  verified; no DOI is required for this route.
- `JiangEtAl2023DraftSketchProve`: arXiv `2210.12283` and DOI
  `10.48550/arXiv.2210.12283` verified.
- `BlanchetteHMN2015AFP`: DOI `10.1007/978-3-319-20615-8_1` verified.
- Local artifact entries are intentionally non-archival unless a later public
  archive is minted; the public source link for the imported theorem spine is
  the pinned `newmath` repository.

## Fit Assessment

The current paper is a strong fit for the presentation-only route because the
CICM topics explicitly include:

- formal mathematics;
- interactive theorem proving;
- AI and LLMs in mathematics;
- formalization of mathematical theories;
- applications of proof assistants and machine-learning systems;
- mathematical knowledge management;
- case studies, evaluations, benchmarks, and experience reports.

## Current Compliance

| Requirement | Current status | Next action |
|---|---|---|
| 2 pages plus bibliography | current `main.pdf` compiles as 2 content pages plus bibliography | keep bibliography outside the two-page body budget |
| narrow work-in-progress claim | satisfied by current abstract and scope section | do not broaden to full source rebuild or Rule110 validation |
| source/artifact access | source paths are recorded in `SOURCE_MAP.md` and `ARTIFACT_INVENTORY.md` | decide whether to expose a public artifact link before submission |
| bibliography | compact related-work entries verified on 2026-06-03 for Lean, LeanDojo, Draft--Sketch--Prove, AFP, public source, and supplemental bundle records | add only a later archive DOI/URL if one is minted |
| style | converted to LNCS class and `splncs04` bibliography style | keep final check against EasyChair form |

## Blockers Remaining

- author/affiliation block must be confirmed;
- public artifact/source link strategy is pinned `newmath` repository plus
  supplemental upload unless a later archive is minted;
- no fresh full-source command rerun is claimed.
