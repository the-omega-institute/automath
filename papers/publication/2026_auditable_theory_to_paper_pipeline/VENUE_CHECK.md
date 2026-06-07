# Venue Check

- historical check date: 2026-06-01
- latest local-readiness verification date: 2026-06-07 Asia/Singapore
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

The 2026-06-04 near-submission check verified the live CICM 2026 call page and
the bibliography records used by `references.bib`.  The later dated
local-readiness check is
`review_bundle/VENUE_BIBLIOGRAPHY_LIVE_CHECK_2026-06-07.log`, summarized by
`review_bundle/VENUE_BIBLIOGRAPHY_LIVE_CHECK_2026-06-07.md`.  These records state
only dated local readiness.  They do not certify compliance at a later
submission time unless the submitted surface adds either a fresh upload-time
venue/bibliography check or an explicit unchanged-rule statement tying the
completed upload to the 2026-06-07 observed rule state.  Under that dated
readiness reading, the route is suitable for the paper as a CICM
presentation-only / mathematical software workshop submission: the manuscript is
framed as ongoing workflow and evidence architecture, not as a
proceedings-length theorem-proving system paper.

Bibliography verification status, last locally checked on 2026-06-07
Asia/Singapore:

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

## Dated Local Readiness

| Requirement | Current status | Next action |
|---|---|---|
| 2 pages plus bibliography | local `main.pdf` build records indicate the intended 2-page body plus bibliography | refresh the compile and submission form check before upload |
| narrow work-in-progress claim | satisfied by the abstract and scope section at this source state | do not broaden to full source rebuild or Rule110 validation |
| source/artifact access | source paths are recorded in `SOURCE_MAP.md` and `ARTIFACT_INVENTORY.md` | decide whether to expose a public artifact link before submission |
| bibliography | compact related-work entries were reachable in the 2026-06-07 dated check | refresh at submission time or add an unchanged-rule statement |
| style | converted to LNCS class and `splncs04` bibliography style | keep final check against EasyChair form |

## Blockers Remaining

- author/affiliation block must be confirmed;
- public artifact/source link strategy is pinned `newmath` repository plus
  supplemental upload unless a later archive is minted;
- no fresh full-source command rerun is claimed.
