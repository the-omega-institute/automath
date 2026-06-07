# Venue/Bibliography Live Check Record (2026-06-07)

This record summarizes `review_bundle/VENUE_BIBLIOGRAPHY_LIVE_CHECK_2026-06-07.log` for the finite venue/bibliography support surface of `main.tex`.  It is a dated local-readiness record only.  For any submission after 2026-06-07 Asia/Singapore, upload-time compliance requires either a fresh upload-time check or an explicit unchanged-rule statement tying the completed upload to the rule state observed in this record.

## Command Record

- Command: PowerShell Invoke-WebRequest against CICM route pages, support locator, and bibliography authority pages.
- Environment: Windows PowerShell 5.1 from paper directory; network enabled.
- Source state: current working tree after Stage A2 round 2 source edits and post-inventory verifier/extractor refresh; before final digest refresh.
- Local run time: 2026-06-07 23:48:52 Asia/Singapore.
- UTC run time: 2026-06-07 15:48:52 UTC.
- Exit code: 0.
- Log path: `review_bundle/VENUE_BIBLIOGRAPHY_LIVE_CHECK_2026-06-07.log`.

## Checked Surfaces
- CICM 2026 CFP route: `https://cicm-conference.org/2026/cicm.php?event=&menu=cfp`, HTTP status 200, final URL `https://cicm-conference.org/2026/cicm.php?event=&menu=cfp`, reachable True.
- EasyChair CICM 2026 submission page: `https://easychair.org/conferences/?conf=cicm2026`, HTTP status 200, final URL `https://easychair.org/account/signin?l=6303605635947824984.1780854535.6af2e7b1`, reachable True.
- Springer LNCS guideline page: `https://www.springer.com/gp/computer-science/lncs/conference-proceedings-guidelines`, HTTP status 200, final URL `https://www.springer.com/gp/computer-science/lncs/conference-proceedings-guidelines`, reachable True.
- Lean DOI resolver: `https://doi.org/10.1007/978-3-319-21401-6_26`, HTTP status 200, final URL `https://link.springer.com/chapter/10.1007/978-3-319-21401-6_26`, reachable True.
- LeanDojo OpenReview locator: `https://openreview.net/forum?id=w8D4aiw9w9`, HTTP status 200, final URL `https://openreview.net/forum?id=w8D4aiw9w9`, reachable True.
- Draft Sketch Prove arXiv record: `https://arxiv.org/abs/2210.12283`, HTTP status 200, final URL `https://arxiv.org/abs/2210.12283`, reachable True.
- AFP DOI resolver: `https://doi.org/10.1007/978-3-319-20615-8_1`, HTTP status 200, final URL `https://link.springer.com/10.1007/978-3-319-20615-8_1`, reachable True.
- newmath public source repository: `https://github.com/the-omega-institute/newmath`, HTTP status 200, final URL `https://github.com/the-omega-institute/newmath`, reachable True.
- automath candidate support branch/path: `https://github.com/the-omega-institute/automath/tree/dev-automation-integration/papers/publication/2026_auditable_theory_to_paper_pipeline`, HTTP status 200, final URL `https://github.com/the-omega-institute/automath/tree/dev-automation-integration/papers/publication/2026_auditable_theory_to_paper_pipeline`, reachable True.

## Conclusions and Boundary

- Venue conclusion: CICM 2026 presentation-only route, EasyChair locator, and LNCS guideline page were checked as a dated local-readiness observation on 2026-06-07 Asia/Singapore; upload-time compliance still requires an actual upload-time or unchanged-rule record.
- Bibliography conclusion: cited public literature, public source locator, and candidate automath support path were checked as reachable when available; local review-bundle entries remain conditional support notes until exact upload or final-state byte equality is recorded.
- Boundary: this is a dated live route, locator, and bibliography check only; it is not upload-time compliance by itself, venue acceptance, upload receipt, archive minting, Lean rebuild, daemon run, artifact rerun evidence, or public byte-equality certification.
