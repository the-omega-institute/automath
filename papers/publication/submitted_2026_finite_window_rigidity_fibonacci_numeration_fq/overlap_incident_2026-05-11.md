# Overlap incident: FQ/JNT manuscript and DCDS-A manuscript

Date recorded: 2026-05-11

Affected manuscripts:
- `submitted_2026_finite_window_rigidity_fibonacci_numeration_fq`
- `2026_sharp_three_window_threshold_fibonacci_conjugacy_dcds`

Issue:
The FQ/JNT manuscript and the later DCDS-A manuscript share the same core theorem package: finite-window Fibonacci folding, overlapping-window reconstruction, the `m >= 3` threshold, finite-memory inverse/conjugacy, residue-window decoding, and Fischer-cover identification. The DCDS-A manuscript adds the two-window branch classification, metallic comparison, and a stronger DCDS-A framing, but the overlap is too large to treat the older manuscript as a separate active submission candidate.

Why this happened:
The existing pipeline had three gaps.

1. The deepening prompt only instructed agents to check `papers/publication/2026_*/*.tex`, so historical `submitted_2026_*` directories were not explicitly covered by the self-plagiarism scan.

2. The cross-paper dedup filter only compared theorem-like environments by long verbatim phrase overlap. The older FQ/JNT manuscript and the DCDS-A manuscript use different titles, labels, section structure, and wording, so the literal-phrase detector did not flag the semantic overlap.

3. The DCDS-A `scope_contract.md` did mention the FQ manuscript as overlapping reconstruction/local-inverse material, but it treated the DCDS-A paper as owning the flagship theorem and did not force the old FQ/JNT route to be closed on the board before DCDS-A could advance.

Fix applied:
`tools/chatgpt-oracle/oracle_pipeline.py` now includes a semantic submission-overlap guard. It extracts high-signal claim-package markers such as Fibonacci finite-window fold, sliding overlap reconstruction, `m >= 3` threshold, finite-memory conjugacy, residue-window decoder, and Fischer cover. If a current paper shares enough core markers with a submitted/rejected sibling that has not been explicitly closed, superseded, merged, or parked on `PROGRAM_BOARD.md`, Stage A blocks before the paper can advance.

Additional fixes:
- Board status skipping now recognizes UTF-8 Chinese statuses such as `已投`, `拒稿`, `审稿中`, `骨架`, and `待分诊`.
- The deepening prompt now explicitly tells agents to check both `papers/publication/2026_*/*.tex` and `papers/publication/submitted_2026_*/*.tex`.
- A-DEDUP sibling collection now includes historical `submitted_*` archives.
- Regression tests were added in `tools/chatgpt-oracle/tests/test_pipeline_supervisor.py`.

Operational rule going forward:
A split is not valid merely because the title, venue, or narrative changes. It must own a distinct theorem package. If an earlier submitted or rejected manuscript has overlapping core claims, the board must first record one of the following decisions:
- old route closed;
- old manuscript superseded;
- old manuscript merged into the new one;
- old manuscript parked and not an active candidate;
- explicit human-approved non-overlap rationale.
