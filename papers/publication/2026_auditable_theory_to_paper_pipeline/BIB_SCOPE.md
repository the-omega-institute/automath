# Bibliography Scope

## Route

The initial route is a CICM-style presentation-only or workshop paper.  The
related-work pass should be compact and focused on mathematical software and
formalization workflow infrastructure.

## Citation Buckets

| Bucket | Manuscript use | Rule |
|---|---|---|
| proof-assistant workflows | position Lean-backed source artifacts and project workflow | cite mature workflow or infrastructure papers, not an exhaustive Lean survey |
| AI-assisted formalization | distinguish advisory AI suggestions from verified proof evidence | cite papers with explicit formalization or theorem-proving evaluation |
| mathematical knowledge management | position source maps, artifact inventories, and traceability | cite systems connecting mathematical text, formal objects, and repositories |
| reproducible computational artifacts | motivate command logs, reruns, and limitation ledgers | cite artifact-evaluation or reproducibility practices relevant to math/software |
| agent governance and evaluation | position deterministic gates and anti-hollow checks | keep claims tied to formal artifacts and generated mathematical text |

## Claims Allowed

- The contribution is a workflow architecture and evidence discipline.
- AI agents are advisory; deterministic checks and human promotion decisions
  carry load-bearing evidence.
- The case studies expose concrete failure modes: overlap blocking, hollow
  theorem growth, intake isolation, and artifact limitation handling.

## Claims To Avoid

- superiority over existing formalization systems;
- a new theorem-proving method;
- fully automatic mathematical discovery;
- complete verification of all BEDC source declarations;
- successful rerun of the Rule110 artifact suite;
- automatic venue selection or acceptance.

## Minimum Work Before Submission

1. Recheck the selected venue page and page limit.
2. Add verified citations for each bucket actually used.
3. Remove any comparison bucket not supported by a citation.
4. Record the literature pass date and exact sources checked.

## Venue Check Status

Completed on 2026-06-01 for CICM 2026.  See `VENUE_CHECK.md`.

The confirmed presentation-only route is 2 pages plus bibliography, with a
submission deadline of 2026-06-15.  The related-work pass remains incomplete:
the current `references.bib` contains only local source placeholders and must
be replaced or supplemented with verified literature before submission.

## Related-Work Pass

Completed initial pass on 2026-06-01.

| Bucket | Added citation | Verification source |
|---|---|---|
| proof-assistant workflow | `deMouraKADR2015Lean` | KIT/DBLP-style publication page for the CADE 2015 Lean system description |
| AI-assisted formalization | `YangEtAl2023LeanDojo` | DBLP record for NeurIPS 2023 LeanDojo |
| informal-to-formal guidance | `JiangEtAl2023DraftSketchProve` | arXiv record `2210.12283`, revised 2023 |
| proof archive/artifact traceability | `BlanchetteHMN2015AFP` | CICM 2015 page for Mining the Archive of Formal Proofs |

Remaining bibliography work:

- replace local-source placeholders with public artifact/source references if
  a public link is available before submission;
- add exact URLs or DOIs for any venue-required bibliography style;
- keep the related-work paragraph short enough for the presentation-only page
  budget.
