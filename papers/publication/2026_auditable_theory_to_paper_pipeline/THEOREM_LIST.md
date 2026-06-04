# Theorem List

This paper is a systems and workflow note.  Its theorem spine is the
discovery-gate calculus extracted from the pinned BEDC source file:

```text
D:/omega/newmath/papers/bedc/parts/visions/audit_map_methodology/automated_theory_discovery_pipeline_calculus.tex
```

## Core Discovery-Gate Spine

| Manuscript role | Source label | Status |
|---|---|---|
| discovery claims require complete source/evidence ledgers | `thm:automated-discovery-dna-completeness-obligation` | source label extracted |
| statement/code output is not discovery | `cor:automated-discovery-statement-code-insufficient` | source label extracted |
| mechanical expansion is not discovery | `thm:automated-discovery-mechanical-not-discovery` | source label extracted |
| compression alone is not discovery | `thm:automated-discovery-compression-not-discovery` | source label extracted |
| certificate ledger is required | `thm:automated-discovery-certificate-ledger-required` | source label extracted |
| positive transition implies discovery under the gate | `thm:automated-discovery-positive-implies-discovery` | source label extracted |
| scored claims need public weights | `thm:automated-discovery-scored-claims-public-weights` | source label extracted |
| gate-kind soundness | `thm:automated-discovery-gate-kind-sound` | source label extracted |
| demotion soundness | `thm:automated-discovery-demotion-soundness` | source label extracted |
| lineage DAG | `thm:automated-discovery-lineage-dag` | source label extracted |
| lowest score is not necessarily the best target | `thm:automated-discovery-lowest-score-not-best-target` | source label extracted |
| selection favors classifier change | `thm:automated-discovery-selection-favours-classifier-change` | source label extracted |
| no unpaid discovery | `thm:automated-discovery-no-unpaid-discovery` | source label extracted |
| pipeline safety | `thm:automated-discovery-pipeline-safety` | source label extracted |
| main pipeline theorem | `thm:automated-discovery-pipeline-theorem` | source label extracted |
| discovery principle | `prin:automated-discovery-principle` | source label extracted |

## Manuscript Use

The technical supplement imports the full sixteen-label source interface listed
above through bounded paraphrase rows in `main.tex`, mirrored in
`source_interface_record.json`, and checked by
`review_bundle/verify_source_interface_record.py`. These rows are the complete
source-interface spine for this paper; they are not a claim to rebuild or restate
the whole BEDC source theory.

## Verification Needed Before Submission

Before quoting exact theorem statements, reread the pinned source file and
copy the precise statement wording into the manuscript or a checked appendix
note.  Do not paraphrase labels as formal Lean theorems unless the source file
itself supports that status.
