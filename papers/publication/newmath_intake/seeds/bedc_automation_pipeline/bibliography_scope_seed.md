# Bibliography Scope Seed: BEDC Automation Pipeline

This is an intake-level bibliography and comparison scaffold.  It is not
`BIB_SCOPE.md`, does not promote the seed, and does not claim that literature
review is complete.

## Route-Specific Comparison Frame

For the first CICM presentation-only route, the comparison should be narrow:

- proof-assistant and formal-mathematics infrastructure;
- AI-assisted formalization workflows;
- reproducibility and audit trails for generated mathematical artifacts;
- source-to-paper traceability;
- failure detection for agent-generated or agent-edited mathematical text.

The paper should not compete with broad automated-theorem-proving systems,
complete formalization environments, or foundation papers about BEDC itself.

## Citation Buckets To Fill After Promotion

| Bucket | Use in manuscript | Inclusion rule | Exclusion rule |
|---|---|---|---|
| Interactive theorem proving systems | Position Lean-backed source artifacts and proof-assistant workflows | cite mature systems and workflow papers relevant to formal mathematics | do not survey proof assistants exhaustively |
| AI for theorem proving / formalization | Distinguish advisory AI work from load-bearing proof evidence | cite LLM/formalization papers with explicit evaluation or workflow claims | do not imply this paper introduces a theorem prover |
| Mathematical knowledge management | Position source maps, artifact inventories, and traceability | cite systems that connect mathematical text, formal objects, and repositories | do not frame BEDC theory as the main knowledge-management contribution |
| Reproducible computational artifacts | Motivate command logs, artifact reruns, and limitation ledgers | cite reproducibility or artifact-evaluation practices relevant to math/software | do not claim Rule110 dynamic evidence was rerun for the CICM note |
| Agent governance and evaluation | Position deterministic gates and anti-hollow checks | cite work on evaluating or constraining generated code/proofs/text | avoid generic AI-safety framing unless directly tied to formal artifacts |

## Search Targets After Human Promotion

After promotion, the active paper should run a live literature pass for:

- CICM proceedings papers on mathematical software and knowledge management;
- ITP/CPP/JAR/JFR papers on proof-assistant workflow infrastructure;
- recent AI-for-formalization papers that distinguish generated suggestions
  from verified proof artifacts;
- artifact-evaluation and reproducibility practices for theorem-proving or
  mathematical-software submissions.

The search should be recorded in the promoted paper's `BIB_SCOPE.md`, not in
this seed file.

## Comparison Claims Allowed

The promoted CICM note may claim:

- the contribution is a workflow architecture and evidence discipline;
- AI agents are used for proposal, review, drafting, and triage, while
  deterministic checks and human promotion decisions carry the evidential load;
- the case studies expose concrete failure modes in paper-generation workflows:
  overlap/submitted blocking, hollow theorem growth, intake isolation, and
  artifact limitation handling.

## Comparison Claims To Avoid

The promoted CICM note must not claim:

- superiority over existing formalization systems;
- a new theorem-proving method;
- fully automatic mathematical discovery;
- complete verification of all BEDC source declarations;
- successful rerun of the Rule110 artifact suite;
- automatic venue selection or acceptance.

## Minimum Bibliography Work Before Submission

Before any actual submission, the promoted active paper must:

1. perform a live venue-page check for CICM formatting and bibliography rules;
2. add a compact related-work paragraph or table using verified citations;
3. ensure every comparison supports the narrow workflow claim;
4. remove any citation bucket that was not actually filled;
5. record the literature pass date in the active paper's `BIB_SCOPE.md`.
