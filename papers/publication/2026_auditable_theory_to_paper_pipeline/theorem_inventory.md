# Theorem Inventory

This inventory is for the CICM presentation-only / mathematical software
workshop route.  It follows the scope contract: the article is about auditable
theory-to-paper routing for AI-assisted formal mathematics, not a new ATP
method, full BEDC theory exposition, implementation-soundness proof, artifact
semantic validation, external upload, or venue acceptance.

## Primary Route

The five Oracle-required source results are present in `main.tex` as theorem or
corollary environments with proof environments:

| Label | Title | Location | Classification |
| --- | --- | --- | --- |
| `thm:finite-audit-antichain-basis` | Finite Audit Antichain Basis | `main.tex:18727-18788` | mandatory primary-route theorem |
| `thm:canonical-stage-a-obstruction-basis` | Canonical Stage-A Obstruction Basis | `main.tex:18790-18881` | mandatory primary-route theorem |
| `thm:no-theorem-delta-nondischarge` | No-Theorem-Delta Non-Discharge Theorem | `main.tex:18883-18936` | mandatory primary-route theorem |
| `thm:stage-a-real-block-discharge-completeness` | Stage-A Real-Block Discharge Completeness | `main.tex:18938-18990` | mandatory primary-route theorem |
| `cor:current-stage-a-closure-exactness` | Current Stage-A Closure Exactness | `main.tex:18992-19039` | mandatory primary-route corollary |

Each row depends on the retained finite-record support layer:
`thm:presentation-compressed-interface`,
`thm:publication-safety-interface`,
`thm:external-interface-projection-no-free-upgrade`,
`thm:four-case-foreground-support-boundary`,
`cor:stage-a-issue-discharge-normal-form`,
`thm:six-coordinate-submission-boundary-normal-form`, and
`thm:current-round-local-only-fixed-point-classifier`.

The foreground software-workshop kernel is the current-byte Stage-A replay chain
in `main.tex:19556-20599`, including `def:canonical-stage-a-byte-manifest`,
`def:byte-to-atom-compiler`, `def:replayable-stage-a-certificate`,
`thm:byte-to-atom-determinacy`, `thm:replay-kernel-soundness`,
`thm:replay-kernel-completeness`, `thm:replayable-obstruction-adequacy`,
`thm:current-byte-two-coordinate-audit`,
`thm:fixed-replay-rgs-coordinate-exactness`,
`thm:accepted-fixed-replay-rgs-pass-row-current-package`,
`thm:post-qrgs-coordinate-independence`,
`cor:stage-a-replay-kernel-software-surface`,
`lem:maximal-qinv-qrgs-replay-closure`,
`thm:replay-kernel-foreground-closure`,
`thm:canonical-finite-basis-replay-foreground-exactness`,
`thm:cicm-public-surface-maximality`,
`cor:five-challenged-interfaces-replay-foreground`,
`thm:two-coordinate-foreground-maximality`,
`cor:no-implementation-upgrade-from-fixed-replay`, and
`prop:stage-a-replay-route-quotient-preservation`.

## Source Coverage

`main.tex` contains 291 labelled theorem-like environments in the extractor
domain (`definition`, `lemma`, `proposition`, `theorem`, `corollary`), all
labelled and with no duplicate labels.  The JSON inventory records every label
at least once in an item `label` field.  The pinned imported source snapshot
`review_bundle/source_snapshots/automated_theory_discovery_pipeline_calculus_3fb3d6a0641767388a401883062aa522ea0b397b.tex`
contains 36 additional labelled theorem-like environments; these are classified
as imported source-interface/background material rather than included
`main.tex` theorem obligations.

## Proof Gaps

Five labelled proposition-like audit interfaces are not followed by immediate
proof environments:

| Label | Location | Required action |
| --- | --- | --- |
| `audit:venue-submission-pack-gate` | `main.tex:7817-7837` | add a proof environment or reclassify as a non-theorem audit record |
| `audit:submission-artifact-role-separation` | `main.tex:7888-7898` | add a proof environment or reclassify as a non-theorem audit record |
| `audit:review-bundle-availability-condition` | `main.tex:11007-11028` | add a proof environment or reclassify as a non-theorem audit record |
| `audit:case-snapshot-non-rerun-boundary` | `main.tex:11061-11072` | add a proof environment or reclassify as a non-theorem audit record |
| `audit:command-run-boundary-inventory` | `main.tex:11208-11230` | add a proof environment or reclassify as a non-theorem audit record |

These are not hidden by demotion in the JSON inventory; they remain proof
interfaces that must be closed or converted in a later source-edit stage.

## Scope Boundaries

The following stronger readings are out of scope for this article and are
recorded only as upgrade coordinates or split-paper candidates:

- Whole-program gate implementation soundness:
  `thm:implementation-soundness-extension-criterion`,
  `thm:current-package-implementation-upgrade-absence`,
  `cor:submitted-gate-implementation-contract-dichotomy`,
  `cor:no-implementation-upgrade-from-fixed-replay`.
- Fresh formal-source rebuild or axiom-purity closure:
  `thm:formal-source-promotion-obstruction`,
  `thm:source-interface-semantic-completeness-obstruction`,
  `thm:scope-contract-three-coordinate-boundary`.
- Dynamic artifact semantic validation:
  `thm:finite-witness-manifest-record-interface`,
  `cor:artifact-semantic-validity-boundary`,
  `prop:artifact-validation-gate-unique-semantic-upgrade`.
- External archive equality, upload-time venue compliance, or venue acceptance:
  `thm:upload-or-archive-instantiation-boundary`,
  `cor:upload-or-archive-instantiation-record`,
  `thm:venue-rule-freshness-non-escalation`,
  `cor:upload-time-venue-compliance-record-requirement`.

## Naive Truncation Risks

The main risk is treating current-byte or post-inventory quantities as invariant
after edits.  The guard labels are `thm:current-byte-support-fixed-point-nonupgrade-boundary`,
`cor:post-inventory-rerun-closure`, `thm:current-inventory-rerun-exactness`,
`thm:post-inventory-package-fixed-point`,
`cor:manifest-required-theorem-inventory-fixed-point`,
`thm:accepted-inventory-coordinate-realization`,
`thm:finite-coordinate-determination-boundary`,
`thm:record-interface-rigidity`,
`thm:scope-contract-three-coordinate-boundary`, and
`thm:round-eight-ordered-support-tuple-closure`.

## Style Gaps

The compact public note should remain `submission_abstract.tex`; `main.tex` is a
technical supplement with a large theorem ledger.  A stricter journal route
would need a shorter theorem spine, proof closure for the five audit
propositions above, and fresh venue/bibliography checks at actual submission
time.
