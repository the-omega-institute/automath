# Theorem Inventory: MetaCIC Closed-Normal Consistency

Promotion requires exact Lean declaration names and statement excerpts.

## Initial Targets

| Family | Source path | Paper role |
|---|---|---|
| Closed-normal consistency | `lean4/BEDC/MetaCIC/Consistency.lean` | Main theorem |
| No closed normal proof of false | `lean4/BEDC/MetaCIC/Consistency.lean` | Companion theorem |
| Beta preservation and conversion | `lean4/BEDC/MetaCIC/Beta/` | Reduction support |
| Closed term lemmas | `lean4/BEDC/MetaCIC/ClosedTerm/` | Closedness infrastructure |
| Confluence support | `lean4/BEDC/MetaCIC/Confluence/` | Reduction confluence support |
| Subject-reduction boundary | `lean4/BEDC/MetaCIC/SubjectReduction/` | Explicit hypotheses and limitations |

## Required Exactness Before Promotion

- Identify the exact Lean name used by the paper as the main theorem.
- Identify all assumptions in the theorem statement.
- Identify which dependent-codomain obligations remain structure fields or
  hypotheses rather than proved theorems.

