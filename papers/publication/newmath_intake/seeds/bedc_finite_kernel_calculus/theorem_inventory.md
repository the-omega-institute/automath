# Theorem Inventory: BEDC Finite Kernel Calculus

This file is an intake-level inventory. Promotion requires replacing these
families with exact Lean declaration names and paper labels.

## Families to Extract

| Family | Source path | Intended paper role |
|---|---|---|
| Mark sameness | `lean4/BEDC/FKernel/Mark.lean` | Base equivalence and no-confusion |
| History sameness | `lean4/BEDC/FKernel/Hist*.lean` | Generated history equality discipline |
| Extension | `lean4/BEDC/FKernel/Ext*.lean` | Relation-based extension |
| Continuation | `lean4/BEDC/FKernel/Cont*.lean` | Local transition and route semantics |
| Ask | `lean4/BEDC/FKernel/Ask*.lean` | Asking-event interface |
| Bundle | `lean4/BEDC/FKernel/Bundle*.lean` | Generated bundle surface |
| Signature | `lean4/BEDC/FKernel/Sig*.lean` | Signature relation and sameSig |
| Package | `lean4/BEDC/FKernel/Package*.lean` | Package policy |
| Gap | `lean4/BEDC/FKernel/Gap*.lean` | Gap ledger and non-escape surface |
| NameCert | `lean4/BEDC/FKernel/NameCert*.lean` | Naming certificate interface |
| GroundCompiler | `lean4/BEDC/GroundCompiler/` | Encoding and reject taxonomy |

## Required Exactness Before Promotion

- Each row must include exact Lean target names.
- Each theorem used in a submitted manuscript must be categorized as checked,
  definition-only, statement-only, or paper-only.
- The manuscript must not cite a family name when an exact theorem target is
  needed.

## Exact-Name Seed

See `declaration_inventory_seed.md` for the first exact-name extraction from
the pinned source.  That file is still broader than a manuscript theorem list;
promotion requires selecting a small theorem spine and excluding example or
interface-only declarations.
