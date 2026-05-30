# Scope Contract: BEDC Finite Kernel Calculus

## Paper Unit

This seed is an intake-stage candidate for a small formal-logic paper isolating
the BEDC finite kernel.  The paper unit is the finite calculus of marks,
histories, extension, continuation, bundles, asking policies, signatures,
packages, gap ledgers, and NameCert surfaces.  GroundCompiler material is
supporting evidence only when it clarifies the interface boundary.

## Central Claim

The central claim is that a finite kernel of mark/history constructors and
relation discipline supports a controlled naming and certificate surface without
treating ordinary mathematical objects as primitives.  The claim must be stated
as a bounded formal calculus result, not as a replacement foundation.

## In-Scope Formal Surfaces

| Surface | Pinned source path | Paper role |
|---|---|---|
| Mark constructors and sameness | `lean4/BEDC/FKernel/Mark.lean` | Two-mark base, equality discipline, no-confusion |
| History constructors and sameness | `lean4/BEDC/FKernel/Hist.lean` | Generated histories, equality discipline, constructor separation |
| Extension | `lean4/BEDC/FKernel/Ext.lean` | One-step relation, totality, determinacy, inversion |
| Continuation | `lean4/BEDC/FKernel/Cont.lean` | Append/continuation relation, cancellation, associativity |
| Bundle | `lean4/BEDC/FKernel/Bundle.lean` and submodules | Bundle generation, membership, append, cancellation |
| Ask | `lean4/BEDC/FKernel/Ask.lean` | Ask event and policy interface |
| Signature | `lean4/BEDC/FKernel/Sig.lean` and submodules | Signature relation, sameSig, generatedness |
| Package | `lean4/BEDC/FKernel/Package*.lean` | Package policy and token-policy boundary |
| Gap | `lean4/BEDC/FKernel/Gap*.lean` | Gap ledger, coverage, separation, globalize surface |
| NameCert | `lean4/BEDC/FKernel/NameCert*.lean` | Naming certificate descent and stability |
| GroundCompiler boundary | `lean4/BEDC/GroundCompiler/*.lean` | Encoding/reject interface, not the main finite-kernel theorem |

## Non-Claims

- The paper must not present BEDC as a complete replacement for set theory,
  type theory, or category theory.
- The paper must not use `Rule110` artifacts as proof of the finite-kernel
  calculus.
- The paper must not claim downstream concrete instances are mature.
- The paper must not cite family names when exact Lean declarations are needed.
- The paper must not merge the automation-pipeline paper or Rule110 artifact
  paper into this unit.

## Promotion Evidence Required

Promotion to an active paper requires:

1. A curated exact theorem inventory, not merely file-family names.
2. A paper outline showing which theorem families form the core calculus and
   which are supporting or excluded.
3. A non-claim registry explaining what ordinary mathematical structure is
   outside the finite kernel.
4. A related-work plan for finite calculi, formal systems, proof assistants,
   and naming/certificate interfaces.
5. A source snapshot note confirming the pinned `D:/omega/newmath` `origin/dev`
   commit `3fb3d6a0641767388a401883062aa522ea0b397b` or documenting a source
   update.

## Route

This seed is less suitable for immediate short-window submission than
`bedc_automation_pipeline` or `bedc_rule110_finite_witness`.  It should remain
intake-only until the theorem inventory is exact enough for a referee to see the
mathematical contribution without reading the whole Lean tree.
