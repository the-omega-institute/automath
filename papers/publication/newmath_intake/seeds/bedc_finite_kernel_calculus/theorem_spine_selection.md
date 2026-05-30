# Theorem Spine Selection: BEDC Finite Kernel Calculus

This is an intake-level manuscript spine, not a promoted `THEOREM_LIST.md`.
It selects a small set of exact Lean declarations from the pinned newmath
snapshot:

- source ref: `D:/omega/newmath` `origin/dev`
- source commit: `3fb3d6a0641767388a401883062aa522ea0b397b`
- verification date: 2026-05-31

The selected declarations were checked by exact-name grep against the pinned
source for the listed core files.  Promotion still requires reading the exact
statement of each selected declaration before it is quoted in a manuscript.

## Proposed Manuscript Spine

| Paper role | Declaration | Source file | Status | Manuscript use |
|---|---|---|---|---|
| Primitive alphabet | `BMark` | `lean4/BEDC/FKernel/Mark.lean` | definition | Defines the two primitive mark constructors. |
| Mark equality discipline | `msame_iff_eq` | `lean4/BEDC/FKernel/Mark.lean` | checked theorem | Connects generated mark sameness to Lean equality. |
| Mark generation | `BMark_generated_cases` | `lean4/BEDC/FKernel/Mark.lean` | checked theorem | Shows there are no hidden mark constructors. |
| Mark separation | `msame_no_confusion` | `lean4/BEDC/FKernel/Mark.lean` | checked theorem | Provides the primitive no-confusion boundary for marks. |
| History alphabet | `BHist` | `lean4/BEDC/FKernel/Hist.lean` | definition | Defines empty and marked history constructors. |
| History equality discipline | `hsame_iff_eq` | `lean4/BEDC/FKernel/Hist.lean` | checked theorem | Connects generated history sameness to Lean equality. |
| History equivalence | `history_sameness_equivalence` | `lean4/BEDC/FKernel/Hist.lean` | checked theorem | Packages reflexivity, symmetry, and transitivity for history sameness. |
| History separation | `history_no_confusion` | `lean4/BEDC/FKernel/Hist.lean` | checked theorem | Gives constructor-level no-confusion for histories. |
| Extension relation | `Ext` | `lean4/BEDC/FKernel/Ext.lean` | definition | Introduces one-step mark extension as a relation. |
| Extension totality | `ext_total` | `lean4/BEDC/FKernel/Ext.lean` | checked theorem | Establishes that every history and mark admits an extension result. |
| Extension determinacy | `ext_deterministic` | `lean4/BEDC/FKernel/Ext.lean` | checked theorem | Shows one-step extension has a unique result. |
| Extension injectivity | `ext_result_injective_pair` | `lean4/BEDC/FKernel/Ext.lean` | checked theorem | Recovers source and mark data from a common extension result. |
| Extension characterization | `ext_constructor_characterization` | `lean4/BEDC/FKernel/Ext.lean` | checked theorem | Converts relational extension into constructor cases. |
| Continuation operation | `append` | `lean4/BEDC/FKernel/Cont.lean` | definition | Provides the recursive operation underlying continuation. |
| Continuation relation | `Cont` | `lean4/BEDC/FKernel/Cont.lean` | definition | Presents continuation relationally rather than as an external process. |
| Continuation equivalence | `cont_iff_append` | `lean4/BEDC/FKernel/Cont.lean` | checked theorem | Identifies the relational and recursive formulations. |
| Continuation associativity | `continuation_associativity` | `lean4/BEDC/FKernel/Cont.lean` | checked theorem | Supplies the main compositional law for histories. |
| Bundle type | `ProbeBundle` | `lean4/BEDC/FKernel/Bundle.lean` | definition | Defines finite probe bundles. |
| Bundle append associativity | `bundleAppend_assoc` | `lean4/BEDC/FKernel/Bundle.lean` | checked theorem | Gives the structural law for bundle composition. |
| Bundle membership split | `inBundle_bundleAppend_iff` | `lean4/BEDC/FKernel/Bundle.lean` | checked theorem | Characterizes membership through bundle append. |
| Ask interface | `AskPolicy` | `lean4/BEDC/FKernel/Ask.lean` | definition | Introduces the policy object for admissible asking events. |
| Ask totality | `ask_total` | `lean4/BEDC/FKernel/Ask.lean` | checked theorem | States total availability of ask events under a policy. |
| Ask determinacy | `ask_deterministic` | `lean4/BEDC/FKernel/Ask.lean` | checked theorem | States deterministic behavior of ask events under a policy. |
| Ask field characterization | `AskPolicy_iff_fields` | `lean4/BEDC/FKernel/Ask.lean` | checked theorem | Packages the policy interface into explicit fields. |

## Section Plan

1. Primitive finite syntax:
   `BMark`, `BHist`, generated sameness, and no-confusion.
2. Relational extension:
   `Ext`, totality, determinacy, injectivity, and constructor
   characterization.
3. Continuation calculus:
   `append`, `Cont`, relational equivalence, and associativity.
4. Finite bundles and asking:
   `ProbeBundle`, bundle append/membership, `AskPolicy`, totality, and
   determinacy.

## Deferred or Excluded From the Core Spine

| Surface | Decision | Reason |
|---|---|---|
| Signature and `sameSig` files | deferred | Important but not yet exact-name audited for this spine.  Promote only after a second exact-source pass. |
| Package policy files | deferred | Better used as a later section or example unless it is needed for the main finite-kernel theorem. |
| Gap ledger files | deferred | Risk of overclaiming completeness; keep out of the first manuscript spine. |
| NameCert files | deferred | Potentially strong, but should not be cited until the exact certificate descent/stability statements are selected. |
| Unary and external binary examples | example only | Useful illustrations, not needed for the first finite-kernel core theorem. |
| GroundCompiler declarations | interface/appendix only | They state encoding and implementation boundaries, not primitive kernel calculus. |

## Promotion Gate

Before this seed can be promoted, the next pass must:

- inspect the exact statement of every selected declaration;
- decide whether the paper's main theorem is a packaged consequence of this
  spine or whether one new packaging theorem must be added upstream in
  `D:/omega/newmath`;
- add a compact non-claim registry to prevent ordinary mathematical
  interpretation layers from being presented as finite-kernel primitives;
- re-check venue fit after the spine is frozen.
