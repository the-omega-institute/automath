# Declaration Inventory Seed: BEDC Finite Kernel Calculus

This is a seed-level inventory extracted from the pinned newmath source
snapshot `origin/dev` commit `3fb3d6a0641767388a401883062aa522ea0b397b`.
It is not yet the final theorem list for a promoted paper.  Promotion requires
selecting a smaller spine and checking the exact statements.

## Core FKernel Spine

| Role | Source file | Candidate declarations |
|---|---|---|
| Mark constructors | `FKernel/Mark.lean` | `BMark`, `msame`, `msame_iff_eq`, `msame_refl`, `msame_generated_rules`, `BMark_generated_cases` |
| History constructors | `FKernel/Hist.lean` | `BHist`, `hsame`, `hsame_iff_eq`, `hsame_refl`, `hsame_symm`, `hsame_trans`, `hsame_equivalence`, `history_sameness_equivalence`, `hsame_no_confusion`, `history_no_confusion` |
| Extension relation | `FKernel/Ext.lean` | `Ext`, `ext_generation_rules`, `ext_total`, `ext_deterministic`, `ext_result_injective_pair`, `ext_constructor_inversion`, `ext_constructor_characterization`, `ext_result_for_mark` |
| Continuation relation | `FKernel/Cont.lean` | `append`, `Cont`, `cont_intro`, `cont_iff_append`, `append_assoc`, `append_right_cancel`, `append_left_cancel`, `cont_deterministic`, `cont_assoc_primary`, `continuation_associativity` |
| Bundle calculus | `FKernel/Bundle.lean` | `ProbeBundle`, `InBundle`, `bundleAppend`, `bundleLength`, `bundleLength_append`, `bundleAppend_assoc`, `inBundle_bundleAppend_iff`, `bundle_generation_cases`, `probeBundle_no_confusion_all` |
| Ask interface | `FKernel/Ask.lean` | `AskSetup`, `AskEvent`, `askEvent_components`, `AskEvent_iff_exists`, `AskPolicy`, `BundleAskPolicy`, `ask_total`, `ask_deterministic`, `asking_determinacy`, `AskPolicy_iff_fields` |

## Secondary FKernel Surfaces to Curate

| Surface | Source files | Promotion task |
|---|---|---|
| Signature and sameSig | `FKernel/Sig*.lean` | Select the exact `SigRel`/`sameSig` generatedness and equivalence spine |
| Package policy | `FKernel/Package*.lean` | Separate package policy from token-policy examples |
| Gap ledger | `FKernel/Gap*.lean` | Decide whether globalize/completeness is core or a later paper |
| NameCert | `FKernel/NameCert*.lean` | Select descent/stability statements that support naming certificates |
| Unary and external binary | `FKernel/Unary*.lean`, `FKernel/ExternalBinary*.lean` | Treat as examples unless the paper needs them for calculus closure |
| Settled | `FKernel/Settled.lean` | Decide whether settledness is core calculus or interface layer |

## GroundCompiler Boundary Declarations

The GroundCompiler material should be used only to define the interface between
the finite kernel and executable/certificate surfaces.  Candidate boundary
declarations include:

| Source file | Candidate declarations | Boundary role |
|---|---|---|
| `GroundCompiler/ChannelEncoding.lean` | `EventEncoding`, `FlowEncoding`, `Decode`, `event_level_round_trip`, `flow_level_round_trip`, `channel_encoding_bijection`, `legal_stream_not_theoremhood` | Encoding and decoding are not proofhood |
| `GroundCompiler/MainTheorems.lean` | `no_hidden_input`, `channel_bijection`, `code_not_proof`, `source_channel_separation`, `theorem_code_not_proof`, `cannot_claim_registry_mandatory`, `global_conservativity` | Non-claim and boundary registry |
| `GroundCompiler/MinimalPrototype.lean` | `PrototypeLevel`, `RejectReason`, `prototype_encoder_soundness`, `prototype_decoder_soundness`, `prototype_reject_soundness`, `reference_prototype_not_full_compiler`, `prototype_output_not_theorem` | Prototype adequacy and reject taxonomy |
| `GroundCompiler/ImplementationInterface.lean` | `ImplementationSoundness`, `ImplementationCompleteness`, `NoHostLeakCondition`, `dec_event_sound`, `decode_sound`, `decoder_functional`, `encoder_totality_obligation` | Interface obligations, not kernel primitives |

## Promotion Tasks

- Reduce this seed inventory to a manuscript theorem spine of roughly 12-25
  exact declarations.
- Categorize each declaration as `checked theorem`, `definition`, `interface
  obligation`, `example`, or `excluded`.
- Confirm every included target exists at the source commit used by the
  promoted paper.
- Link each target to a paper section before creating `THEOREM_LIST.md`.
