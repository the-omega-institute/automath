# Current Declaration Map: BEDC Finite Kernel Calculus

This is an intake-level read-only source map for the local `D:/omega/newmath`
checkout.  It does not promote the seed, does not modify the source repo, and
must not be treated as a promoted `THEOREM_LIST.md`.

## Snapshot Warning

- intake pinned commit: `3fb3d6a0641767388a401883062aa522ea0b397b`
- local source HEAD observed during this pass:
  `dc06a0ecb02e586142dda3932749bcfe6fe3c9ba`
- local source branch/status observed: `auto-dev...origin/auto-dev`

The declaration locations below are useful for planning, but they do not
replace the pinned source evidence.  If this newer local source snapshot is
used for a promoted manuscript, first add a source update note using
`../../SOURCE_UPDATE_NOTE_TEMPLATE.md`.

## Exact-Name Declaration Locations

The following names were found by exact-name search in the current local source
tree under `D:/omega/newmath/lean4/BEDC/FKernel`.

| Role | Declaration | Current local path and line |
|---|---|---|
| primitive mark syntax | `BMark` | `Mark.lean:4` |
| mark equality discipline | `msame_iff_eq` | `Mark.lean:11` |
| mark generation | `BMark_generated_cases` | `Mark.lean:23` |
| mark no-confusion | `msame_no_confusion` | `Mark.lean:68` |
| primitive history syntax | `BHist` | `Hist.lean:8` |
| history equality discipline | `hsame_iff_eq` | `Hist.lean:16` |
| history equivalence | `history_sameness_equivalence` | `Hist.lean:64` |
| history no-confusion | `history_no_confusion` | `Hist.lean:256` |
| extension relation | `Ext` | `Ext.lean:10` |
| extension totality | `ext_total` | `Ext.lean:20` |
| extension determinacy | `ext_deterministic` | `Ext.lean:26` |
| extension injectivity | `ext_result_injective_pair` | `Ext.lean:51` |
| extension characterization | `ext_constructor_characterization` | `Ext.lean:117` |
| continuation operation | `append` | `Cont.lean:8` |
| continuation relation | `Cont` | `Cont.lean:65` |
| continuation equivalence | `cont_iff_append` | `Cont.lean:70` |
| continuation associativity | `continuation_associativity` | `Cont.lean:540` |
| bundle syntax | `ProbeBundle` | `Bundle.lean:4` |
| bundle append associativity | `bundleAppend_assoc` | `Bundle.lean:51` |
| bundle membership split | `inBundle_bundleAppend_iff` | `Bundle.lean:173` |
| ask interface | `AskPolicy` | `Ask.lean:71` |
| ask totality | `ask_total` | `Ask.lean:350` |
| ask determinacy | `ask_deterministic` | `Ask.lean:356` |
| ask field characterization | `AskPolicy_iff_fields` | `Ask.lean:471` |

## Pinned Origin/Dev Exact-Name Expansion

The pinned `origin/dev` source contains additional exact declarations that
should be mined before any claim that this seed lacks content.  These names are
still intake-level evidence; a promoted manuscript must read exact statements
before quoting them.

| Source file | Exact declarations now available for manuscript selection |
|---|---|
| `lean4/BEDC/FKernel/Sig.lean` | `SigRel`, `sig_empty_constructor`, `sig_cons_constructor`, `sig_cons_inversion`, `sig_cons_head_mark_determinacy`, `sig_cons_head_marks_same`, `sig_cons_result_inversion`, `sameSig_intro_from_witnesses`, `sameSig_witnesses`, `sameSig_refl`, `sameSig_symm`, `sameSig_trans`, `sameSig_equivalence`, `signature_sameness_equivalence_policy_spine`, `sameSig_equivalence_under_policy` |
| `lean4/BEDC/FKernel/Package/Core.lean` | `PkgSig`, `PkgSig_iff_TokIntro`, `TokIntro_nonempty_pkg`, `psame`, `ConcretePackageSamenessPolicy_holds`, `psame_reflection_witness_chain_under_tok_unique`, `psame_iff_hsame_under_tok_unique`, `concrete_package_equivalence_signature_grounded`, `signature_package_relation_generated_only` |
| `lean4/BEDC/FKernel/NameCert.lean` | `NameCert`, `SemanticNameCert`, `NameCert_carrier_self_semantic_lifting`, `semanticNameCert_ledger_policy_witness`, `semanticNameCert_pattern_ledger_witness`, `semanticNameCert_classifier_chain_transport`, `NameCert_iff_semantic_fields`, `derived_interfaces_require_certificates`, `SealEvent`, `SealInterface`, `DescentCertificate`, `StableTransformation`, `stableTransformation_descends_to_packages`, `function_like_interfaces_require_descent` |
| `lean4/BEDC/GroundCompiler/MainTheorems.lean` | `NoHiddenInputCompilerState`, `canonical_no_hidden_input_compiler_state`, `no_hidden_input`, `channel_bijection`, `channel_code_lossless`, `code_not_proof`, `source_channel_separation`, `carry_not_channel_rewrite`, `structure_emergence`, `yaml_ast_output_only`, `recognizer_generatedness`, `self_hosting_removes_hidden_compiler`, `accepted_export`, `code_existence_not_export`, `motif_existence_not_export`, `theorem_code_bijection`, `proposition_not_theorem_code`, `theorem_code_not_proof`, `chapter_code_bijection`, `topic_not_chapter_code`, `classifier_quotient_many_to_one`, `normal_address_requires_ledger`, `declared_bootstrap_boundary`, `motif_analysis`, `metric_conservativity`, `similarity_not_identity`, `cannot_claim_registry_mandatory`, `global_conservativity`, `compiler_layer_address_analysis_layer`, `no_hidden_input_streaming_compiler` |
| `lean4/BEDC/GroundCompiler/ChannelEncoding.lean` | `BodyEncoding`, `EventTerminator`, `EventEncoding`, `FlowEncoding`, `LegalEvent`, `LegalZStream`, `Decode`, `NoAdjacentOneOne`, `body_encoding_no_adjacent_11`, `first_11_is_terminator`, `flow_encoding_legal_zstream`, `flow_encoding_not_single_one`, `channel_encoding_0111_illegal`, `event_level_round_trip`, `decode_fuel_flow_encoding`, `flow_level_round_trip`, `compiles_functional`, `encoder_streaming`, `decoder_streaming_one_glyph_lookahead`, `no_tree_no_manifest_no_table`, `legal_stream_not_theoremhood`, `legal_stream_completeness`, `channel_encoding_bijection`, `prototype_roundtrip_correctness`, `channel_conservativity` |
| `lean4/BEDC/GroundCompiler/MinimalPrototype.lean` | `RejectReason`, `RequiredUnitTestVectors`, `RequiredRejectTestVectors`, `RoundTripTestSuite`, `PrototypeStreamDecoder`, `DecodeStatus`, `PrototypeAuditChecklist`, `P0ChannelObligations`, `P0Adequate`, `HigherPrototypeAdequacy`, `reference_prototype_not_full_compiler`, `prototype_encoder_soundness`, `prototype_decoder_soundness`, `prototype_decoder_completeness_on_legal_streams`, `prototype_reject_soundness`, `p0_channel_obligations_hold`, `prototype_audit_suffices`, `p0_adequacy_not_higher`, `reference_prototype_not_higher_adequacy`, `reference_prototype_conservative_over_kernel`, `reference_prototype_address_layer`, `prototype_output_not_namecert`, `prototype_output_not_theorem`, `prototype_output_not_accepted` |

## Stronger Manuscript Split Now Available

The seed should no longer be treated as a flat list of local constructor facts.
The pinned declarations support three possible manuscript spines:

| Spine | Core declarations | Route consequence |
|---|---|---|
| finite syntax and extension calculus | `BMark`, `BHist`, `Ext`, `Cont`, `ProbeBundle`, `AskPolicy` families | modest short-note route; least source-side work |
| finite kernel interface with signatures and packages | core spine plus `SigRel`, `sameSig_*`, `PkgSig`, `psame_*` | stronger logic paper if packaged by a new interface theorem |
| certificate and compiler boundary | `NameCert`, `StableTransformation`, `GroundCompiler/*` conservativity and channel declarations | appendix or separate systems/formal-methods route unless tied to the finite-kernel theorem |

## Packaging Gap

No packaging theorem was added by this intake pass.  The current evidence still
supports the prior assessment:

- the selected spine is coherent;
- the content base extends beyond local constructor facts into signature,
  package, certificate, and compiler-boundary surfaces;
- a journal-style finite-kernel paper still needs an upstream packaging theorem
  or theorem family before promotion.

The preferred source-side target remains:

```text
finite_kernel_interface_soundness
```

or the split form:

```text
finite_syntax_certificate
extension_continuation_certificate
bundle_ask_interface_certificate
```

## Automath-Only Next Work

Without editing `D:/omega/newmath`, agents may still:

- refine the manuscript role table using the declaration locations above;
- use `source_update_note_shell.md` if the local `dc06a0...` snapshot should
  replace the pinned `3fb3d6...` snapshot later;
- decide whether GroundCompiler belongs only in an appendix/interface note.

Agents must not claim that the packaging theorem exists until it is added or
identified in the source tree and the source update is recorded.
