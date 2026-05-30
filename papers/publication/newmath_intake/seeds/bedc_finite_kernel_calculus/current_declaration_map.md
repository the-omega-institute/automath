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

## Packaging Gap

No packaging theorem was added by this intake pass.  The current evidence still
supports the prior assessment:

- the selected spine is coherent;
- most statements are local constructor, equality, determinacy, associativity,
  or field-projection facts;
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
- draft a source update note shell if the local `dc06a0...` snapshot should
  replace the pinned `3fb3d6...` snapshot later;
- decide whether GroundCompiler belongs only in an appendix/interface note.

Agents must not claim that the packaging theorem exists until it is added or
identified in the source tree and the source update is recorded.
