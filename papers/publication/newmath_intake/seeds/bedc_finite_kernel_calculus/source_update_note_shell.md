# Source Update Note Shell: BEDC Finite Kernel Calculus

This note is an intake-only placeholder for a possible future source update.
It does not adopt a newer source commit, does not promote this seed, and does
not assert that a packaging theorem currently exists.

## Update Identity

- automath path:
  `papers/publication/newmath_intake/seeds/bedc_finite_kernel_calculus`
- source repo: `D:/omega/newmath`
- previous source ref: `origin/dev`
- previous source commit:
  `3fb3d6a0641767388a401883062aa522ea0b397b`
- observed local source ref: `auto-dev`
- observed local source commit:
  `dc06a0ecb02e586142dda3932749bcfe6fe3c9ba`
- update date: not adopted
- reviewer: pending

## Reason For Possible Update

The finite-kernel seed currently has a coherent theorem spine, but the spine is
too local for journal-style promotion.  A source update should be considered
only if a newer `D:/omega/newmath` snapshot adds or identifies a manuscript-scale
packaging theorem, for example:

```text
finite_kernel_interface_soundness
```

or a small theorem family such as:

```text
finite_syntax_certificate
extension_continuation_certificate
bundle_ask_interface_certificate
```

Without such a theorem or theorem family, the seed remains intake-only or a
modest short-note candidate under `short_note_route_memo.md`.

## Changed Source Paths

| Path | Previous role | New role | Required manuscript change |
|---|---|---|---|
| `lean4/BEDC/FKernel` | pinned source family for local constructor/equality/determinacy facts | pending packaging-theorem evidence | update `source_map.md`, `theorem_inventory.md`, and the promoted `THEOREM_LIST.md` only after adoption |
| `lean4/BEDC/GroundCompiler` | appendix/interface-only context | unchanged unless a source theorem explicitly uses it | keep out of the main theorem spine unless justified by exact statements |

## Changed Claims

| Claim | Status after update | Evidence |
|---|---|---|
| The selected finite-kernel declarations form a coherent theorem spine. | unchanged | `theorem_spine_selection.md`, `exact_statement_note.md`, `current_declaration_map.md` |
| The seed has a manuscript-scale packaging theorem suitable for journal-style promotion. | not adopted / unproven | requires exact source path, theorem statement, and source-side verification |
| GroundCompiler supplies the main finite-kernel theorem. | removed / forbidden | `groundcompiler_placement_decision.md` keeps it appendix/interface-only |

## Required Rechecks Before Adoption

- [ ] source paths exist at the new commit;
- [ ] exact packaging theorem name and statement are recorded;
- [ ] `lake build` succeeds in `D:/omega/newmath`;
- [ ] BEDC inventory command succeeds, if available;
- [ ] axiom-purity or equivalent trust check succeeds, if available;
- [ ] `theorem_inventory.md` is updated;
- [ ] `source_map.md` is updated only after this note is completed;
- [ ] `risk_register.md` is updated if any claim is weakened;
- [ ] `venue_ladder.md` is rechecked if the route changes;
- [ ] intake guard passes if this remains a seed.

## Decision

Current decision: keep the previous pinned source commit and park the update
until source-side packaging theorem work is complete.

