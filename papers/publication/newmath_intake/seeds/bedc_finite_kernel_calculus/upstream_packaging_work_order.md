# Upstream Packaging Work Order: BEDC Finite Kernel Calculus

This is an intake-level work order for future source-side work in
`D:/omega/newmath`.  It does not modify the source repo, does not promote this
seed, and must not be treated as a `THEOREM_LIST.md`.

- work order date: 2026-05-31
- automath seed:
  `papers/publication/newmath_intake/seeds/bedc_finite_kernel_calculus`
- source repo: `D:/omega/newmath`
- pinned source commit:
  `3fb3d6a0641767388a401883062aa522ea0b397b`

## Objective

Add or identify one manuscript-scale packaging theorem for the finite-kernel
calculus.  The current Lean spine is coherent but mostly local.  A standalone
logic paper needs a statement that packages the local declarations into a
finite, constructor-controlled interface.

## Preferred Source Location

Use one of these source-side locations, depending on the existing module
layout:

| Candidate path | Use when |
|---|---|
| `lean4/BEDC/FKernel/Interface.lean` | A file for interface-level packaging already exists or can be added without disrupting imports. |
| `lean4/BEDC/FKernel/Packaging.lean` | No interface file exists and a dedicated packaging file is cleaner. |
| `lean4/BEDC/FKernel.lean` or equivalent aggregator | The project already exposes FKernel through a central import file. |

Do not bury the package theorem in examples, GroundCompiler files, or dossier
prose.  It should live close to `Mark`, `Hist`, `Ext`, `Cont`, `Bundle`, and
`Ask`.

## Main Theorem Shape

Preferred Lean role name:

```text
finite_kernel_interface_soundness
```

The exact name may change, but the theorem should combine the following
already-audited declarations:

| Component | Source facts to package |
|---|---|
| finite syntax | `BMark`, `msame_iff_eq`, `BMark_generated_cases`, `msame_no_confusion`, `BHist`, `hsame_iff_eq`, `history_sameness_equivalence`, `history_no_confusion` |
| extension | `Ext`, `ext_total`, `ext_deterministic`, `ext_result_injective_pair`, `ext_constructor_characterization` |
| continuation | `append`, `Cont`, `cont_iff_append`, `continuation_associativity` |
| bundles | `ProbeBundle`, `bundleAppend_assoc`, `inBundle_bundleAppend_iff` |
| ask policies | `AskPolicy`, `ask_total`, `ask_deterministic`, `AskPolicy_iff_fields` |

An acceptable theorem can return a bundled conjunction, a structure instance,
or a small certificate object.  The manuscript only needs one clean statement
that can be quoted as the finite-kernel interface theorem.

## Acceptable Split Form

If one theorem becomes unwieldy, use three packaged theorem roles:

```text
finite_syntax_certificate
extension_continuation_certificate
bundle_ask_interface_certificate
```

Then add one lightweight theorem or definition that names the combined package,
so a manuscript can cite a single interface result rather than a list of local
lemmas.

## Acceptance Criteria

Source-side work is acceptable for promotion only when all criteria below are
met:

- the theorem or theorem family compiles in the pinned or explicitly updated
  `newmath` source snapshot;
- its statement mentions the finite-kernel interface, not merely one local
  constructor fact;
- it depends only on the intended finite-kernel declarations or documented
  imports;
- any axioms, partial proof markers, or trusted escapes are recorded;
- automath intake is updated with exact source path, theorem name, and exact
  statement summary;
- the promoted manuscript can quote it without claiming semantic completeness
  or foundation replacement.

## Non-Goals

Do not use this work order to:

- add broad manifesto claims about BEDC as a replacement foundation;
- move GroundCompiler implementation facts into the main finite-kernel theorem;
- inflate theorem counts with parameter-echo or shallow restatements;
- introduce examples as if they were part of the primitive kernel;
- create an automath `2026_*` paper track before human promotion.

## Verification Commands After Source Work

Run these from the source workspace after the theorem is added or identified:

```powershell
cd D:\omega\newmath\lean4
lake build
cd D:\omega\newmath
python lean4\scripts\bedc_ci.py inventory
python lean4\scripts\bedc_ci.py axiom-purity --strict
```

After the source commands pass or fail, update this seed with a source update
note recording:

- old source commit and new source commit;
- exact theorem path and name;
- exact statement summary;
- command outputs or failure reasons;
- whether the seed is still journal-bound or only suitable for a short note.
