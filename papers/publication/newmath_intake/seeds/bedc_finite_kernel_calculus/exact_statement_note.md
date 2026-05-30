# Exact Statement Note: BEDC Finite Kernel Calculus

This is an intake-level note for the selected theorem spine.  It records the
actual Lean statement shape of the selected declarations from the pinned
newmath source snapshot.  It is not a promoted `THEOREM_LIST.md`.

- note date: 2026-05-31
- source repo: `D:/omega/newmath`
- source ref: `origin/dev`
- source commit: `3fb3d6a0641767388a401883062aa522ea0b397b`

## Exact Statement Summary

| Declaration | Exact statement shape | Manuscript consequence |
|---|---|---|
| `BMark` | Inductive type with constructors `b0` and `b1`. | Safe as primitive mark syntax. |
| `msame_iff_eq` | `msame m n ↔ m = n`. | `msame` is definitionally equality, not a new quotient relation. |
| `BMark_generated_cases` | Every `BMark` is `b0` or `b1`. | Supports finite-generation/no-hidden-mark wording. |
| `msame_no_confusion` | `msame .b0 .b1 -> False` and conversely. | Supports binary mark separation. |
| `BHist` | Inductive type with constructors `Empty`, `e0 h`, and `e1 h`. | Safe as primitive history syntax. |
| `hsame_iff_eq` | `hsame h k ↔ h = k`. | `hsame` is definitionally equality, not quotient equality. |
| `history_sameness_equivalence` | Packages reflexivity, symmetry, and transitivity of `hsame`. | Safe as equivalence discipline, but mathematically elementary. |
| `history_no_confusion` | Rules out `Empty` vs `e0`, `Empty` vs `e1`, `e0` vs `e1`, and `e1` vs `e0` under `hsame`. | Supports constructor separation for histories. |
| `Ext` | Inductive relation with constructors `Ext h .b0 (.e0 h)` and `Ext h .b1 (.e1 h)`. | One-step extension is exactly constructor extension. |
| `ext_total` | For every `h` and `m`, some `r` satisfies `Ext h m r`. | Safe as totality of one-step extension. |
| `ext_deterministic` | Two `Ext h m` results are `hsame`. | Safe as determinacy, but follows directly from constructors. |
| `ext_result_injective_pair` | A common extension result recovers `hsame h h'` and `msame m m'`. | Useful as the strongest local spine statement in the extension section. |
| `ext_constructor_characterization` | `Ext h m r` iff either `m=b0, r=e0 h` or `m=b1, r=e1 h`. | This is the cleanest local characterization theorem. |
| `append` | Recursive operation appending one `BHist` to another. | Defines continuation composition. |
| `Cont` | `Cont h k r := r = append h k`. | Relational continuation is definitionally append equality. |
| `cont_iff_append` | `Cont h k r <-> r = append h k`. | Shows `Cont` adds presentation, not extra structure. |
| `continuation_associativity` | If `Cont h k u`, `Cont u l v`, `Cont k l w`, and `Cont h w z`, then `hsame v z`. | Main local associativity result; still a direct append associativity consequence. |
| `ProbeBundle` | Inductive finite bundle with `Bnil` and `Bcons`. | Safe as finite bundle syntax. |
| `bundleAppend_assoc` | Associativity of `bundleAppend`. | Safe as bundle composition law. |
| `inBundle_bundleAppend_iff` | Membership in appended bundle iff membership in left or right. | Useful finite membership characterization. |
| `AskPolicy` | Structure with totality, deterministic answer, and history-respect fields. | Interface object, not a kernel theorem by itself. |
| `ask_total` | Extracts the totality field from an `AskPolicy`. | Interface projection, not independent theorem content. |
| `ask_deterministic` | Extracts deterministic answer behavior from an `AskPolicy`. | Interface projection, not independent theorem content. |
| `AskPolicy_iff_fields` | `AskPolicy D` iff the totality, determinacy, and history-respect fields hold. | Useful as a policy-field characterization. |

## Promotion Assessment

The selected spine is coherent and clean, but most statements are local
constructor, equality, determinacy, associativity, or field-projection facts.
On its current evidence, the paper should not be promoted as a major logic
contribution.  A strong promoted manuscript needs one of the following:

1. a new upstream packaging theorem that states the finite-kernel calculus as a
   single compositional interface theorem; or
2. a deliberately modest note framing the contribution as a formally checked
   finite syntax/interface spine, likely for a workshop or short note rather
   than a high-bar logic journal.

## Recommended Upstream Packaging Theorem

Before promotion, add or identify one theorem in `D:/omega/newmath` that
packages the spine into a single manuscript-level statement.  A suitable target
would combine:

- finite mark/history generation and no-confusion;
- extension totality, determinacy, and constructor characterization;
- continuation associativity;
- bundle append associativity and membership splitting;
- ask-policy field characterization.

The exact formulation should avoid claiming that BEDC replaces ordinary
foundations.  It should state that the selected declarations form a finite,
constructor-controlled relational interface for marks, histories, continuations,
bundles, and asking policies.

## Current Venue Consequence

Do not send this seed to APAL/LMCS/JAR/JFR yet.  The current spine is better
used as:

- supporting source material inside `bedc_automation_pipeline`; or
- a later short finite-calculus note after an upstream packaging theorem is
  available.
