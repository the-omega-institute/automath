# Source Pin Status: Newmath Intake

This note records the current source-pin decision for the newmath-derived
intake seeds. It is intake-only and does not promote any seed into an active
paper track.

- intake root: `papers/publication/newmath_intake`
- source repo: `D:/omega/newmath`
- pinned source ref for current intake: `origin/dev`
- pinned source commit:
  `3fb3d6a0641767388a401883062aa522ea0b397b`
- checked date: 2026-05-31

## Current Local Source Drift

At the latest check, `D:/omega/newmath` was on local branch `auto-dev` with
working-tree `HEAD`:

```text
dc06a0ecb02e586142dda3932749bcfe6fe3c9ba
```

The intake does not adopt that local `HEAD`.  The authoritative source for the
current P0 seed packets remains the pinned `origin/dev` commit listed above.

## Path Existence Recheck

The following representative source-map paths were rechecked at the pinned
`origin/dev` ref and were present:

| Seed | Representative pinned paths checked |
|---|---|
| `bedc_automation_pipeline` | `lean4/scripts/bedc_ci.py`; `papers/bedc/scripts/codex_revise.py` |
| `bedc_finite_kernel_calculus` | `lean4/BEDC/FKernel`; `lean4/BEDC/GroundCompiler` |
| `bedc_rule110_finite_witness` | `rule110/STATUS.md`; `lean4/BEDC/FKernel`; `lean4/BEDC/GroundCompiler` |

This is a path-existence check only. It is not a proof that the verification
commands pass, and it does not replace the route-specific gates recorded in
`P0_GATE_AUDIT.md`.

## Decision

Keep the existing pinned source commit for all current newmath intake seeds.
If a seed needs newer source-side evidence, copy
`SOURCE_UPDATE_NOTE_TEMPLATE.md` into the relevant seed under a descriptive
name and record the old commit, new commit, changed paths, changed claims, and
required rechecks before editing that seed's source map.
