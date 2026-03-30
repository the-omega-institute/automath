# Omega — Lean 4 Formalization Library

A zero-axiom Lean 4 library formalizing algebraic and combinatorial structures arising from the golden-mean shift and Zeckendorf representation.

## Build

```bash
lake build
```

Requires Lean 4 v4.28.0 (see `lean-toolchain`). Mathlib v4.28.0 is fetched automatically via `lake`.

## Local Automation

From `lean4/`, the repository now exposes lightweight local automation commands:

```bash
python scripts/omega_ci.py audit
python scripts/omega_ci.py inventory --strict
python scripts/omega_ci.py search "entropy log phi"
python scripts/omega_ci.py paper-coverage --sections body
python scripts/omega_ci.py paper-coverage --tex-root ../theory/publication/2026_scan_projection_address_semantics_sigma_nonexpansion_etds --paper-id E2
python scripts/omega_ci.py verify-files Omega/Core/Fib.lean
```

- `audit` is the executable zero-axiom gate: it fails on `sorry`, `admit`, raw `axiom` declarations, or paper-label doc blocks that are not attached to a declaration.
- `inventory` extracts Lean declarations plus attached paper labels into a machine-readable summary. Pass `--json <path>` to persist the report.
- `search` provides local declaration retrieval over the Lean inventory, useful for finding candidate lemmas or exact paper labels before writing a proof.
- `paper-coverage` scans theorem-like LaTeX environments in the paper and reconciles their `\label{...}` values against Lean registry labels, producing a coverage gap report.
  Pass `--tex-root <dir>` to scan an individual publication draft instead of the parent monograph, and `--gate-json <path>` to emit a compact machine-readable P6 gate artifact for that draft.
- `verify-files` gives a faster local loop than full `lake build` when you only need to check one or a few modules.

## Module Map

| Module | Files | Theorems | Description |
|--------|-------|----------|-------------|
| Core | 4 | ~25 | Fibonacci numbers, binary words, no-consecutive-1s constraint, coprime scalar multiplication |
| Folding | 38 | ~596 | Fold operator, stable values, fibers, moments, collisions, defects, carry, inverse limits |
| SPG | 5 | ~210 | Scan-projection generation: cylinders, prefix metric, clopen sets, scan error (discrete + measure) |
| Graph | 3 | ~37 | Labeled graphs, sofic shifts, transfer matrix (golden-mean adjacency, Perron-Frobenius) |
| Frontier | 5 | ~347 | Paper interface layer: assumptions, certificates, conditional theorems, conjectures |
| Combinatorics | 2 | ~510 | Path independent sets (Fibonacci counting), Fibonacci cubes |

**Total: ~2,350 theorems across 66 files, 0 axioms.**

## Key Results

### Arithmetic

- **Ring isomorphism** `stableValueRingEquiv : X m ≃+* ZMod (Nat.fib (m+2))` — stable types over m-bit words are isomorphic to cyclic rings
- **Fibonacci prime fields** `instFieldOfPrime` — when F_{m+2} is prime, X_m is a finite field GF(F_{m+2})
- **CRT decomposition** `crtDecomposition` — when F_{m+2} factors, X_m decomposes as a product ring

### Fiber Spectrum & Moments

- **S₂ recurrence** `momentSum_two_recurrence` — S₂(m+3) + 2·S₂(m) = 2·S₂(m+2) + 2·S₂(m+1), the first unconditional infinite-family recurrence
- **S₂ strict monotonicity** `momentSum_two_strict_mono'` — S₂(m) < S₂(m+1) for m ≥ 1
- **Fold congruence** `Fold_eq_iff_weight_mod` — Fold w = Fold w' iff weight w ≡ weight w' (mod F_{m+2})
- **Fiber multiplicity closed form** `fiberMultiplicity_allFalse_closed` — d(allFalse, m) = ⌊m/2⌋ + 1

### Dynamics & Topology

- **Topological entropy** `topological_entropy_eq_log_phi` — h_top = log φ for the golden-mean shift
- **Compact totally disconnected** `CompactSpace XInfinity`, `TotallyDisconnectedSpace XInfinity`
- **Unique fixed point** `shift_fixed_iff` — the shift map σ has exactly one fixed point (the all-false sequence)

## Lean → Paper Mapping

Selected correspondences between Lean theorems and paper labels:

| Lean theorem | Paper label | Statement |
|-------------|-------------|-----------|
| `stableValueRingEquiv` | `thm:finite-resolution-mod` | X_m ≃+* ZMod(F_{m+2}) |
| `instFieldOfPrime` | `cor:field-phase-fib-prime` | X_m is a field when F_{m+2} is prime |
| `momentSum_two_recurrence` | `prop:pom-s2-recurrence` | S₂ three-term recurrence |
| `topological_entropy_eq_log_phi` | `cor:folding-stable-syntax-entropy-logqdim` | h_top = log φ |
| `path_independent_set_count` | `thm:pom-max-fiber` (prerequisite) | pathIndCount(n) = fib(n+2) |
| `Fold_eq_iff_weight_mod` | `lem:pom-fold-congruence` | Fold equivalence via weight mod |
| `fiberMultiplicity_allFalse_closed` | `thm:pom-fiberMultiplicity-allFalse` | allFalse fiber closed form |

The full mapping is maintained in `Omega/Frontier/` via `SourceMap` annotations. See `IMPLEMENTATION_PLAN.md` for complete coverage data.

## Zero-Axiom Guarantee

This library introduces **no custom axioms**. Every theorem is proved from:
- Lean 4 core logic (Prop, Type, inductive types)
- Mathlib definitions and theorems

Verification now has two layers:
- `lake build` must complete successfully.
- `python scripts/omega_ci.py audit` must report no `sorry`, no `admit`, no raw `axiom` declarations, and no orphan paper-label blocks.

## Dependencies

- **Lean 4** v4.28.0
- **Mathlib** v4.28.0
