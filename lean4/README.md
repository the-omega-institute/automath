# Omega — Lean 4 Formalization Library

A zero-axiom Lean 4 library formalizing algebraic and combinatorial structures arising from the golden-mean shift and Zeckendorf representation.

## Build

```bash
lake build
```

Requires Lean 4 v4.28.0 (see `lean-toolchain`). Mathlib v4.28.0 is fetched automatically via `lake`.

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

Verification: `lake build` must complete with no `sorry`, no `admit`, no `axiom` declarations outside of Lean/Mathlib core.

## Dependencies

- **Lean 4** v4.28.0
- **Mathlib** v4.28.0
