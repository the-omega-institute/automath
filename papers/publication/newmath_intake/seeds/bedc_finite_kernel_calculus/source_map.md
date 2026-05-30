# Source Map: BEDC Finite Kernel Calculus

| Role | Path | Notes |
|---|---|---|
| Lean kernel | `lean4/BEDC/FKernel/` | Primary formal source |
| compiler/certificate surface | `lean4/BEDC/GroundCompiler/` | Encoding and reject reasons |
| finite-kernel paper source | `papers/bedc/parts/finite_kernel_theory/` | Paper-side theory source if present |
| proof obligations | `papers/bedc/parts/proof_obligations/` | Scope and verification discipline |
| concrete instances | `papers/bedc/parts/concrete_instances/` | Evidence only, not main scope |
| dossier framing | `docs/dossier/distinction-as-foundation.qmd` | Expository background |
| audit framing | `docs/dossier/zero-information-debt.qmd` | Non-claim and audit discipline |

## Verification Commands

```bash
cd D:/omega/newmath/lean4 && lake build
cd D:/omega/newmath && python3 tools/check-axioms.py
cd D:/omega/newmath && python3 lean4/scripts/bedc_ci.py audit
cd D:/omega/newmath && python3 lean4/scripts/bedc_ci.py axiom-purity --strict
```

