# Source Map: BEDC Rule 110 Finite Witness Artifacts

| Role | Path | Notes |
|---|---|---|
| artifact overview | `rule110/README.md` | Trust chain and reproducibility commands |
| artifact status | `rule110/STATUS.md` | Counts, coverage, and verification snapshot |
| evaluator | `rule110/evaluator/` | Rule 110 and cyclic-tag executable substrate |
| encoder | `rule110/encoder/` | GroundCompiler and Cook/Rule110 lowering surface |
| manifests | `rule110/manifests/` | Source and generated witness assertions |
| tests | `rule110/tests/` | Test binaries and audit checks |
| documentation | `rule110/docs/` | Manifest format, theorem encoding, Cook data |
| design boundary | `docs/superpowers/specs/2026-05-13-rule110-roadmap-rewrite-design.md` | Finite witness vs universal limitation |
| Lean source | `lean4/BEDC/FKernel/` | Source theorem families mirrored by manifests |
| compiler source | `lean4/BEDC/GroundCompiler/` | Encoding and reject reason source |

## Verification Commands

```bash
cd D:/omega/newmath/rule110 && make clean && make && make test
cd D:/omega/newmath/rule110 && make test-collision-audit
cd D:/omega/newmath/rule110 && make test-scale
```

