# Source Map: MetaCIC Closed-Normal Consistency

| Role | Path | Notes |
|---|---|---|
| public summary | `docs/dossier/metacic-first-main-result.qmd` | Main result and limitation statement |
| Lean source | `lean4/BEDC/MetaCIC/` | Formal syntax, typing, substitution, beta, consistency |
| consistency theorem | `lean4/BEDC/MetaCIC/Consistency.lean` | Target family including closed-normal result |
| subject reduction | `lean4/BEDC/MetaCIC/SubjectReduction/` | Boundary hypotheses and discharge modules |
| confluence | `lean4/BEDC/MetaCIC/Confluence/` | Beta/confluence support |
| normalization | `lean4/BEDC/MetaCIC/Normalization/` | Strong-normalization-related support |
| audit script | `lean4/scripts/bedc_ci.py` | `metacic-purity` and `axiom-purity` commands |

## Verification Commands

```bash
cd D:/omega/newmath/lean4 && lake build
cd D:/omega/newmath && python3 lean4/scripts/bedc_ci.py metacic-purity --strict
cd D:/omega/newmath && python3 lean4/scripts/bedc_ci.py axiom-purity --strict
```

