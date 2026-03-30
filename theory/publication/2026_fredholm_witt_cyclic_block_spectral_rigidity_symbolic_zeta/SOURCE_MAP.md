# SOURCE_MAP

Paper: *Fredholm determinants, cyclic-block realisations, and spectral rigidity for symbolic zeta-functions*

## File inventory

| File | Lines | Role |
|------|-------|------|
| `main.tex` | 88 | Master document, preamble, macros |
| `sec_introduction.tex` | 140 | Introduction, main-result statements, prior work |
| `sec_preliminaries.tex` | 179 | Finite-state zeta, primitive orbits, finite-part constants |
| `sec_fredholm.tex` | 175 | Fredholm--Witt bridge, cyclic-block realisation, spectral rigidity |
| `sec_perturbation.tex` | 163 | Perturbative applications (gradient formula, CLT) |
| `sec_conclusion.tex` | 16 | Concluding remarks |
| `references.bib` | 250 | Bibliography (25 entries) |

---

## sec_introduction.tex

| Label | Type | Deps |
|-------|------|------|
| `sec:introduction` | section | -- |
| `thm:intro-fredholm-rigidity` | theorem | Collects (i)--(iii); forward-references `thm:fredholm-witt-bridge`, `thm:cyclic-fredholm-realisation`, `thm:fredholm-spectral-rigidity` |
| `thm:intro-perturbative-applications` | theorem | Collects (i)--(ii); forward-references `thm:finite-part-reduced-determinant-group-inverse-gradient`, `thm:logM-holomorphic-variation`, `thm:clt-spectral` |

## sec_preliminaries.tex

| Label | Type | Deps |
|-------|------|------|
| `sec:preliminaries` | section | -- |
| `eq:primitive-mobius` | equation | Mobius function, `a_n(A)` definition |
| `eq:trace-primitive-identity` | equation | Inverse of `eq:primitive-mobius` |
| `prop:prelim-trace-primitive` | proposition | `eq:trace-primitive-identity` |
| `lem:primitive-orbit-asymptotic` | lemma | Perron--Frobenius theory (external) |
| `eq:residue-constant-def` | equation | Definition of `C(A)` |
| `eq:reduced-det-poly` | equation | Reduced determinant polynomial `F_A(t)` |
| `eq:reduced-det-constant` | equation | `C(A) = F_A(1)^{-1}` |
| `def:abel-finite-part` | definition | Abel finite-part constant `log M(A)` |
| `thm:finite-part-primitive-closed-form` | theorem | `prop:prelim-trace-primitive`, `eq:reduced-det-constant` |
| `rem:finite-state-arithmetic` | remark | -- |

## sec_fredholm.tex

| Label | Type | Deps |
|-------|------|------|
| `sec:fredholm` | section | -- |
| `thm:fredholm-witt-bridge` | theorem | Standard Fredholm determinant identity (Simon), Mobius inversion |
| `rem:witt-audit-constraints` | remark | `thm:fredholm-witt-bridge`, `rem:finite-state-arithmetic` |
| `eq:cycle-block-det` | equation | Eigenvalue computation for cyclic permutation |
| `thm:cyclic-fredholm-realisation` | theorem | `eq:cycle-block-det`, trace-class norm estimate |
| `cor:finite-rank-realisation` | corollary | `thm:cyclic-fredholm-realisation` (finite J case) |
| `thm:fredholm-spectral-rigidity` | theorem | Simon product representation [Chapter 3], Mobius inversion |
| `cor:realisability-vs-rigidity` | corollary | `thm:fredholm-spectral-rigidity` |

## sec_perturbation.tex

| Label | Type | Deps |
|-------|------|------|
| `sec:perturbation` | section | -- |
| `thm:finite-part-reduced-determinant-group-inverse-gradient` | theorem | Group inverse, `eq:reduced-det-constant`, standard Perron perturbation |
| `thm:logM-holomorphic-variation` | theorem | `thm:finite-part-primitive-closed-form`, `thm:finite-part-reduced-determinant-group-inverse-gradient` |
| `thm:clt-spectral` | theorem | Baladi, Parry--Pollicott (external), Nagaev--Guivarc'h method (external) |

## sec_conclusion.tex

| Label | Type | Deps |
|-------|------|------|
| `sec:conclusion` | section | -- |
| (no labelled environments) | -- | -- |

---

## Cross-file dependency graph (theorems only)

```
prop:prelim-trace-primitive
  |
  v
thm:finite-part-primitive-closed-form ---> thm:logM-holomorphic-variation
                                               ^
thm:fredholm-witt-bridge                       |
                                               |
thm:cyclic-fredholm-realisation                |
  |                                            |
  +---> cor:finite-rank-realisation            |
                                               |
thm:fredholm-spectral-rigidity                 |
  |                                            |
  +---> cor:realisability-vs-rigidity          |
                                               |
thm:finite-part-reduced-determinant-group-inverse-gradient
                                               |
                                               v
                                    thm:logM-holomorphic-variation

thm:clt-spectral  (independent; uses external spectral-gap theory)
```
