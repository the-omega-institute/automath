# Pipeline: Fredholm-Witt Cyclic-Block Spectral Rigidity (Journal of Spectral Theory)
Target: Journal of Spectral Theory (JST)
Status: P2 complete, P3--P7 pending

## Stage Progress

| Stage | Status | Date | Notes |
|---|---|---|---|
| P0 Intake and Contract | completed | -- | JST primary; IEOT fallback |
| P1 Traceability | completed | -- | 11 body claims (6 theorems, 1 proposition, 1 lemma, 2 corollaries, 1 definition), all proved |
| P2 Research Extension | completed | 2026-03-30 | Core triad (bridge/realisation/rigidity) + perturbative applications; 16 uncited bib entries flagged |
| P3 Journal-Fit Rewrite | pending | -- | |
| P4 Editorial Review | pending | -- | |
| P5 Integration | pending | -- | |
| P6 Lean Sync | pending | -- | |
| P7 Submission Pack | pending | -- | |

### Blocking Issues

- 16 of 25 bibliography entries uncited (inherited from parent manuscript)
- Missing references: Nagaev/Guivarch (CLT method), Campbell-Meyer (group inverse), Kato (perturbation theory), Grothendieck (Fredholm determinants)
- Convergence radius $|z| < 1$ in Thm 3.3 is a placeholder; needs correct statement

## Theorem Inventory

### Introduction (umbrella statements)

- `thm:intro-fredholm-rigidity` (i--iii): Fredholm-Witt Euler-product, cyclic-block realisation, spectral rigidity
- `thm:intro-perturbative-applications` (i--ii): Holomorphic variation of finite-part constants, spectral-gap CLT

### Core triad (Section 3)

- `thm:fredholm-witt-bridge`: Trace-class Fredholm determinant = exp(trace series) = Euler product in Witt coordinates
- `thm:cyclic-fredholm-realisation`: Countable Euler product with trace-class summability admits explicit cyclic-block realisation
- `cor:finite-rank-realisation`: Finite Euler products give finite-rank Fredholm models
- `thm:fredholm-spectral-rigidity`: Equal Fredholm determinants imply equal non-zero spectra with algebraic multiplicity
- `cor:realisability-vs-rigidity`: Cyclic-block constructions enlarge the operator category but not the spectral freedom

### Perturbative applications (Section 4)

- `thm:finite-part-reduced-determinant-group-inverse-gradient`: Gradient of log C(A_theta) via group inverse
- `thm:logM-holomorphic-variation`: Holomorphic variation of log M(A_theta) with resolvent differentiation
- `thm:clt-spectral`: CLT for locally constant observables on mixing SFTs with exponential decay of characteristic functions

### Preliminaries (Section 2)

- `prop:prelim-trace-primitive`: exp-trace = det-inverse = Euler product for primitive A
- `lem:primitive-orbit-asymptotic`: Primitive orbit count asymptotics
- `def:abel-finite-part`: Abel-regularised finite-part constant
- `thm:finite-part-primitive-closed-form`: Closed form for log M(A) via Mobius series

**Total:** 6 body theorems, 1 proposition, 1 lemma, 2 corollaries, 1 definition. All proved.

## Source Map

| File | Lines | Role |
|------|-------|------|
| `main.tex` | 88 | Master document, preamble, macros |
| `sec_introduction.tex` | 140 | Introduction, main-result statements, prior work |
| `sec_preliminaries.tex` | 179 | Finite-state zeta, primitive orbits, finite-part constants |
| `sec_fredholm.tex` | 175 | Fredholm-Witt bridge, cyclic-block realisation, spectral rigidity |
| `sec_perturbation.tex` | 163 | Perturbative applications (gradient formula, CLT) |
| `sec_conclusion.tex` | 16 | Concluding remarks |
| `references.bib` | 250 | Bibliography (25 entries; 16 uncited) |

### Cross-file dependency graph

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

## Stage Notes

### P2 Research Extension

**Main theorem package:** Three operator-theoretic results (core triad) and two symbolic-dynamical applications. The flagship contribution is the existence-versus-rigidity picture: cyclic blocks can realise any trace-class-summable Euler product (maximum flexibility), but the non-zero spectrum is then uniquely determined (maximum rigidity once the determinant is fixed).

**Novelty assessment:**
- Fredholm-Witt bridge (Thm 3.1): Standard (Grothendieck, Simon). Expository value in explicit Euler-product reformulation.
- Cyclic-block realisation (Thm 3.3): **Genuinely new in this generality.** Summability condition and explicit operator model for arbitrary countable Euler products do not appear in standard literature.
- Spectral rigidity (Thm 3.6): Direct consequence of Simon product representation. Novelty in isolating as named principle and pairing with realisation theorem.
- Finite-part gradient (Thm 4.1): Clean reorganisation of known perturbation theory (Campbell-Meyer group inverse).
- CLT (Thm 4.5): Standard (Baladi, Parry-Pollicott, Nagaev-Guivarch).

**Gaps identified:**
1. Summability condition necessity: Is the trace-class condition the weakest possible? Paper is silent.
2. Choice of n_j-th root in realisation: Different roots yield unitarily inequivalent operators. Should be noted.
3. Convergence radius $|z| < 1$ is a placeholder; needs $|z| < r^{-1}$ where $r = \sup |\beta_j|^{1/n_j}$.
4. Spectral rigidity proof implicitly uses entireness of trace-class Fredholm determinants (Simon).
5. Group inverse analytic dependence on theta not explicitly verified.
6. CLT variance formula should either assume centred $f$ or write correct two-term formula.

**Scope recommendations:**
- Core triad (Section 3): Keep as-is; tight logical unit.
- CLT (Thm 4.5): Either strengthen with Berry-Esseen bounds or demote to remark.
- Bibliography: Remove 16 uncited entries; add 4-6 missing references.

**Journal recommendation:** Journal of Spectral Theory. The existence/rigidity duality fits JST scope precisely. Alternative: Integral Equations and Operator Theory.

**Main risk:** Perception that novelty is "merely" reorganisational. Counter by emphasising cyclic-block construction as new tool and adding sharpness remark for spectral rigidity.
