# THEOREM_LIST

Paper: *Fredholm determinants, cyclic-block realisations, and spectral rigidity for symbolic zeta-functions*

---

## Introduction (collected statements)

| # | Label | File:Line | Statement | Status |
|---|-------|-----------|-----------|--------|
| T0a | `thm:intro-fredholm-rigidity` (i) | sec_introduction.tex:32 | Fredholm--Witt Euler-product identity for trace-class operators | Proved (sec_fredholm) |
| T0b | `thm:intro-fredholm-rigidity` (ii) | sec_introduction.tex:32 | Cyclic-block Fredholm realisation of Euler products under trace-class summability | Proved (sec_fredholm) |
| T0c | `thm:intro-fredholm-rigidity` (iii) | sec_introduction.tex:32 | Spectral rigidity: equal Fredholm determinants imply equal non-zero spectra | Proved (sec_fredholm) |
| T0d | `thm:intro-perturbative-applications` (i) | sec_introduction.tex:79 | Holomorphic variation of finite-part constants with group-inverse gradient | Proved (sec_perturbation) |
| T0e | `thm:intro-perturbative-applications` (ii) | sec_introduction.tex:79 | Spectral-gap CLT for locally constant observables on mixing SFTs | Proved (sec_perturbation) |

## Preliminaries

| # | Label | File:Line | Statement | Status |
|---|-------|-----------|-----------|--------|
| P1 | `prop:prelim-trace-primitive` | sec_preliminaries.tex:28 | For primitive A: exp-trace = det-inverse = Euler product of primitive orbits | Proved |
| L1 | `lem:primitive-orbit-asymptotic` | sec_preliminaries.tex:57 | Primitive orbit count: p_n(A) = lambda^n/n + O(max{Lambda^n, lambda^{n/2}}/n) | Proved |
| D1 | `def:abel-finite-part` | sec_preliminaries.tex:111 | Definition of log M(A) as Abel-regularised finite-part constant | Definition |
| T1 | `thm:finite-part-primitive-closed-form` | sec_preliminaries.tex:119 | Closed form for log M(A) via Mobius series over higher-order determinants | Proved |

## Fredholm determinants and cyclic-block realisations

| # | Label | File:Line | Statement | Status |
|---|-------|-----------|-----------|--------|
| T2 | `thm:fredholm-witt-bridge` | sec_fredholm.tex:15 | Trace-class Fredholm determinant = exp(trace series) = Euler product in Witt coordinates | Proved |
| T3 | `thm:cyclic-fredholm-realisation` | sec_fredholm.tex:68 | Countable Euler product with trace-class summability admits explicit cyclic-block realisation | Proved |
| C1 | `cor:finite-rank-realisation` | sec_fredholm.tex:115 | Finite Euler products give finite-rank Fredholm models | Proved (immediate) |
| T4 | `thm:fredholm-spectral-rigidity` | sec_fredholm.tex:128 | Equal Fredholm determinants => equal non-zero spectra with algebraic multiplicity | Proved |
| C2 | `cor:realisability-vs-rigidity` | sec_fredholm.tex:164 | Cyclic-block constructions enlarge the operator category but not the spectral freedom | Proved (immediate) |

## Perturbative applications

| # | Label | File:Line | Statement | Status |
|---|-------|-----------|-----------|--------|
| T5 | `thm:finite-part-reduced-determinant-group-inverse-gradient` | sec_perturbation.tex:6 | Gradient of log C(A_theta) via group inverse of reduced spectral complement | Proved |
| T6 | `thm:logM-holomorphic-variation` | sec_perturbation.tex:68 | Holomorphic variation of log M(A_theta) with explicit resolvent differentiation | Proved |
| T7 | `thm:clt-spectral` | sec_perturbation.tex:115 | CLT for locally constant observables + exponential decay of characteristic functions | Proved |

---

## Summary counts

- Theorems (body): 6 (T1--T4, T5--T7, excl. introduction duplicates)
- Propositions: 1
- Lemmas: 1
- Corollaries: 2
- Definitions: 1
- All claims: **Proved** (no items cited-without-proof or assumed)
