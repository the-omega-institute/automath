# SOURCE_MAP

Cross-reference of all labelled theorem-level environments and their internal dependencies.

## sec_introduction.tex

| Label | Type | Line | Dependencies |
|-------|------|------|--------------|
| `sec:introduction` | Section | 1 | -- |
| `thm:intro-kernel-geometry` | Theorem | 37 | `def:sync-kernel`, `prop:kernel-delta-explicit`, `prop:sync-hatdelta-completion`, `prop:sync-hatdelta-quotient`, `prop:sync-hatdelta-double-cover`, `prop:sync-hatdelta-galois-s6-generic` |
| `thm:intro-kernel-cyclotomic` | Theorem | 81 | `prop:sync-hatdelta-completion`, `thm:sync-cyclotomic-degree-law`, `cor:rho-m2-closed-form`, `thm:rho-gap-m12` |

These are umbrella statements collecting results proved in `sec_kernel.tex`.

## sec_preliminaries.tex

| Label | Type | Line | Dependencies |
|-------|------|------|--------------|
| `sec:preliminaries` | Section | 1 | -- |
| `eq:primitive-mobius` | Equation | 13 | -- |
| `lem:primitive-orbit-asymptotic` / `prop:prelim-prime-orbit` | Lemma | 17 | `eq:primitive-mobius`, Perron--Frobenius theory (external) |
| `def:sync-kernel` | Definition | 43 | -- |
| `prop:sync-self-duality` | Proposition | 79 | `def:sync-kernel` |

Note: `lem:primitive-orbit-asymptotic` and `prop:prelim-prime-orbit` are declared as two labels on the same `\begin{lemma}`.

## sec_kernel.tex

| Label | Type | Line | Dependencies |
|-------|------|------|--------------|
| `sec:kernel` | Section | 2 | -- |
| `prop:kernel-delta-explicit` | Proposition | 6 | `def:sync-kernel`, `prop:sync-self-duality` |
| `prop:sync-kernel-spectrum` | Proposition | 27 | `prop:kernel-delta-explicit` |
| `prop:sync-hatdelta-completion` | Proposition | 61 | `prop:kernel-delta-explicit` |
| `prop:sync-hatdelta-quotient` | Proposition | 88 | `prop:sync-hatdelta-completion` |
| `prop:sync-hatdelta-double-cover` | Proposition | 116 | `prop:sync-hatdelta-quotient` |
| `prop:sync-hatdelta-galois-s6-generic` | Proposition | 136 | `prop:sync-hatdelta-completion` |
| `thm:sync-cyclotomic-degree-law` | Theorem | 166 | `prop:sync-hatdelta-completion` |
| `cor:rho-m2-closed-form` | Corollary | 185 | `thm:sync-cyclotomic-degree-law`, `prop:sync-hatdelta-completion` |
| `prop:sync-endpoint-jet` | Proposition | 213 | `prop:sync-hatdelta-completion`, Implicit Function Theorem (standard) |
| `thm:rho-gap-m12` | Theorem | 242 | `prop:sync-endpoint-jet`, `thm:sync-cyclotomic-degree-law` |
| `prop:cyclic-lift-primitive-asymptotics` | Proposition | 279 | `lem:primitive-orbit-asymptotic` |

## sec_conclusion.tex

No labelled environments. Label: `sec:conclusion` (line 1).

## Dependency graph (topological order)

```
def:sync-kernel
  -> prop:sync-self-duality
      -> prop:kernel-delta-explicit
          -> prop:sync-kernel-spectrum
          -> prop:sync-hatdelta-completion
              -> prop:sync-hatdelta-quotient
                  -> prop:sync-hatdelta-double-cover
              -> prop:sync-hatdelta-galois-s6-generic
              -> thm:sync-cyclotomic-degree-law
                  -> cor:rho-m2-closed-form
                  -> thm:rho-gap-m12  (also depends on prop:sync-endpoint-jet)
              -> prop:sync-endpoint-jet

eq:primitive-mobius
  -> lem:primitive-orbit-asymptotic
      -> prop:cyclic-lift-primitive-asymptotics
```
