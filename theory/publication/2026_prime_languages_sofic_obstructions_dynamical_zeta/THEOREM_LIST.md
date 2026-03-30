# THEOREM_LIST

Paper: *Prime languages, finite-state obstructions, and dynamical zeta-functions*

## Introduction (restatements)

The introduction restates the three main theorems for the reader's convenience. The authoritative versions with proofs appear in the body sections. The introduction restatements are:

- `thm:intro-density` (sec_introduction.tex:23) -- restatement of `thm:dfa-density-dichotomy`
- `cor:intro-binary-primes` (sec_introduction.tex:54) -- restatement of `cor:dfa-prime-symmetric-diff` + `cor:dfa-prime-recall-precision`
- `thm:intro-zeckendorf` (sec_introduction.tex:74) -- restatement of `thm:zeckendorf-regular-powerlaw` + corollaries
- `thm:intro-analytic` (sec_introduction.tex:96) -- restatement of `thm:euler-product-natural-boundary` + `prop:finite-zeta-imaginary-periodicity`

## Body theorems

| # | Label | File:Line | Statement (one line) | Status |
|---|---|---|---|---|
| 1 | `thm:dfa-density-dichotomy` | sec_automata.tex:22 | For a complete DFA over {0,1}, the accepted-word density $a_m/2^m$ is eventually periodic mod $p$ up to $O(\theta^m)$; hence either exponentially sparse or positive-density along a residue class. | **Proved** |
| 2 | `cor:dfa-prime-symmetric-diff` | sec_automata.tex:85 | Every DFA language has symmetric difference $\ge c\,2^m/m$ with the binary prime language for large $m$. | **Proved** (from Thm 1 + PNT) |
| 3 | `cor:dfa-prime-recall-precision` | sec_automata.tex:126 | No fixed DFA achieves both recall and precision bounded away from 0 on binary primes for infinitely many lengths. | **Proved** (from Cor 2) |
| 4 | `thm:zeckendorf-regular-powerlaw` | sec_zeckendorf.tex:19 | Every regular sublanguage $L \subseteq \mathcal{Z}$ has counting function $N_L(T) = T^{\alpha+o(1)}$ for some $\alpha \in [0,1]$. | **Proved** |
| 5 | `cor:zeckendorf-prime-language-not-regular` | sec_zeckendorf.tex:60 | The language of Zeckendorf representations of primes is not regular. | **Proved** (from Thm 4 + PNT) |
| 6 | `prop:sofic-counts-exponential-polynomial` | sec_zeckendorf.tex:83 | Sofic shift word counts are exponential polynomials in $m$. | **Cited** (standard; proof sketch via Jordan form, references Lind--Marcus and Kitchens) |
| 7 | `thm:zeckendorf-primes-not-sofic` | sec_zeckendorf.tex:102 | The length slices of the prime Zeckendorf language cannot be the admissible words of any sofic shift. | **Proved** (from Prop 6 + PNT asymptotics) |
| 8 | `thm:euler-product-natural-boundary` | sec_analytic.tex:4 | If $b_p > 0$ for infinitely many primes $p$, the Euler product $\prod(1-z^n)^{-b_n}$ has $|z|=1$ as natural boundary. | **Proved** |
| 9 | `prop:finite-zeta-imaginary-periodicity` | sec_analytic.tex:26 | $\det(I - e^{-s}M)^{-1}$ is $2\pi i$-periodic; the Riemann $\zeta$-function is not. | **Proved** |

## Dependency chain

```
PNT (external) ──┬──> Cor 2 ──> Cor 3
Thm 1 ───────────┘
PNT (external) ──┬──> Cor 5
Thm 4 ───────────┘
PNT (external) ──┬──> Thm 7
Prop 6 (cited) ───┘
Thm 8: self-contained (density of roots of unity)
Prop 9: self-contained (periodicity of exponential)
```
