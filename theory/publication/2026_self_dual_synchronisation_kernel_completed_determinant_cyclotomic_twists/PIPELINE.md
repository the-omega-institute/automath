# THEOREM_LIST

Catalogue of every theorem-level claim.

| # | Label | Location | Statement | Status |
|---|-------|----------|-----------|--------|
| 1 | `lem:primitive-orbit-asymptotic` | sec_preliminaries.tex:17 | Primitive orbit count satisfies $p_n(M) = \lambda^n/n + O(\max\{\Lambda(M)^n, \lambda^{n/2}\}/n)$. | Proved |
| 2 | `prop:sync-self-duality` | sec_preliminaries.tex:79 | The involution $\iota$ on the state set exchanges $B_0$ and $B_1$, giving $\Delta(z,u)=\Delta(uz,u^{-1})$. | Proved |
| 3 | `prop:kernel-delta-explicit` | sec_kernel.tex:6 | Explicit closed form of $\Delta(z,u)$ as a degree-6 polynomial in $z$ with coefficients in $\mathbb{Z}[u]$. | Proved (by direct computation; proof references elimination from the 10x10 matrix) |
| 4 | `prop:sync-kernel-spectrum` | sec_kernel.tex:27 | $\det(I-zB) = (z-1)(z+1)(3z-1)(z^3-z^2+z+1)$, $\rho(B)=3$, $C_B = 243/272$. | Proved |
| 5 | `prop:sync-hatdelta-completion` | sec_kernel.tex:61 | Completed determinant $\widehat\Delta(w,s) = 1 - sw - 5w^2 + 3sw^3 + (5-s^2)w^4 + (s^3-6s)w^5 + (s^2-1)w^6$; parity relation $\widehat\Delta(w,-s) = \widehat\Delta(-w,s)$. | Proved |
| 6 | `prop:sync-hatdelta-quotient` | sec_kernel.tex:88 | Quotient of the curve by involution $(w,s)\mapsto(-w,-s)$ is a smooth plane quartic of genus 3. | Proved |
| 7 | `prop:sync-hatdelta-double-cover` | sec_kernel.tex:116 | Two-sheeted cover branched at exactly two points; normalisation has genus 6 by Hurwitz. | Proved |
| 8 | `prop:sync-hatdelta-galois-s6-generic` | sec_kernel.tex:136 | Generic Galois group of $\widehat\Delta(w,s)$ over $\mathbb{Q}(s)$ is $S_6$. | Proved (sketch: discriminant not a square + specialisation producing transposition and 5-cycle) |
| 9 | `thm:sync-cyclotomic-degree-law` | sec_kernel.tex:166 | $\deg_w R_m = 3\varphi(2m)$ for $m \ge 4$; $R_m$ is even when $m$ is even. | Proved |
| 10 | `cor:rho-m2-closed-form` | sec_kernel.tex:185 | $R_2(w) = (1-w^2)(w^4-4w^2+1)$, $\rho_2 = \sqrt{2+\sqrt{3}}$. | Proved |
| 11 | `prop:sync-endpoint-jet` | sec_kernel.tex:213 | Endpoint jet of the analytic branch $\rho(s)$ near $s=2$: leading coefficients $w'(2)=-11/153$, $\rho'(2)=11/17$, etc. | Proved |
| 12 | `thm:rho-gap-m12` | sec_kernel.tex:242 | Asymptotic expansion of $\rho_m$ to order $O(m^{-14})$; leading gap $3 - \rho_m \sim 11\pi^2/(17m^2)$. | Proved |
| 13 | `prop:cyclic-lift-primitive-asymptotics` | sec_kernel.tex:279 | Primitive orbit count for cyclic lift $M^{\langle q\rangle} = M \otimes P_q$: vanishes for $q \nmid n$, standard asymptotics for $n = qm$. | Proved |

**Summary**: 13 theorem-level claims, all marked as proved. No claims are merely cited or assumed. External dependencies are limited to Perron--Frobenius theory, the implicit function theorem, and Hurwitz's formula, all standard.

---

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

---



# P2 Extension Note -- 2026-03-30

## 1. Main Theorem Package (Flagship Results)

The paper centres on a single ten-state weighted synchronisation kernel $B(u) = B_0 + uB_1$. Its contribution is a chain of explicit computations:

**Tier A (headline results):**
- `thm:intro-kernel-geometry` (iii): The normalisation of $\widehat\Delta(w,s)=0$ has genus 6; quotient by the involution is a smooth plane quartic (genus 3); generic Galois group is $S_6$.
- `thm:rho-gap-m12`: Full asymptotic expansion of twisted Perron roots $\rho_m$ to order $O(m^{-14})$, with leading gap $3 - \rho_m \sim 11\pi^2/(17m^2)$.

**Tier B (essential supporting results):**
- `prop:sync-self-duality`: The self-duality $\Delta(z,u) = \Delta(uz,u^{-1})$ via an explicit state-space involution.
- `prop:sync-hatdelta-completion`: Completed determinant and its parity relation.
- `thm:sync-cyclotomic-degree-law`: Degree law $\deg_w R_m = 3\varphi(2m)$.
- `cor:rho-m2-closed-form`: Closed form $\rho_2 = \sqrt{2+\sqrt{3}}$.

**Tier C (standard or auxiliary):**
- `lem:primitive-orbit-asymptotic`: Standard prime orbit theorem.
- `prop:cyclic-lift-primitive-asymptotics`: Direct consequence of Mobius inversion for tensor products with cyclic permutation matrices.

## 2. Novelty Assessment

| Result | Novelty | Comment |
|--------|---------|---------|
| Self-duality relation | Medium | The duality itself is specific to this kernel and is verified by inspection. The observation that $\iota$ swaps output-0 and output-1 edges is clean but kernel-specific. |
| Completed determinant | Medium-High | The passage from a two-variable $\Delta(z,u)$ to a one-parameter $\widehat\Delta(w,s) \in \mathbb{Z}[s][w]$ using $u = r^2$, $s = r + r^{-1}$ is a natural algebraic simplification, but for this specific kernel it is carried out in full. |
| Genus computation | High for this context | The genus-6 result via Hurwitz applied to a double cover of a genus-3 quartic is non-trivial. |
| $S_6$ Galois group | Medium | The strategy (discriminant + specialisation) is standard Galois-theoretic, but the execution is specific to this polynomial. |
| Cyclotomic degree law | Medium | The Sylvester-matrix argument is straightforward given the explicit form of $\widehat\Delta$. |
| Asymptotic expansion | High | The computation of six explicit terms in the $\rho_m$ expansion, with exact rational coefficients, is the paper's most labour-intensive and distinctive result. |
| Primitive orbit asymptotics (cyclic lift) | Low | Standard material. |

**Overall**: The paper is a case study -- one kernel, carried through to full explicitness. The novelty lies in the completeness of the computation rather than in new general methods. This is a legitimate contribution for the right venue.

## 3. Scope Decisions

| Item | Recommendation |
|------|---------------|
| Primitive orbit lemma (Lem 1) | **Keep but compress.** It is standard; a one-line reference to Lind--Marcus suffices. The current proof is short enough, so this is minor. |
| Cyclic-lift asymptotics (Prop 13) | **Keep.** Provides the dynamical interpretation promised in the abstract. Without it the paper lacks a concrete dynamical consequence. |
| Conclusion section | **Keep.** It is brief and raises natural follow-up questions. |
| Extended asymptotic expansion to $O(m^{-14})$ | **Keep all six terms.** This is the showpiece computation. Truncating would remove the paper's main distinguishing feature. |

## 4. Gaps, Unstated Assumptions, and Issues

### 4.1 Smoothness of the Quartic (Prop 6)

The proof of `prop:sync-hatdelta-quotient` states: "A direct check of the partial derivatives on the affine chart and on the line at infinity shows that the projective closure is smooth." This check is not exhibited. The polynomial $F(x,y)$ is degree 4 in the projective closure. The claim that the projective closure is smooth requires verifying that $F$, $\partial_x F$, $\partial_y F$ (and the homogenised versions at infinity) have no common zero. This should be verified computationally and the result either displayed or referenced to a companion computation.

**Severity**: Moderate. The claim is almost certainly correct but the proof as written outsources the verification to the reader.

### 4.2 Branch Points in the Hurwitz Computation (Prop 7)

The proof of `prop:sync-hatdelta-double-cover` claims the function $x = w^2$ has odd valuation at exactly one affine point $(x,y) = (0,1)$ and at one point at infinity. The identification of these two branch points determines the genus via $2g(\mathcal{X}) - 2 = 2(2 \cdot 3 - 2) + 2$, i.e., $2 \cdot 6 - 2 = 10$ and $2(4) + 2 = 10$. The arithmetic checks out. However:

- The claim that $(0,1)$ is the only affine point where $x$ has odd valuation needs justification. This amounts to checking that $F(0,y) = 1 - y$ has a simple root at $y = 1$, which is true, and that $F$ is smooth there. This should be made more explicit.
- The behaviour at infinity requires homogenising $F$ and checking valuations on the line at infinity. The proof omits this.

**Severity**: Low-moderate. The Hurwitz formula application is standard; the gap is expository rather than mathematical.

### 4.3 Galois Group Proof (Prop 8)

The proof of `prop:sync-hatdelta-galois-s6-generic` is the least complete in the paper. It claims:

1. The discriminant of $\widehat\Delta(w,s)$ (as a polynomial in $w$) is not a square in $\mathbb{Q}(s)$ -- this rules out $\subseteq A_6$.
2. Explicit specialisations produce a transposition and a 5-cycle.

Neither the discriminant nor the specialisations are exhibited. For $S_6$, one needs to show the group contains a transposition and a $p$-cycle for some prime $p > n/2$. A 5-cycle works since $5 > 6/2 = 3$, and together with a transposition this generates $S_6$ (Jordan's theorem). The strategy is correct, but the proof is incomplete as stated.

**Severity**: Moderate. The result is standard to verify computationally, but a reader cannot reproduce the proof from what is written. Specific specialisation values and the resulting cycle types should be recorded.

### 4.4 The Determinant Computation (Prop 3)

The proof says "direct elimination from the explicit $10 \times 10$ matrix." For a degree-6 polynomial in $z$ with coefficients polynomial in $u$, this is a substantial symbolic computation. The paper provides no script or supplementary file for verification. This is somewhat at odds with the reproducibility principle.

**Severity**: Low. The self-duality check provides partial validation. A short verification script would resolve this completely.

### 4.5 Asymptotic Expansion Coefficients (Thm 12)

The six-term expansion of $\rho_m$ involves large integer coefficients (numerators up to 19 digits, denominators up to 23 digits). These arise from composing the Taylor series of $\cos(\pi/m)$ with the implicit-function jet. The computation is mechanical but error-prone by hand. No verification script is provided.

**Severity**: Low-moderate. Correctness can be checked by numerical evaluation of $\rho_m$ for moderate $m$ and comparison with the asymptotic formula. A companion script would strengthen the paper.

### 4.6 Primitivity of $B(1)$

The paper states that $B = B(1)$ is primitive (Prop 4) but does not prove this. Since every state has exactly three outgoing edges (some weighted), primitivity of the unweighted graph means there exists $N$ such that $B^N > 0$ entrywise. This should be verified (it is easy from the transition structure: the graph is strongly connected and aperiodic since state 000 has a self-loop).

**Severity**: Very low. Immediate from the transition list.

### 4.7 Unstated Assumption: Analytic Branch Selection

In the proof of `thm:rho-gap-m12`, the claim that $\rho_m = \rho(s_m)$ for "all sufficiently large $m$" uses the fact that the analytic branch at $(w,s) = (1/3, 2)$ gives the smallest-modulus root of $R_m(w)$ when $s_m$ is close to 2. This continuity argument is correct but the paper does not address what happens for small $m$ (say $m = 3, 4, 5$). The theorem statement is for $m \to \infty$ so this is not a logical gap, but the paper could note for which range of $m$ the asymptotic formula is already a good approximation.

**Severity**: Very low. Cosmetic.

## 5. Intrinsic vs. Coordinate-Dependent Self-Duality

The self-duality $\Delta(z,u) = \Delta(uz,u^{-1})$ arises from an explicit involution $\iota$ on the state set that swaps output-0 and output-1 edges. This is:

- **Intrinsic to the kernel**: $\iota$ is a graph automorphism of the underlying directed graph that flips the edge labelling. It does not depend on a choice of basis or coordinates.
- **Specific to this kernel**: It is a property of the particular transition structure, not a general phenomenon for weighted SFT adjacency matrices.

The involution $\Pi^{-1} B_0 \Pi = B_1$ is a concrete matrix identity. The coordinate change $u = r^2$, $s = r + r^{-1}$ is then the standard algebraic step to exploit a $u \leftrightarrow u^{-1}$ symmetry. The completed determinant $\widehat\Delta$ is the natural object once self-duality is granted.

**Assessment**: The self-duality is intrinsic and well-justified. The completion is a natural algebraic consequence.

## 6. Rigour of the Genus Computation

The genus-6 result follows from a two-step argument:

1. The quotient curve (in the $(x,y)$ plane) has a smooth projective model of degree 4, hence genus $\binom{4-1}{2} = 3$.
2. The double cover $\mathcal{X} \to \mathcal{X}/\langle\iota\rangle$ is branched at 2 points, so Hurwitz gives $g(\mathcal{X}) = 6$.

**Is the curve smooth?** The paper asserts this without calculation. For the quartic $F(x,y) = 0$, smoothness of the projective closure can be checked by computing the resultant of $F$ and its partials (or by direct Jacobian evaluation at candidate singular points). The paper should provide this. Homogenising $F(x,y)$ to $\bar{F}(X,Y,Z)$ and checking $\bar{F} = \bar{F}_X = \bar{F}_Y = \bar{F}_Z = 0$ has no solution is the standard approach.

**Is the branch locus correct?** The branch points are where $x = w^2$ has odd valuation. At affine points, this means $x = 0$ on the quotient curve $F(x,y) = 0$. We have $F(0,y) = 1 - y$, so $(0,1)$ is the unique affine branch point, with $x$ vanishing to order 1 (smooth point, simple zero). At infinity, one needs to check the homogenised curve. The paper claims exactly one more branch point at infinity. This is plausible (degree 4 curve, line $x = 0$ meets it in 4 points projectively, of which one is affine; the 3 points at infinity need examination).

**Assessment**: The argument is structurally correct. The smoothness verification is the main gap; it should be made explicit.

## 7. Completeness of the $S_6$ Proof

The Galois group argument needs:
1. $\operatorname{disc}_w(\widehat\Delta) \notin \mathbb{Q}(s)^2$ -- computable from the explicit polynomial.
2. A specialisation $s = s_0$ where $\widehat\Delta(w, s_0)$ has factorisation pattern implying a transposition (e.g., four distinct roots + one double root specialising to two roots that coalesce).
3. A specialisation where the pattern implies a 5-cycle (e.g., an irreducible quintic factor over $\mathbb{Q}$).

By Jordan's theorem, a transposition and a $p$-cycle with $p$ prime and $p > n/2$ generate $S_n$. Here $n = 6$, so a 5-cycle ($p = 5 > 3$) plus a transposition gives $S_6$.

The discriminant computation and the specific specialisations should be recorded, at minimum in an appendix or companion file.

**Assessment**: The strategy is sound and the result is very likely correct. The proof needs two or three lines of additional data (specific $s_0$ values and resulting factorisations).

## 8. Sharpness of the Cyclotomic Asymptotics

The expansion $\rho_m = 3 - \frac{11\pi^2}{17m^2} + \cdots + O(m^{-14})$ is derived by composing two Taylor series: $s_m = 2\cos(\pi/m) = 2 - \pi^2/m^2 + \cdots$ and the implicit-function jet $\rho(2 - \delta)$. Since both series converge for $|\delta|$ small enough (and $\delta = 2 - s_m \to 0$), the expansion is asymptotic to any desired order.

- **Sharpness of the leading term**: The coefficient $11/17$ comes from $\rho'(2) = 11/17$, which is determined by the implicit function theorem applied to $\widehat\Delta(1/3, 2) = 0$ with $\partial_w \widehat\Delta(1/3, 2) \neq 0$. This is sharp (not merely an upper bound).
- **Higher-order terms**: Each additional term is determined by the jet of $\widehat\Delta$ at $(1/3, 2)$. The six terms given are exact, not estimates.
- **Optimality of the $O(m^{-14})$ remainder**: The expansion can in principle be extended to any order. The paper stops at order 12 (six terms) for practical reasons. This is a choice, not a limitation.

**Assessment**: The asymptotics are sharp and exact to the order stated. The leading term $3 - \rho_m \sim 11\pi^2/(17m^2)$ is a genuine asymptotic equivalence, not just a bound.

## 9. Bibliography Assessment

The bibliography contains 24 entries. Assessment:

**Present and appropriate:**
- Bowen--Lanford, Manning (foundational dynamical zeta function references)
- Lind--Marcus, Kitchens (standard symbolic dynamics textbooks)
- Parry--Pollicott (zeta functions and periodic orbits)
- Ruelle (thermodynamic formalism)
- Bass (Ihara zeta function, relevant for graph-theoretic zeta functions)
- Choe--Kwak--Park--Sato, Sato (weighted Bartholdi zeta functions -- directly relevant)

**Present but not cited in the .tex files:**
- Baladi (2000), Cuntz--Krieger (1980), Dembo--Zeitouni (2010), Pollicott--Sharp (2007), Brin--Stuck (2002), Karp (1978), Ziemian (1995), Chazottes--Gambaudo--Ugalde (2011), Levin--Peres--Wilmer (2009), Morse--Hedlund (1940), Zeckendorf (1972), Walters (1982), Ruelle (1976, 1978), Parry (1964), Bowen (1975), Skolem--Mahler--Lech. Many of these appear to be inherited from the parent manuscript. Only Bowen--Lanford, Manning, Lind--Marcus, and Kitchens are actually cited in the text.

**Missing references that should be considered:**
- No reference on resultants or elimination theory (the cyclotomic resultant is a central construction).
- No reference for the Hurwitz formula (standard, but given the reliance on it for the genus computation, a textbook citation would help: e.g., Hartshorne, Griffiths--Harris, or Miranda's "Algebraic Curves and Riemann Surfaces").
- No reference for Jordan's theorem on permutation groups (used implicitly in the $S_6$ proof).
- No reference for the implicit function theorem in the algebraic/analytic category (used for the endpoint jet).

**Recommendation**: Prune unused bibliography entries inherited from the parent manuscript. Add citations for: (1) a standard algebraic geometry text for the Hurwitz formula, (2) optionally, a reference for resultants.

## 10. Specific Recommendations

### High Priority

1. **Exhibit the smoothness check** for the projective quartic in `prop:sync-hatdelta-quotient`. Either display the partial-derivative computation inline or provide a companion verification script.

2. **Complete the Galois group proof** in `prop:sync-hatdelta-galois-s6-generic`. State the specific specialisation values of $s$ and the resulting factorisation patterns. This requires only 3--5 additional lines.

3. **Provide a verification script** for the determinant computation (`prop:kernel-delta-explicit`) and the asymptotic coefficients (`thm:rho-gap-m12`). A single Python/Sage script that constructs $B(u)$, computes $\det(I - zB(u))$, performs the completion, and evaluates the jet would satisfy the reproducibility requirement.

4. **Prune the bibliography** to remove entries not cited in this manuscript.

### Medium Priority

5. **Verify primitivity of $B(1)$ explicitly.** A one-line argument: state 000 has a self-loop, and the graph is strongly connected (traceable through the transition list).

6. **Add a Hurwitz formula citation.** The genus computation relies on it; a standard reference anchors the argument.

7. **Clarify the branch locus at infinity** in the proof of `prop:sync-hatdelta-double-cover`. One sentence identifying the point at infinity would suffice.

### Low Priority

8. **Numerical validation table.** A small table comparing $\rho_m$ (exact, from root-finding on $R_m$) with the asymptotic formula for $m = 4, 6, 8, 10, 12$ would demonstrate the quality of the expansion and strengthen the paper's appeal.

9. **Note the range of validity** of the asymptotic formula. For which $m$ does the six-term expansion achieve, say, 10-digit accuracy?

10. **Tighten the introduction.** The paper currently positions itself modestly ("much narrower in scope"). This is appropriate for the venue, but the introduction could more explicitly state that the completed-determinant technique is potentially applicable to other self-dual kernels, which is the main forward-looking question raised in the conclusion.

## 11. Journal-Fit Assessment (see P0 below for full recommendation)

The paper is a detailed explicit computation in symbolic dynamics / algebraic combinatorics. The primary audience is researchers working on zeta functions of subshifts of finite type, weighted graph zeta functions, and their algebraic-geometric properties. The natural homes are:

- **IMRN**: Appropriate scope and prestige. Accepts algebraic/arithmetic results with geometric content. The genus computation and Galois group determination give the paper enough "algebraic geometry" flavour.
- **Journal of Algebraic Combinatorics**: Reasonable fit, but the dynamical-systems framing may make it slightly off-target.
- **ETDS (Ergodic Theory and Dynamical Systems)**: The README notes the parent manuscript targets ETDS. This split-out paper has enough algebraic geometry to stand alone, but ETDS readers would appreciate the dynamical context.

See TRACK_BOARD.md for the P0 recommendation.

---

