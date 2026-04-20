# Pipeline: Fredholm-Witt Cyclic-Block Spectral Rigidity (Journal of Spectral Theory)
Target: Journal of Spectral Theory (JST)
Status: P5 complete, P6--P7 pending

## Stage Progress

| Stage | Status | Date | Notes |
|---|---|---|---|
| P0 Intake and Contract | completed | -- | JST primary; IEOT fallback |
| P1 Traceability | completed | -- | 11 body claims (5 theorems, 2 propositions, 1 lemma, 2 corollaries, 1 definition), all proved |
| P2 Research Extension | completed | 2026-03-30 | Core triad (bridge/realisation/rigidity) + perturbative applications; 16 uncited bib entries flagged |
| P3 Journal-Fit Rewrite | completed | 2026-03-31 | JST style; bib cleaned (14 entries, all cited); Thm 3.3 convergence fixed; CLT centred; missing refs added |
| P4 Editorial Review | completed | 2026-03-31 | MINOR REVISION; 3 MEDIUM + 10 LOW issues; all resolved in P5 |
| P5 Integration | completed | 2026-03-31 | All 13 P4 issues fixed; CLT demoted to Proposition; intro split; 2 refs added; bib now 16 entries |
| P6 Lean Sync | pending | -- | |
| P7 Submission Pack | pending | -- | |

### Blocking Issues

None (all P2 issues resolved in P3).

## Theorem Inventory

### Introduction (umbrella statements)

- `thm:intro-fredholm-rigidity` (i--iii): Fredholm-Witt Euler-product, cyclic-block realisation, spectral rigidity
- `thm:intro-perturbative-applications`: Holomorphic variation of finite-part constants (gradient formula)
- `prop:intro-clt`: Spectral-gap CLT for locally constant observables

### Core triad (Section 3)

- `thm:fredholm-witt-bridge`: Trace-class Fredholm determinant = exp(trace series) = Euler product in Witt coordinates
- `thm:cyclic-fredholm-realisation`: Countable Euler product with trace-class summability admits explicit cyclic-block realisation
- `cor:finite-rank-realisation`: Finite Euler products give finite-rank Fredholm models
- `thm:fredholm-spectral-rigidity`: Equal Fredholm determinants imply equal non-zero spectra with algebraic multiplicity
- `cor:realisability-vs-rigidity`: Cyclic-block constructions enlarge the operator category but not the spectral freedom

### Perturbative applications (Section 4)

- `thm:finite-part-reduced-determinant-group-inverse-gradient`: Gradient of log C(A_theta) via group inverse
- `thm:logM-holomorphic-variation`: Holomorphic variation of log M(A_theta) with resolvent differentiation
- `thm:clt-spectral` (now Proposition): CLT for locally constant observables on mixing SFTs with exponential decay of characteristic functions

### Preliminaries (Section 2)

- `prop:prelim-trace-primitive`: exp-trace = det-inverse = Euler product for primitive A
- `lem:primitive-orbit-asymptotic`: Primitive orbit count asymptotics
- `def:abel-finite-part`: Abel-regularised finite-part constant
- `thm:finite-part-primitive-closed-form`: Closed form for log M(A) via Mobius series

**Total:** 5 body theorems, 2 propositions, 1 lemma, 2 corollaries, 1 definition. All proved.

## Source Map

| File | Lines | Role |
|------|-------|------|
| `main.tex` | 87 | Master document, preamble, macros |
| `sec_introduction.tex` | 159 | Introduction, main-result statements, prior work |
| `sec_preliminaries.tex` | 183 | Finite-state zeta, primitive orbits, finite-part constants |
| `sec_fredholm.tex` | 215 | Fredholm-Witt bridge, cyclic-block realisation, spectral rigidity |
| `sec_perturbation.tex` | 191 | Perturbative applications (gradient formula, CLT) |
| `sec_conclusion.tex` | 32 | Concluding remarks and extensions |
| `references.bib` | 155 | Bibliography (16 entries, all cited) |

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

## P4 Editorial Review

**Reviewer:** Automated editorial referee (pre-submission gate)
**Target journal:** Journal of Spectral Theory
**Date:** 2026-03-31

### 1. Decision

**MINOR REVISION**

### 2. Summary

This short note isolates three operator-theoretic statements about symbolic dynamical zeta-functions: a Fredholm--Witt bridge expressing the trace-class Fredholm determinant as an Euler product in Witt coordinates (Thm 3.1), a cyclic-block converse realisation showing that every trace-class-summable Euler product admits an explicit operator model (Thm 3.3), and a spectral rigidity theorem asserting that equal Fredholm determinants force equal non-zero spectra (Thm 3.6). Two perturbative applications in the finite-state setting are recorded: a group-inverse gradient formula for finite-part constants (Thm 4.1) and a spectral-gap CLT for locally constant observables (Thm 4.5). The paper is well-written, appropriately scoped for a short note, and suitable for JST provided the issues below are addressed.

### 3. Strengths

- **Clean conceptual decomposition.** The existence-versus-rigidity framing (Thm 3.3 vs Thm 3.6) is genuinely clarifying and gives a useful organising principle for perturbative arguments in symbolic dynamics.
- **Self-contained proofs.** Every stated result is proved within the paper; no deferred or incomplete arguments.
- **Appropriate scope.** At roughly 800 lines across all section files, the paper does not overreach. The core triad and two applications form a tight logical unit.
- **Correct identification of novelty boundaries.** The introduction and conclusion are honest about which results are classical (Thm 3.1, Thm 4.5) and which represent new content (Thm 3.3, the pairing of realisation with rigidity).
- **Good bibliography.** All 14 entries are cited, references are standard and authoritative, and prior work is discussed fairly.

### 4. Issue Table

| ID | Section/Label | Severity | Description | Suggested Fix |
|----|---------------|----------|-------------|---------------|
| R1 | `thm:fredholm-witt-bridge` (Sec 3.1) | LOW | The theorem is stated as if it were a new result, but the proof consists entirely of applying the classical Fredholm determinant identity (Grothendieck/Simon) followed by Mobius inversion. The expository value is real, but the paper should be more explicit that the content of this theorem is a reformulation. | Add a sentence such as "The following is a direct consequence of the classical Fredholm determinant identity; we record it here to fix notation and to make the Euler-product structure explicit." |
| R2 | `thm:cyclic-fredholm-realisation` (Sec 3.2) | MEDIUM | The summability condition $\sum m_j n_j \lvert\beta_j\rvert^{1/n_j} < \infty$ is sufficient for trace-class membership, but the paper is silent on whether it is necessary. A reader will naturally ask whether weaker conditions (e.g., Hilbert-Schmidt summability $\sum m_j n_j \lvert\beta_j\rvert^{2/n_j} < \infty$) could work. | Add a remark stating whether the condition is sharp for trace-class membership of the specific cyclic-block construction, or whether it is merely sufficient. Even a sentence like "The condition is sharp for the cyclic-block model but not for trace-class realisability in general" would suffice. |
| R3 | `thm:fredholm-spectral-rigidity` (Sec 3.3) | LOW | The proof is a direct corollary of Simon's canonical product representation (Theorem 3.7 in Simon 2005). The logical content is: identity theorem for entire functions + product representation = spectral uniqueness. This is essentially immediate. The paper should acknowledge the brevity of the argument more directly, so that no reader suspects a hidden difficulty. | The proof is fine as written, but consider adding "This is an immediate consequence of the product representation..." rather than letting the reader wonder whether more is needed. |
| R4 | `thm:finite-part-reduced-determinant-group-inverse-gradient` (Sec 4.1) | MEDIUM | The proof uses $\partial_\theta \log \det'(B_\theta) = \Tr(R_\theta \partial_\theta B_\theta)$. This is the standard log-derivative formula applied to the reduced determinant on $(I - P_\theta)\mathbb{C}^d$. However, the analytic dependence of $R_\theta$ on $\theta$ is not verified. Since $B_\theta$ has a simple zero eigenvalue, the group inverse $R_\theta$ depends analytically on $\theta$ by standard resolvent calculus, but this step should be stated explicitly. | Add one sentence: "Since $\lambda(\theta)$ is a simple eigenvalue varying analytically, $P_\theta$ and hence $R_\theta = B_\theta^\# $ depend analytically on $\theta$ by standard resolvent calculus (see Kato, Chapter II, Section 1.4)." |
| R5 | `thm:finite-part-reduced-determinant-group-inverse-gradient` (Sec 4.1) | LOW | The formula for $\partial_\theta \log C(A_\theta)$ involves a minus sign that arises from the relation $C(A) = \det'(B)^{-1}$, i.e., $\partial_\theta \log C = -\partial_\theta \log \det'(B)$. The proof jumps from $\partial_\theta \log \det'(B_\theta) = \Tr(R_\theta \partial_\theta B_\theta)$ to the final formula, absorbing the sign flip and the substitution of $\partial_\theta B_\theta$ in one step. This is correct but slightly compressed. | Consider displaying the intermediate step showing $\partial_\theta \log C = -\Tr(R_\theta \partial_\theta B_\theta)$ and then substituting $\partial_\theta B_\theta = -\partial_\theta A_\theta / \lambda + (\partial_\theta \lambda / \lambda^2) A_\theta$. The two minus signs cancel to produce the stated formula. Making this explicit removes any ambiguity. |
| R6 | `thm:logM-holomorphic-variation` (Sec 4.1) | LOW | The proof appeals to Thm 2.5 (`thm:finite-part-primitive-closed-form`) for each $A_\theta$ and then differentiates the resulting Mobius series term by term. The justification for term-by-term differentiation is "the higher-order series is locally uniformly convergent." This is correct but deserves one more sentence explaining why: for $k \geq 2$, $\lvert\lambda(\theta)^{-k}\rvert$ is bounded away from $\lvert\lambda(\theta)^{-1}\rvert$ uniformly for $\theta$ near $\theta_0$, giving normal convergence of the series of holomorphic functions. | Add the explicit uniform bound, e.g., "For $k \geq 2$, $\lvert\lambda(\theta)^{-k}\rvert \leq \lambda_{\min}^{-2}$ uniformly near $\theta_0$ where $\lambda_{\min} := \min_{\lvert\theta - \theta_0\rvert \leq \epsilon} \lambda(\theta) > 1$, so the series converges normally in $\theta$." |
| R7 | `thm:clt-spectral` (Sec 4.2) | MEDIUM | The CLT and exponential decay of characteristic functions for locally constant observables on mixing SFTs are entirely standard results in the Nagaev--Guivarch framework. The paper presents them as a "theorem" with a proof sketch that delegates everything to external references. The value added here is limited to the observation (made in the concluding remark) that the same "simple dominant eigenvalue + spectral gap" input underlies both the finite-part variation and the CLT. For a JST paper, this observation alone may not justify a full theorem statement. | Either (a) strengthen the CLT statement with a quantitative bound (Berry-Esseen rate, moderate deviations) that would constitute new content, or (b) demote it to a proposition or remark, clearly labeled as a standard consequence, to avoid the impression of overclaiming. Option (b) is more honest and appropriate for the paper's scope. |
| R8 | `sec_introduction.tex` lines 79--111 | LOW | The umbrella `thm:intro-perturbative-applications` states both the gradient formula and the CLT as parts of a single theorem. These two results are logically independent and draw on different techniques (group-inverse calculus vs. spectral-gap probability). Bundling them creates a false impression of unity. | Split into two separate introductory statements, or restructure as "Theorem (i) + Proposition (ii)" to reflect the different logical status. |
| R9 | `lem:primitive-orbit-asymptotic` (Sec 2.1) | LOW | The proof uses $\sum_{d \mid n, d \geq 2} \lvert a_{n/d}(A)\rvert / n \ll \lambda^{n/2}/n$ by bounding $a_{n/d} \leq C \lambda^{n/d} \leq C \lambda^{n/2}$. The implicit constant depends on $A$ but this is fine since $A$ is fixed. However, the proof uses the asymptotic notation $\ll$ without specifying the implicit constant depends only on $A$. | Add "where the implied constant depends only on $A$" after the $\ll$ bound, or use explicit big-$O$ notation with the dependence stated. |
| R10 | `rem:choice-of-roots` (Sec 3.2) | LOW | The remark states that different root choices give unitarily inequivalent operators but the same Fredholm determinant, and invokes Thm 3.6 for the conclusion about spectra. This is a good remark. However, it would be even more useful to note that different root choices produce operators with different eigenvalue *locations* (since the $n_j$-th roots of unity rotate the spectrum) even though the *multiset of eigenvalues* is the same. | Optionally expand by one sentence: "The individual eigenvalues may differ by $n_j$-th roots of unity, but by Thm 3.6 the multiset $\{\lambda_k\}$ with algebraic multiplicity is invariant." |
| R11 | `thm:finite-part-primitive-closed-form` (Sec 2.2) | LOW | The proof uses the identity $\sum_{k \geq 1} (\mu(k)/k) \log(1 - x^k) = -x$ for $\lvert x \rvert < 1$. This identity, while elementary, is not standard enough to go without citation or derivation. | Either provide a one-line proof (take $-\log$ of the Euler product for $(1-x)^{-1}$) or cite a reference for Ramanujan-type Mobius identities. |
| R12 | `sec_conclusion.tex` | LOW | The concluding section (15 lines) is very brief. For JST, a short remark section is acceptable, but it would benefit from a forward-looking sentence about whether the cyclic-block construction has applications beyond the symbolic-dynamical setting (e.g., in nuclear operator theory, or for zeta-functions of more general dynamical systems such as Axiom A flows). | Add 2--3 sentences on potential extensions, without overclaiming. |
| R13 | `references.bib` | LOW | The Grothendieck 1956 entry gives the journal as "Bulletin de la Societe Mathematique de France." The standard title for the relevant paper is "La theorie de Fredholm." This matches the entry, but note that the paper is actually published in volume 84, pages 319--384, of the Bulletin SMF. Verify the page range is correct. Also, the Lind--Marcus 1995 first edition may want updating to the second edition (2021) since it is widely used. | Verify Grothendieck page range; consider updating Lind--Marcus to 2021 second edition if desired. |

### 5. Missing References

The bibliography is adequate for the paper's scope, but the following works are relevant and their absence is noticeable:

- **Fried (1986)**, "Analytic torsion and closed geodesics on hyperbolic manifolds" -- for the connection between zeta-functions and Fredholm determinants in the Ruelle setting.
- **Ruelle (1990)**, "An extension of the theory of Fredholm determinants," Publ. Math. IHES 72, 175--193 -- directly relevant to the trace-class/nuclear Fredholm determinant theory used in the paper, and extends Grothendieck's framework.
- **Pollicott (1986)**, "Meromorphic extensions of generalised zeta functions," Invent. Math. 85, 147--164 -- for the operator-theoretic approach to dynamical zeta-functions that parallels Section 3.
- **Gohberg, Goldberg, Krupnik (2000)**, "Traces and Determinants of Linear Operators," Birkhauser -- an alternative systematic reference for Fredholm determinants that complements Simon 2005.

None of these are strictly necessary, but citing Ruelle 1990 and Pollicott 1986 would strengthen the connection to the operator-theoretic literature that JST readers will expect.

### 6. pub_check.py Results

All 9/9 checks PASS (as reported in P3 stage notes). No automated issues detected.

### 7. Overall Assessment

The paper is a well-written short note that makes a clear conceptual contribution: the existence-versus-rigidity picture for Fredholm determinants of trace-class operators applied to symbolic zeta-functions. The core triad (Sections 2--3) is tight and the proofs are correct. The main risk is the perception that the novelty is "merely organisational." The cyclic-block realisation theorem (Thm 3.3) is the strongest claim to genuine novelty, and the paper correctly identifies it as such.

The perturbative applications in Section 4 are mixed. The group-inverse gradient formula (Thm 4.1) is a clean and useful reorganisation. The CLT (Thm 4.5) is entirely standard and adds limited value; demoting it to a remark or proposition would be more appropriate.

The paper is suitable for JST after minor revisions addressing the issues above. The most important items are R2 (sharpness of summability condition), R4 (analytic dependence of group inverse), and R7 (overclaiming on the CLT).

**Recommendation:** Address R2, R4, R7 as priority items. The remaining issues are cosmetic or expository improvements that would polish the paper but are not essential.

### Backflow to Core

| Result | Core target section | Status |
|---|---|---|
| `thm:fredholm-witt-bridge` | `zeta_finite_part/` | pending |
| `thm:cyclic-fredholm-realisation` | `zeta_finite_part/` | pending |
| `thm:block-cyclic-rigidity` | `zeta_finite_part/` | pending |
| `cor:finite-rank-realisation` | `zeta_finite_part/` | pending |
| `thm:fredholm-spectral-rigidity` | `zeta_finite_part/` | pending |
| `cor:realisability-vs-rigidity` | `zeta_finite_part/` | pending |
| `thm:intro-fredholm-rigidity` | `zeta_finite_part/` | pending |
| `thm:intro-perturbative-applications` | `zeta_finite_part/` | pending |
| `prop:intro-clt` | `zeta_finite_part/` | pending |
| `thm:finite-part-reduced-determinant-group-inverse-gradient` | `zeta_finite_part/` | pending |
| `thm:logM-holomorphic-variation` | `zeta_finite_part/` | pending |
| `thm:clt-spectral` | `zeta_finite_part/` | pending |
| `prop:prelim-trace-primitive` | `zeta_finite_part/` | pending |
| `lem:primitive-orbit-asymptotic` | `zeta_finite_part/` | pending |
| `thm:finite-part-primitive-closed-form` | `zeta_finite_part/` | pending |
