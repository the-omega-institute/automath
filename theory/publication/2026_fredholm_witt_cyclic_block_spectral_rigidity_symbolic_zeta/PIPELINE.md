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

---

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

---



# P2 Extension Note -- 2026-03-30

Paper: *Fredholm determinants, cyclic-block realisations, and spectral rigidity for symbolic zeta-functions*

---

## 1. Main theorem package

The paper proves three operator-theoretic results and two symbolic-dynamical applications:

**Core triad (Section 3):**

1. **Fredholm--Witt bridge** (Thm 3.1). The standard identity $\det(I-zT)^{-1} = \exp(\sum a_n z^n/n)$ is recast as an Euler product indexed by Witt coordinates $p_n(T)$ obtained via Mobius inversion. This is formal once trace-class determinant theory is available.

2. **Cyclic-block realisation** (Thm 3.3). Given a countable family $(n_j, \beta_j, m_j)$ satisfying $\sum m_j n_j |\beta_j|^{1/n_j} < \infty$, the Euler product $\prod (1 - \beta_j z^{n_j})^{-m_j}$ is the reciprocal Fredholm determinant of an explicit direct sum of cyclic blocks $C(n_j, \alpha_j) \otimes I_{m_j}$.

3. **Spectral rigidity** (Thm 3.6). If $\det(I - zT_1) = \det(I - zT_2)$ near the origin, then $T_1$ and $T_2$ share the same non-zero spectrum with algebraic multiplicity.

**Applications (Section 4):**

4. **Finite-part gradient formula** (Thm 4.1). For a holomorphic family of primitive matrices $A_\theta$, the quantity $\log C(A_\theta)$ varies holomorphically, with derivative expressed via the group inverse $R_\theta = (I - A_\theta/\lambda(\theta))^\#$. The Abel finite-part $\log \mathcal{M}(A_\theta)$ inherits holomorphy (Thm 4.3).

5. **Spectral-gap CLT** (Thm 4.5). Locally constant observables on mixing SFTs satisfy a CLT with positive variance (under non-coboundary hypothesis), and the characteristic functions decay exponentially on compact subsets of $\mathbb{R} \setminus \{0\}$.

The flagship contribution is the *existence-versus-rigidity* picture: cyclic blocks can realise any trace-class-summable Euler product (maximum flexibility), but the non-zero spectrum is then uniquely determined (maximum rigidity once the determinant is fixed).

---

## 2. Novelty assessment

| Result | Assessment |
|--------|------------|
| Fredholm--Witt bridge (Thm 3.1) | Standard. The exp-trace identity is classical (Grothendieck, Simon). The Euler-product reformulation via Witt coordinates is implicit in number-theoretic treatments but the explicit statement for trace-class operators has expository value. |
| Cyclic-block realisation (Thm 3.3) | **Genuinely new in this generality.** The construction itself is elementary (direct sum of scaled cyclic permutations), but the precise summability condition $\sum m_j n_j |\beta_j|^{1/n_j} < \infty$ ensuring trace-class membership, and the explicit operator model for arbitrary countable Euler products, do not appear in the standard literature. |
| Spectral rigidity (Thm 3.6) | The content is a direct consequence of the product representation theorem for trace-class Fredholm determinants (Simon, Chapter 3). The proof is two lines once the product representation is invoked. The novelty is in isolating this as a named principle and pairing it with the realisation theorem to form the flexibility/rigidity duality. |
| Finite-part gradient (Thm 4.1) | The formula is a clean reorganisation of known perturbation theory. The use of the group inverse to handle the rank-deficiency of $I - A/\lambda$ is standard in matrix analysis (Campbell--Meyer). The result is useful but not surprising to specialists. |
| Abel finite-part holomorphy (Thm 4.3) | Direct consequence of Thm 2.5 + Thm 4.1 + uniform convergence. |
| CLT (Thm 4.5) | Standard. The proof explicitly defers to Baladi and Parry--Pollicott for the spectral gap, and to the Nagaev--Guivarc'h method for the CLT. The exponential decay of characteristic functions is a known consequence. |

**Summary:** The genuinely new content is Theorem 3.3 and Corollary 3.8 (the existence/rigidity duality). The rest is reorganisation and consolidation.

---

## 3. Scope decisions

**Keep as-is:**
- Section 3 in its entirety. This is the core of the paper and the three results form a tight logical unit.
- Corollary 3.5 (finite-rank case) -- clean and immediately useful.

**Keep but consider strengthening:**
- Section 2 (preliminaries). The finite-part closed form (Thm 2.5) is needed for the perturbative section but feels somewhat isolated. Its relationship to Mertens-type constants in prime orbit theorems could be made more explicit; see Recommendations below.

**Consider demoting to remarks or an appendix:**
- Theorem 4.5 (CLT). The proof consists entirely of pointing to existing literature. If the paper is targeted at an operator-theory journal, this may feel tangential. If targeted at a dynamics journal, it connects the abstract framework to concrete probabilistic output and should stay. The decision depends on the target venue.

---

## 4. Gaps, unstated assumptions, and issues

### 4.1 Summability condition in Thm 3.3

The trace-class summability condition $\sum m_j n_j |\beta_j|^{1/n_j} < \infty$ is sufficient, and the proof shows it equals $\|L_{\mathcal{D}}\|_1$. However, the paper does not discuss:

- **Necessity.** Is this the weakest condition guaranteeing trace-class membership of the direct sum? For the specific cyclic-block construction, yes (it is the trace norm). But could a different realisation of the same Euler product achieve trace class under a weaker condition on the data $(n_j, \beta_j, m_j)$? The paper is silent on this. A brief remark would be valuable.

### 4.2 Choice of $\alpha_j$ in the realisation

The proof selects $\alpha_j$ with $\alpha_j^{n_j} = \beta_j$. The resulting operator $L_{\mathcal{D}}$ depends on which $n_j$-th root is chosen, even though the determinant does not. The paper should note that different root choices yield unitarily inequivalent operators with the same Fredholm determinant -- this is actually a nice illustration of the flexibility that spectral rigidity constrains.

### 4.3 Convergence radius statement

Theorem 3.3 asserts the determinant identity "for every $|z| < 1$". This should be "$|z| < (\sup_j |\beta_j|^{1/n_j})^{-1}$" or simply "in the disc of convergence". The number 1 is not intrinsic to the data. If $|\beta_j|^{1/n_j} < 1$ for all $j$, then the Fredholm determinant is entire (the operator is quasinilpotent in norm), and the identity holds on all of $\mathbb{C}$. The stated bound $|z| < 1$ appears to be a placeholder.

### 4.4 Spectral rigidity proof -- implicit use of entireness

The proof of Thm 3.6 says "they agree as entire functions." This uses the fact that Fredholm determinants of trace-class operators are entire -- a non-trivial result from Simon. The logical step from "agree in a neighbourhood" to "agree everywhere" is by analytic continuation of entire functions. This is correct but the paper should make the appeal to entireness of trace-class Fredholm determinants more visible (a one-sentence addition).

### 4.5 Group inverse smoothness

Theorem 4.1 assumes $\lambda(\theta)$ stays simple. The group inverse $R_\theta$ is then an analytic function of $\theta$ (it is a rational function of $A_\theta$ and $\lambda(\theta)$). The proof states that $R_\theta$ "exists" but does not explicitly verify analytic dependence on $\theta$. Since $R_\theta = (I - P_\theta)(B_\theta + P_\theta)^{-1}(I - P_\theta)$, this follows from the analytic implicit function theorem for the Perron projection, but it should be stated.

### 4.6 CLT variance formula

Theorem 4.5 states $\sigma_f^2 = \lambda''(0)/\lambda(0)$ in the proof. This is the standard formula, but strictly it is $\sigma_f^2 = (\log\lambda)''(0) = \lambda''(0)/\lambda(0) - (\lambda'(0)/\lambda(0))^2$. If $f$ is centred ($\int f\,d\mu = 0$), then $\lambda'(0) = 0$ and the two coincide. Since the theorem statement centres $f$ via the subtraction of $n\int f\,d\mu$, this is fine -- but the proof should either assume $\int f\,d\mu = 0$ without loss of generality (by replacing $f$ with $f - \int f\,d\mu$) or write the correct two-term formula.

---

## 5. Bibliography assessment

### Cited entries (8 of 25)

| Key | Cited in |
|-----|----------|
| BowenLanford1970Zeta | sec_introduction |
| Manning1971Axiom | sec_introduction |
| Ruelle1976ZetaExpanding | sec_introduction |
| Ruelle1978Thermodynamic | sec_introduction |
| ParryPollicott1990Zeta | sec_introduction, sec_perturbation |
| LindMarcus1995 | sec_introduction |
| Kitchens1998 | sec_introduction |
| Simon2005TraceIdeals | sec_introduction, sec_fredholm |
| Baladi2000PositiveTransfer | sec_introduction, sec_perturbation |

### Uncited entries (16 of 25)

CuntzKrieger1980, DemboZeitouni2010LargeDeviations, PollicottSharp2007Chebotarev, BrinStuck2002, Karp1978MinCycleMean, Bass1992Ihara, Ziemian1995RotationSFT, ChoeKwakParkSato2007Bartholdi, Sato2008WeightedBartholdiCoverings, ChazottesGambaudoUgalde2011ZeroTempLocConst, LevinPeresWilmer2009MarkovMixing, MorseHedlund1940, Zeckendorf1972, WaltersErgodicTheory, Parry1964Intrinsic, Bowen1975EquilStates, SkolemMahlerLech.

These uncited entries appear to be remnants from a larger project bibliography. They should be pruned before submission unless future sections will reference them.

### Missing references

The following standard references are absent and should be considered:

1. **Gohberg--Goldberg--Krupnik** or **Simon (2005) Chapter 3 specifically** for the product representation of trace-class Fredholm determinants (the key input for spectral rigidity).

2. **Nagaev (1957, 1961)** and **Guivarc'h--Hardy (1988)** for the Nagaev--Guivarc'h method invoked in the CLT proof. Currently the proof says "the Nagaev--Guivarc'h argument" without a direct citation.

3. **Hennion (1993)** -- "Sur un theoreme spectral et son application aux noyaux lipchitziens" -- standard reference for the quasi-compactness argument underlying spectral-gap proofs in the transfer operator setting.

4. **Campbell--Meyer (1979)** or **Ben-Israel--Greville (2003)** for the group inverse. The paper uses $B^\#$ notation without citing a source for the definition or properties.

5. **Grothendieck (1956)** -- the original source for Fredholm determinants in the trace-class setting, if the paper wants to acknowledge the historical origin.

6. **Kato (1966/1995), Perturbation Theory for Linear Operators** -- for the analytic perturbation theory used implicitly in Section 4.

---

## 6. Specific recommendations

### 6.1 Sharpen the spectral rigidity statement

Theorem 3.6 says: equal determinants imply equal non-zero spectra. This is sharp in the sense that the zero eigenvalue (and its multiplicity/Jordan structure) is invisible to the Fredholm determinant. The paper should state this explicitly as a remark: the Fredholm determinant sees the non-zero spectrum but is blind to the kernel. A concrete example (two operators with the same non-zero spectrum but different-dimensional kernels) would cost one line and make the sharpness claim precise.

### 6.2 Make the cyclic-block construction more visibly constructive

The construction in Theorem 3.3 is fully explicit, which is a strength. Add a brief example: take the golden-mean shift ($A = \begin{pmatrix}1&1\\1&0\end{pmatrix}$), compute its Euler product, and exhibit the cyclic-block realisation. This would be two or three lines and would anchor the abstract construction concretely.

### 6.3 Connect the finite-part constant to prime orbit theorems

The Abel finite-part $\log\mathcal{M}(A)$ is an analogue of the Mertens constant in prime number theory. Making this analogy explicit (even one sentence) would help readers from analytic number theory or thermodynamic formalism recognise the object.

### 6.4 Strengthen the CLT section or demote it

As written, Theorem 4.5 is entirely standard. Two options:

- **Strengthen:** Add quantitative error rates (Berry--Esseen bounds) via the exponential decay of characteristic functions. The exponential decay statement already in the theorem gives $O(n^{-1/2})$ Berry--Esseen via the standard Fourier-analytic argument, and this would be a non-trivial quantitative addition.

- **Demote:** Move to a remark, citing the precise theorem from Parry--Pollicott or Baladi, and focus the perturbative section entirely on the finite-part gradient formula (which is more tightly coupled to the Fredholm machinery).

### 6.5 Clean the bibliography

Remove the 16 uncited entries. Add the 4--6 missing references identified above. This is a small paper (under 30 pages typeset); a bloated bibliography will draw reviewer attention.

### 6.6 Address the $|z| < 1$ issue in Thm 3.3

Replace with the correct convergence statement. If the intention is that $|\beta_j|^{1/n_j} \le 1$ for all $j$ (which the summability condition does not require), state it. Otherwise, write $|z| < r^{-1}$ where $r = \sup_j |\beta_j|^{1/n_j}$.

### 6.7 Journal targeting

The paper sits at the intersection of operator theory, symbolic dynamics, and ergodic theory. Based on the content:

- **Journal of Spectral Theory** (EMS): Good fit for the core triad (Fredholm determinants, spectral rigidity). The perturbative applications provide context. This journal values clean operator-theoretic statements. Length is appropriate.

- **Integral Equations and Operator Theory** (Birkhauser/Springer): Also a natural home. Slightly more tolerant of expository consolidation papers.

- **Advances in Mathematics**: The novelty threshold is higher. The cyclic-block realisation is new but elementary; the spectral rigidity is a short consequence of known theory. This would need the paper to be positioned more aggressively (e.g., as opening a new programme).

- **Annales de l'Institut Fourier**: Possible, but the paper's French-school connections are through Ruelle/Baladi rather than through harmonic analysis, which is Fourier's core.

**Recommendation: Journal of Spectral Theory.** The paper's central contribution -- the operator-theoretic separation of Fredholm--Witt bridge / cyclic-block realisation / spectral rigidity -- is a clean structural observation that fits the journal's scope precisely. The perturbative applications demonstrate utility without inflating claims. The paper's length (short article) and style (amsart, terse proofs) match JST norms.

---

## 7. Overall assessment

The paper is mathematically correct and well-organised. The central insight -- that the three logically distinct statements (bridge, realisation, rigidity) should be separated and proved at the operator-theoretic level -- is a genuine clarification. The cyclic-block realisation theorem is the only result that does not follow immediately from standard theory; it is elementary but useful. The perturbative section is competent but routine.

The main risk at a strong journal is the perception that the novelty is "merely" reorganisational. To counter this: (a) emphasise the cyclic-block construction as a new tool, (b) add the sharpness remark for spectral rigidity, (c) either strengthen the CLT to include Berry--Esseen or trim Section 4 to focus on the gradient formula, and (d) clean the bibliography thoroughly.

---

