# TRACK_BOARD

Paper: *Prime languages, finite-state obstructions, and dynamical zeta-functions*
Directory: `theory/publication/2026_prime_languages_sofic_obstructions_dynamical_zeta/`

---

## Pipeline Status

| Stage | Description | Status | Date |
|---|---|---|---|
| **P0** | Intake and Contract | DONE | 2026-03-30 |
| **P1** | Traceability (SOURCE_MAP, THEOREM_LIST) | DONE | 2026-03-30 |
| **P2** | Research Extension | DONE | 2026-03-30 |
| **P3** | Proof Audit | PENDING | -- |
| **P4** | Exposition Polish | PENDING | -- |
| **P5** | Bibliography and Formatting | PENDING | -- |
| **P6** | Journal Submission Package | PENDING | -- |

---

## P0 Summary

**Title:** Prime languages, finite-state obstructions, and dynamical zeta-functions

**Subject area:** Intersection of symbolic dynamics, automata theory, combinatorics on words, and analytic number theory.

**Target journal:** *Monatshefte fur Mathematik*

**Rationale:** Short, self-contained note (8--10 pages) collecting elementary obstructions from three distinct mathematical perspectives. Monatshefte publishes clean cross-area notes at the intersection of number theory, combinatorics, and dynamics. The scope is too modest for JNT or Advances; the automata content is too light for TCS. Alternative: Proceedings of the AMS.

**MSC 2020:** 37B10, 68Q45, 11A41, 05A15

---

## P1 Summary

Artifacts produced:
- `SOURCE_MAP.md`: Enumerates all theorem-level environments across 6 .tex files.
- `THEOREM_LIST.md`: Catalogues 9 body-level claims with labels, locations, one-line statements, proof status, and dependency chain.

---

## P2 Summary

Artifact produced:
- `P2_EXTENSION_NOTE_2026-03-30.md`

Key findings:
- Results range from folklore to mild extensions of standard material. The value is in the systematic assembly.
- The density dichotomy (Block A) is standard finite Markov chain theory; the DFA application to primes is a clean new formulation.
- The Zeckendorf argument (Block B) generalizes to all Parry numeration systems; this generality should be stated.
- The natural boundary proof (Block C, Thm 8) is too terse and needs a non-cancellation clarification.
- Proposition 9 implicitly uses irrationality of $\log 2$ without stating it.
- The bibliography contains 12+ uncited entries from the parent manuscript and is missing key references (Allouche--Shallit, Cobham, Hardy--Wright, Bruyere--Hansel, Flajolet--Sedgewick).
- No computational/reproducibility component; the paper is purely theoretical.

---

## Pending stages

**P3 (Proof Audit):** Line-by-line verification of all 9 claims. Priority items: natural boundary non-cancellation argument, $\lambda = 0$ edge case in Zeckendorf theorem, leading-zeros convention in DFA corollaries.

**P4 (Exposition Polish):** Label the unlabelled DFA definition; define $\mathrm{val}(w)$ before first use in introduction; state Parry-numeration generality; make the $\log 2$ irrationality explicit.

**P5 (Bibliography and Formatting):** Remove uncited entries; add Allouche--Shallit, Hardy--Wright, Bruyere--Hansel, Cobham, Mauduit--Rivat, Estermann, Flajolet--Sedgewick, Frougny. Verify amsart formatting for Monatshefte submission.

**P6 (Journal Submission Package):** Prepare cover letter, compile PDF, verify MSC codes, finalize author metadata.

---

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

---

# SOURCE_MAP

Paper: *Prime languages, finite-state obstructions, and dynamical zeta-functions*

## main.tex

No theorem-level environments. Document shell: preamble, abstract, `\input` calls, bibliography.

## sec_introduction.tex

| Environment | Label | Line |
|---|---|---|
| Theorem | `thm:intro-density` | 23 |
| Corollary | `cor:intro-binary-primes` | 54 |
| Theorem | `thm:intro-zeckendorf` | 74 |
| Theorem | `thm:intro-analytic` | 96 |

## sec_automata.tex

| Environment | Label | Line |
|---|---|---|
| Definition | *(unlabelled)* | 4 |
| Theorem | `thm:dfa-density-dichotomy` | 22 |
| Corollary | `cor:dfa-prime-symmetric-diff` | 85 |
| Corollary | `cor:dfa-prime-recall-precision` | 126 |

## sec_zeckendorf.tex

| Environment | Label | Line |
|---|---|---|
| Theorem | `thm:zeckendorf-regular-powerlaw` | 19 |
| Corollary | `cor:zeckendorf-prime-language-not-regular` | 60 |
| Proposition | `prop:sofic-counts-exponential-polynomial` | 83 |
| Theorem | `thm:zeckendorf-primes-not-sofic` | 102 |

## sec_analytic.tex

| Environment | Label | Line |
|---|---|---|
| Theorem | `thm:euler-product-natural-boundary` | 4 |
| Proposition | `prop:finite-zeta-imaginary-periodicity` | 26 |
| Remark | *(unlabelled)* | 51 |

## sec_conclusion.tex

No theorem-level environments. Expository discussion only.

## references.bib

23 entries. Key references: LindMarcus1995, Kitchens1998, Zeckendorf1972, LevinPeresWilmer2009MarkovMixing, BowenLanford1970Zeta, Ruelle1976ZetaExpanding, ParryPollicott1990Zeta, Manning1971Axiom.

---



# P2 Extension Note

Paper: *Prime languages, finite-state obstructions, and dynamical zeta-functions*
Date: 2026-03-30

---

## 1. Main theorem package

The paper proves three independent families of obstructions showing that prime-supported languages are incompatible with finite-state models:

**Block A (Probabilistic).** A density dichotomy for complete DFA over {0,1}: the accepted-word fraction $a_m/2^m$ is eventually periodic up to exponentially decaying error. This is applied via PNT to show that no DFA simultaneously achieves positive recall and positive precision on binary primes.

**Block B (Combinatorial).** Regular sublanguages of the Zeckendorf language have counting functions of the form $T^{\alpha+o(1)}$, excluding $T/\log T$ growth. Sofic word counts are exponential polynomials, excluding $\varphi^m/m$ growth. Both exclude prime-supported Zeckendorf languages.

**Block C (Analytic).** Two distinct obstructions: (i) Euler products with infinitely many prime-indexed factors have the unit circle as natural boundary; (ii) finite determinants $\det(I - e^{-s}M)^{-1}$ are $2\pi i$-periodic, unlike $\zeta(s)$.

## 2. New vs. folklore assessment

| Result | Assessment |
|---|---|
| Thm 1 (density dichotomy) | The statement is a direct consequence of finite Markov chain theory and is folklore in automata theory. The formulation as a "density dichotomy" with the explicit two-case structure is a mild packaging contribution. The underlying fact (word counts of regular languages satisfy linear recurrences with characteristic roots that are eigenvalues of the transition matrix) is standard; see e.g., Flajolet--Sedgewick, *Analytic Combinatorics*, Ch. V. |
| Cor 2--3 (binary primes) | The observation that DFA cannot approximate the binary prime language is implicit in the literature on automatic sequences, but the explicit symmetric-difference lower bound and the recall/precision formulation appear to be new as stated. |
| Thm 4 (Zeckendorf regular power law) | The key step -- that $a_m = \lambda^{m+o(m)}$ for regular languages -- is standard. The connection to Zeckendorf counting functions via $\alpha = \log\lambda/\log\varphi$ is a clean observation but essentially follows from the standard theory of numeration systems (Frougny, Bruyere--Hansel). The statement that regular Zeckendorf sublanguages have pure power-law counting functions is known in the automatic-sequences community, though perhaps not stated in precisely this form. |
| Cor 5 (prime Zeckendorf not regular) | Folklore consequence of PNT + the growth theory of regular languages in non-standard numeration systems. |
| Prop 6 (sofic counts) | Textbook result (Lind--Marcus). |
| Thm 7 (prime Zeckendorf not sofic) | A straightforward application of the exponential-polynomial structure of sofic counts. The observation that $\varphi^m/m$ is not an exponential polynomial is elementary. |
| Thm 8 (natural boundary) | The argument is a standard application of the density-of-roots principle. Analogous results appear in the work of Estermann (1928) on products over primes, and in the lacunary series literature. The specific Euler-product formulation with non-negative $b_n$ may not appear verbatim in the literature, but the proof technique is entirely classical. |
| Prop 9 (periodicity rigidity) | Elementary and likely known, though the explicit statement that $\zeta(s) \neq F_M(s)$ on any open set via periodicity is a clean formulation. |

**Summary.** The paper collects known or near-known obstructions into a single coherent note. Individual results range from folklore to mild extensions of standard material. The value proposition is the systematic assembly, not any single deep theorem.

## 3. Scope decisions

The paper is deliberately narrow: it restricts to **complete** DFA (not NFA), to the **binary** alphabet, to the **canonical** Zeckendorf representation, and to Euler products with **non-negative** exponents. These restrictions simplify proofs but limit generality:

- The density dichotomy extends to NFA (via the subset construction, the transition matrix becomes larger but the argument is identical). The restriction to complete DFA is unnecessary.
- The Zeckendorf argument works for any Parry numeration system (beta-numeration), not just Fibonacci. The paper could state this generality at no extra cost.
- The analytic obstruction (Thm 8) requires non-negative $b_n$ to prevent cancellation. The paper does not discuss what happens when cancellation is allowed, which is where the interesting analytic number theory lives (e.g., the Estermann phenomenon).

These scope decisions are reasonable for a short note but should be stated more explicitly.

## 4. Gaps, unstated assumptions, and issues

### 4.1 Density argument (Block A)

**Issue: The DFA definition does not require the initial state constraint for binary numbers.** The binary prime language $\mathcal{P}_m^{(2)}$ consists of binary strings of length $m$ with leading digit 1. The DFA density dichotomy applies to *all* strings of length $m$, including those with leading 0. The corollary implicitly assumes that the DFA's language is compared against primes among all $m$-bit strings, but the prime count $\pi(2^m) - \pi(2^{m-1}) \asymp 2^m/m$ counts only integers in $[2^{m-1}, 2^m)$. This is consistent as stated, but the paper should clarify whether the DFA is meant to accept strings with leading zeros or not. The current formulation works because even if the DFA accepts some leading-zero strings, the symmetric difference bound still holds (the extra strings only increase the symmetric difference). However, the recall/precision corollary (Cor 3) is slightly imprecise: if the DFA accepts many leading-zero strings, the "precision" as defined becomes small for a trivial reason.

**Issue: The PNT application uses $\asymp$ without specifying the implied constants.** The statement $p_m^{(2)} \asymp 2^m/m$ follows from PNT but the proof of Corollary 2 uses this in both directions. The implied constants should be made explicit or at least acknowledged as depending on the PNT error term.

### 4.2 Zeckendorf argument (Block B)

**Issue: The proof of Theorem 4 has a gap in the lower bound for $N_L(T)$.** The proof states: "every word of length at most $n-1$ has value at most $T$." This requires $F_n \le T$, not just $F_{n+1} \le T$. When $F_{n+1} \le T < F_{n+2}$, words of length $n-1$ have values at most $F_{n+1} - 1 < T$, so this is correct. But words of length exactly $n$ may have values exceeding $T$: the maximum value of a Zeckendorf word of length $n$ is $F_{n+2} - 1$ (the word $10101\ldots$), which can exceed $T$. The upper bound $N_L(T) \le \sum_{m \le n} a_m$ is therefore valid but potentially loose. For the $o(1)$ exponent statement this does not matter -- the ratio $\sum_{m \le n-1} a_m / \sum_{m \le n} a_m$ is at most $\lambda^{-1+o(1)}$ which is absorbed -- but the argument could be made more explicit.

**Issue: The claim $a_m = \lambda^{m+o(m)}$ needs qualification.** If $\lambda = 0$ (the language is finite), the claim is vacuously true but the subsequent algebra involving $\log\lambda$ is undefined. The $\lambda = 0$ case should be handled separately (it gives $\alpha = 0$ directly since $N_L(T)$ is eventually constant).

### 4.3 Analytic obstructions (Block C)

**Issue: Theorem 8 (natural boundary) proof has a subtle gap.** The proof argues that $(1 - z^p)^{-b_p}$ "has poles at all $p$th roots of unity" and that "no cancellation can occur" because all exponents are non-negative. This reasoning needs more care. The function $Z_b(z) = \prod_{n \ge 1}(1 - z^n)^{-b_n}$ is a product, not a sum, so "cancellation" means that the product might converge to a nonzero finite value at a root of unity despite individual factors diverging. In fact, the argument should proceed as follows: if $\omega$ is a primitive $p$th root of unity and $b_p > 0$, then the factor $(1 - z^p)^{-b_p} = (1 - z^p)^{-b_p}$ has a pole of order $b_p$ at $z = \omega$. The other factors $(1 - z^n)^{-b_n}$ for $n \neq p$ are either analytic and nonzero at $\omega$ (when $n \nmid p$ and $\omega^n \neq 1$... but actually $\omega^n = 1$ iff $p | n$), or have poles of their own. The key point is: for $n$ such that $p | n$, the factor $(1 - z^n)^{-b_n}$ also has a singularity at $\omega$. Since all exponents $b_n \ge 0$, all such factors have poles (not zeros) at $\omega$, so singularities accumulate rather than cancel. This argument is correct but the proof as written is too terse to be fully rigorous. A cleaner approach would use the logarithmic derivative or appeal to the Fabry gap theorem.

**Issue: Convergence of the Euler product.** The theorem assumes $Z_b(z)$ "converges to a holomorphic function on $|z| < 1$" but does not discuss when this holds. For instance, if $b_n = 1$ for all $n$, then $Z_b(z) = \prod(1-z^n)^{-1}$ is the generating function for partitions, which converges on $|z| < 1$. But for rapidly growing $b_n$, convergence could fail. This is not a gap per se (the hypothesis covers it), but the paper provides no examples showing the hypothesis is satisfiable beyond the trivial ones.

**Issue: Proposition 9 (periodicity) proof.** The claim that $\zeta(\sigma + 2\pi i) - \zeta(\sigma)$ is nonzero for large $\sigma$ because "the $n=2$ term has size comparable to $2^{-\sigma}$ while the tail is $O(3^{-\sigma})$" is correct but should note that the $n=2$ term is $2^{-\sigma}(e^{-2\pi i \log 2} - 1)$, whose modulus is $2^{-\sigma} \cdot 2|\sin(\pi \log 2)| > 0$ since $\log 2$ is irrational. The irrationality of $\log 2$ is used implicitly and should be stated.

## 5. Bibliography assessment

**Present and appropriate:**
- Lind--Marcus (1995), Kitchens (1998): standard symbolic dynamics references.
- Zeckendorf (1972): the original Zeckendorf representation paper.
- Levin--Peres--Wilmer (2009): Markov chain theory for the DFA density argument.
- Bowen--Lanford (1970), Ruelle (1976, 1978), Parry--Pollicott (1990): dynamical zeta function background.

**Missing references (should be added):**

1. **Allouche--Shallit, *Automatic Sequences* (2003).** This is the standard reference for the connection between finite automata and numeration systems. The paper's entire premise -- that languages defined by number-theoretic conditions are not regular -- is a central theme of this book. Its absence is conspicuous.

2. **Cobham (1972), "Uniform tag sequences."** Cobham's theorem on automatic sequences in different bases is directly relevant to the question of which number-theoretic sets are recognizable by automata.

3. **Mauduit--Rivat (2010), "Sur un probleme de Gelfond: la somme des chiffres des nombres premiers."** This is the state of the art on digit properties of primes and is thematically relevant.

4. **Bruyere--Hansel (1997), "Bertrand numeration systems and recognizability."** Directly relevant to Theorem 4: the theory of recognizable sets in Bertrand (including Fibonacci) numeration systems.

5. **Hardy--Wright, *An Introduction to the Theory of Numbers*.** Standard reference for PNT, which is used repeatedly but never cited.

6. **Estermann (1928), "On certain functions represented by Dirichlet series."** The natural boundary argument in Theorem 8 is closely related to Estermann's work on products over primes.

7. **Flajolet--Sedgewick, *Analytic Combinatorics* (2009).** The connection between regular languages and rational generating functions (used implicitly throughout) is developed systematically here.

8. **Frougny (1992), "Representation of numbers and finite automata."** Directly relevant to the Zeckendorf section.

**Present but unused/tangential:** Several references in the bibliography (CuntzKrieger1980, Bass1992Ihara, ChoeKwakParkSato2007Bartholdi, Sato2008WeightedBartholdiCoverings, Ziemian1995RotationSFT, ChazottesGambaudoUgalde2011ZeroTempLocConst, Karp1978MinCycleMean, DemboZeitouni2010LargeDeviations, MorseHedlund1940, WaltersErgodicTheory, BrinStuck2002, Bowen1975EquilStates) are not cited anywhere in the text. These appear to be inherited from the parent manuscript (`2026_dynamical_zeta_finite_part_spectral_fingerprint_etds`). They should be removed unless they will be cited in a revision.

## 6. Specific recommendations

### 6.1 Mathematical improvements

1. **State the generality for Parry numeration systems.** Theorem 4 holds for any numeration system associated with a Pisot number (or more generally, any linear numeration system where the greedy representations form a sofic language). A remark to this effect costs one paragraph and significantly increases the paper's utility.

2. **Handle the $\lambda = 0$ case in Theorem 4 explicitly.** Add a one-line remark that finite regular sublanguages have $N_L(T) = O(1) = T^{0+o(1)}$.

3. **Tighten the natural boundary proof.** Either (a) add two sentences clarifying the non-cancellation argument (all factors contribute poles or are regular-and-nonzero at each primitive $p$th root, so the product inherits the singularity), or (b) appeal to the logarithm: $\log Z_b(z) = \sum b_n \sum_{k \ge 1} z^{nk}/k$, which diverges as $z$ approaches any $p$th root of unity with $b_p > 0$.

4. **State the irrationality of $\log 2$ in Proposition 9.** The proof that $\zeta$ is not $2\pi i$-periodic uses $e^{-2\pi i \log 2} \neq 1$, which requires $\log 2 \notin \mathbb{Q}$. This is elementary but should be explicit.

5. **Strengthen Corollary 3 to a quantitative statement.** The current qualitative "recall or precision tends to 0" could be strengthened: in the sparse case, recall decays exponentially; in the dense case, precision decays as $O(1/m)$. The proof already establishes this.

### 6.2 Structural improvements

6. **Prune the bibliography.** Remove the 12+ uncited entries inherited from the parent manuscript.

7. **Add the missing references** listed in Section 5 above. At minimum: Allouche--Shallit, Hardy--Wright (or another PNT reference), and Bruyere--Hansel.

8. **Add a definition of "Zeckendorf value".** The notation $\mathrm{val}(w)$ is defined inline in sec_zeckendorf.tex but is used in the introduction (Theorem `thm:intro-zeckendorf`) before being defined. Either add a forward reference or move the definition to the introduction.

9. **Label the DFA definition.** The definition in sec_automata.tex:4 has no label, preventing cross-referencing.

### 6.3 Journal targeting

The paper is a short "note" collecting elementary obstructions across three different mathematical areas (automata theory, combinatorics on words, analytic number theory). This cross-disciplinary character is both a strength and a positioning challenge.

**Recommended target: *Monatshefte fur Mathematik*.**

Rationale:
- The journal publishes short papers (this is roughly 8--10 pages) at the intersection of number theory, combinatorics, and dynamical systems.
- The paper's results are "intentionally modest in scope" (the authors' own words), which fits Monatshefte's tradition of publishing clean, self-contained notes that clarify relationships between areas.
- The MSC codes (37B10, 68Q45, 11A41, 05A15) span symbolic dynamics, automata theory, and prime number theory, which is well within Monatshefte's scope.
- JNT would expect deeper number-theoretic content. Advances in Applied Mathematics would want applications. Theoretical Computer Science would want more automata-theoretic depth.
- Alternatively, *Proceedings of the AMS* is suitable for short notes of this type, if the authors prefer a broader-audience venue.

---

