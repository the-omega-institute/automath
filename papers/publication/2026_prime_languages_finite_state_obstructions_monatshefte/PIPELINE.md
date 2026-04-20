# Pipeline: Prime Languages / Sofic Obstructions / Dynamical Zeta (Monatshefte)
Target: Monatshefte fur Mathematik
Status: P4 Gate 3 review complete -- MAJOR_REVISION -- return to P3

## Stage Progress

| Stage | Status | Date | Notes |
|---|---|---|---|
| P0 Intake and Contract | completed | 2026-03-30 | Monatshefte primary; Proc. AMS fallback. MSC 37B10, 68Q45, 11A41, 05A15 |
| P1 Traceability | completed | 2026-03-30 | 9 body-level claims catalogued; all proved or cited-standard |
| P2 Research Extension | completed | 2026-03-30 | Three blocks (probabilistic, combinatorial, analytic); value is systematic assembly |
| P3 Proof Audit | **NEEDS REDO** | -- | Priority: natural boundary non-cancellation, lambda=0 edge case, leading-zeros convention |
| P4 Gate 3 Review | **MAJOR_REVISION** | 2026-04-04 | 4 BLOCKERs, 5 MEDIUM, 5 MINOR; none of P2 issues resolved; see P4_EDITORIAL_REVIEW_2026-04-04.md |
| P5 Bibliography and Formatting | pending | -- | Bibliography critically thin (4 refs); add 6-8 missing references |
| P6 Journal Submission Package | pending | -- | Cover letter, PDF compile, MSC codes, author metadata |

### Top-3 Blockers (from P4 Gate 3 Review)

1. **BLOCKER-1:** Thm 4.1 (natural boundary) non-cancellation argument is incomplete -- needs convergence proof or logarithmic approach
2. **BLOCKER-3 + MEDIUM-3:** Thm 3.4 proof contains wrong identity ($\pi(F_{m+2})+O(1)$ should be $\pi(F_{m+2})-\pi(F_{m+1})+O(1)$); Prop 4.2 proof uses irrationality of log 2 without stating it
3. **EDITORIAL-1+2:** Bibliography has only 4 entries; "Previous work" section is 5 lines; no comparison with existing literature (Cobham, Mauduit-Rivat, Bruyere-Hansel, etc.)

### Action Required

Return to **P3 Proof Audit** to fix all 4 BLOCKERs and MEDIUM-3, then proceed through P4/P5 for exposition and bibliography.

## Theorem Inventory

### Block A: Probabilistic (DFA density)

- `thm:dfa-density-dichotomy`: Accepted-word density is eventually periodic mod p up to O(theta^m); either exponentially sparse or positive-density along a residue class
- `cor:dfa-prime-symmetric-diff`: Every DFA language has symmetric difference >= c 2^m/m with binary prime language
- `cor:dfa-prime-recall-precision`: No fixed DFA achieves both recall and precision bounded away from 0 on binary primes

### Block B: Combinatorial (Zeckendorf)

- `thm:zeckendorf-regular-powerlaw`: Regular sublanguages of Zeckendorf language have counting function T^{alpha+o(1)}
- `cor:zeckendorf-prime-language-not-regular`: Language of Zeckendorf representations of primes is not regular
- `prop:sofic-counts-exponential-polynomial`: Sofic shift word counts are exponential polynomials (cited-standard, Lind-Marcus)
- `thm:zeckendorf-primes-not-sofic`: Length slices of prime Zeckendorf language cannot be admissible words of any sofic shift

### Block C: Analytic

- `thm:euler-product-natural-boundary`: Euler product with infinitely many prime-indexed positive factors has |z|=1 as natural boundary
- `prop:finite-zeta-imaginary-periodicity`: det(I - e^{-s}M)^{-1} is 2pi i-periodic; Riemann zeta is not

### Dependency chain

```
PNT (external) --+---> Cor 2 ---> Cor 3
Thm 1 -----------+
PNT (external) --+---> Cor 5
Thm 4 -----------+
PNT (external) --+---> Thm 7
Prop 6 (cited) ---+
Thm 8: self-contained (density of roots of unity)
Prop 9: self-contained (periodicity of exponential)
```

**Total:** 9 body-level claims. All proved (Prop 6 cited-standard).

## Source Map

| File | Key content |
|------|-------------|
| `main.tex` | Document shell, preamble, abstract |
| `sec_introduction.tex` | Restatements of main theorems (thm:intro-density, cor:intro-binary-primes, thm:intro-zeckendorf, thm:intro-analytic) |
| `sec_automata.tex` | DFA definition (unlabelled), density dichotomy, prime symmetric difference, recall/precision |
| `sec_zeckendorf.tex` | Regular power law, prime Zeckendorf not regular, sofic counts, primes not sofic |
| `sec_analytic.tex` | Natural boundary theorem, periodicity proposition |
| `sec_conclusion.tex` | Expository discussion, no theorem environments |
| `references.bib` | 4 entries only (critically thin; needs 6-8 more) |

## Stage Notes

### P2 Research Extension

**Assessment:** Results range from folklore to mild extensions of standard material. The value proposition is systematic assembly across three mathematical perspectives (automata theory, combinatorics on words, analytic number theory), not any single deep theorem.

**Novelty by result:**
- Thm 1 (density dichotomy): Folklore in automata theory (finite Markov chain consequence)
- Cor 2-3 (binary primes): Explicit formulations appear new; underlying fact is implicit in automatic-sequences literature
- Thm 4 (Zeckendorf regular power law): Standard via numeration-system theory (Frougny, Bruyere-Hansel)
- Cor 5 (prime Zeckendorf not regular): Folklore consequence of PNT + growth theory
- Prop 6 (sofic counts): Textbook (Lind-Marcus)
- Thm 7 (primes not sofic): Straightforward application of exponential-polynomial structure
- Thm 8 (natural boundary): Classical technique (Estermann 1928); specific Euler-product formulation may be new
- Prop 9 (periodicity rigidity): Elementary; clean formulation

**Scope decisions:** Paper restricts to complete DFA, binary alphabet, canonical Zeckendorf, non-negative Euler exponents. These restrictions simplify proofs but limit generality. Zeckendorf argument extends to all Parry numeration systems at no extra cost -- should be stated.

**Gaps identified:**
1. DFA definition does not address leading-zeros convention for binary numbers
2. PNT application uses asymptotic notation without specifying implied constants
3. Thm 4 proof: lambda=0 case (finite language) needs separate handling
4. Thm 8 non-cancellation argument too terse; needs explicit clarification or logarithmic approach
5. Prop 9 implicitly requires irrationality of log 2
6. No computational/reproducibility component (purely theoretical)

**Missing references:** Allouche-Shallit (2003), Cobham (1972), Mauduit-Rivat (2010), Bruyere-Hansel (1997), Hardy-Wright, Estermann (1928), Flajolet-Sedgewick (2009), Frougny (1992).
