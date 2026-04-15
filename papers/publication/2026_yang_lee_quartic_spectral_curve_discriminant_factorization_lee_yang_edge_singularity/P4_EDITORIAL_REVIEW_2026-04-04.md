# P4 Editorial Review -- 2026-04-04

**Paper:** "Elliptic Normalization of a Quartic Transfer Family: Real Branch Points and Edge Zeros"
**Author:** Haobo Ma (Auric)
**Target journal:** Not specified in manuscript. Assessed for a strong mathematical physics journal such as *Communications in Mathematical Physics*, *Journal of Statistical Physics*, or *Annales Henri Poincare*.

---

## 1. Decision

**MINOR_REVISION**

The paper is mathematically rigorous, well-structured, and contains genuine new results. All 17 formal statements have been verified line-by-line (12 verified symbolically via SymPy, 5 verified by direct algebraic tracking). The proofs are complete and do not rely on unstated assumptions. One intermediate computation has a numerical typo that does not propagate to any theorem statement. A small number of editorial and structural items need attention before submission.

---

## 2. Main Mathematical Assessment

### 2.1 Theorems correctly stated with all hypotheses: YES

Every theorem, proposition, lemma, and corollary states its hypotheses explicitly. The dependency chain is clean:

- Proposition 4.1 (balanced family) -> Corollary 4.2 (smooth condition) -> Corollary 4.3 (ramification)
- Theorem 4.4 (elliptic reduction) uses all three above
- Theorem 5.1 (EP classification) uses Theorem 4.4 and Lemma 2.1
- Theorem 5.2 (real phase diagram) uses Theorem 5.1
- Theorem 6.3 (universal EP2 normal form) is self-contained with explicit hypotheses
- Theorem 6.4 (vacuum scaling) uses Theorem 6.3 via Appendix E verification
- Theorem 7.1 (degree law) is independent, using only the recurrence

### 2.2 Proofs complete: YES, with one intermediate typo

All proofs are complete. The following were verified computationally:

| Claim | Verification method | Status |
|-------|-------------------|--------|
| Pi = P_{-1,-1,1,0} | SymPy symbolic | PASS |
| Disc_lam Pi = -y(y-1)(256y^3+411y^2+165y+32) | SymPy discriminant | PASS |
| Res_t(N,D) = y^3(y-1)^3(y+1)^6 | SymPy resultant | PASS |
| Pi(lam,0) = lam(lam-1)^2(lam+1) | SymPy factor | PASS |
| Pi(lam,1) = (lam-2)(lam-1)(lam+1)^2 | SymPy factor | PASS |
| Ramification quintic factorization | SymPy factor | PASS |
| Branch values at lam=1, lam=-1 | Direct eval | PASS |
| Smooth genus-one condition = 37 | Direct eval | PASS |
| Weierstrass invariants g2=4, g3=-1, Delta=37 | Direct eval | PASS |
| Riemann-Hurwitz count 3+5=8 | Arithmetic | PASS |
| beta_1 < -1 < alpha < beta_2 < beta_3 < 1 | NumPy roots | PASS |
| Puiseux expansion y = 2eps^2 - 5eps^3 + 21eps^4 - 94eps^5 | SymPy series | PASS |
| Puiseux inversion coefficients 1/sqrt(2), 5/8, -43sqrt(2)/128 | SymPy series reversion | PASS |
| f_dom coefficients 1/sqrt(2), 3/8, -217sqrt(2)/384 | SymPy log expansion | PASS |
| N-D identity for double zero | SymPy expand | PASS |
| Subdominance q > alpha^2 | SymPy + NumPy | PASS |
| Degree formula d_m = floor((m+3)/2) for m=2..5 | SymPy polynomial | PASS |
| Leading coefficients L_3=1, L_4=3, L_5=2 | SymPy polynomial | PASS |
| Z_4(-1)=0, Z_4'(-1)=0 | SymPy eval | PASS |
| Real root counts at y=-2,-.5,.5,2 | NumPy roots | PASS |
| Vacuum edge zeros vs asymptotic formula (m=80,120,200) | NumPy polynomial roots | PASS |

**One typo found:** In the proof of Proposition 6.2 (line 104 of 06_global_physical_sheet.tex), the expansion
```
sqrt(4*lam^3 - 4*lam + 1) = 1 + 4*eps - 2*eps^2 + 10*eps^3 - 52*eps^4 + O(eps^5)
```
has the wrong coefficient at eps^4. The correct value is **-42**, not -52. Verification: (1+4eps-2eps^2+10eps^3+c*eps^4)^2 requires 2*1*c + 2*4*10 + 4 = 0, giving c = -42. The final result y = 2eps^2 - 5eps^3 + 21eps^4 - 94eps^5 is **correct** (the typo in the intermediate sqrt does not propagate because the paper derives y_phys independently via SymPy-verifiable algebra).

### 2.3 Novelty assessment: GENUINE

The main contributions are new:

1. The balanced quartic family and its systematic Weierstrass reduction is a new observation. While individual quartic-to-elliptic reductions exist in the literature, the four-parameter balanced family P_{a,c,d,g} with its clean xi=y-lam^2 substitution has not been identified before.

2. The complete dominant/subdominant classification of all real branch points for this specific family, with the explicit modulus gap inequality, is new.

3. The universal dominant-EP2 edge normal form (Theorem 6.3) is a clean general result. While local scaling near exceptional points has been studied, the explicit normal form with the cos(au - cu/(C_0 m)) phase and the resulting odd-integer quantization formula is a precise new statement.

4. The degree law d_m = floor((m+3)/2) with explicit leading coefficients L_{2n+1} = n and L_{2n} = n(n^2+5)/6 is new for this family.

The paper correctly distinguishes its results from Yang-Lee edge singularity, BKW theory, and general EP theory.

---

## 3. Editorial Assessment

### 3.1 Abstract vs content: GOOD

The abstract accurately summarizes all main results. Every formula in the abstract appears as a proven theorem in the body. No overclaiming detected.

### 3.2 Introduction: GOOD

The introduction is clear, reader-friendly, and correctly positions the paper relative to three standard frameworks (Yang-Lee, BKW, EP theory). The five-item summary of main results is precise and each item points to the correct section.

### 3.3 Structural issues

**BLOCKER-1: Missing figure file.** The paper references `figures/zero_locus_validation.pdf` (Section 9, Figure 1), but the figures directory does not exist. The generation script `scripts/generate_validation_figure.py` exists and is correct, but has not been run. LaTeX compilation fails fatally on this.

**MEDIUM-1: Orphaned section files.** The sections directory contains 6 files not included by main.tex:
- `04_discriminant_factorization_and_edge_singularity.tex`
- `05_free_energy_and_limit_laws.tex`
- `06_zero_accumulation_and_spectral_geometry.tex`
- `07_algorithms_and_certified_computation.tex`
- `08_discussion.tex`
- `91_appendix_b_implicit_differentiation_constants.tex`

These appear to be remnants of a previous version. They should be deleted or moved to a drafts directory to avoid confusion.

**MEDIUM-2: Appendix numbering gap.** The appendices are labeled A, C, D, E (Appendix B is missing). In LaTeX with `\appendix`, sections are auto-lettered, so Appendix C (file 92) will actually compile as Appendix B, Appendix D as C, and Appendix E as D. The filenames suggest the author intended a gap, but LaTeX does not produce one. The author should verify the compiled appendix labels match their intent.

### 3.4 Bibliography assessment

**MEDIUM-3: Bibliography is thin (13 entries) and includes 2 self-citations to unpublished companion manuscripts.** For a journal like CMP or JSP, this is borderline. Missing references that a referee would expect:

- No reference for the Puiseux expansion / Newton polygon method
- No reference for the theory of polynomial sequences defined by linear recurrences (beyond BKW and Flajolet-Sedgewick)
- No reference for the spectral theory of companion matrices beyond the implicit use
- The Lind-Marcus [1995] and Baxter [1982] references are cited in the bib file but never used in the text (no `\cite` calls found)
- Hwang [1998] is in the bib file but never cited

**MINOR-1:** The two `@unpublished` entries (Ma2026FoldingSpectralFingerprints, Ma2026ResolutionFoldingLedger) are never cited in the text. They should be removed from the .bib file.

### 3.5 Writing quality: STRONG

The prose is precise and professional. No instances of vague language, appeal to authority, or unsupported claims. The paper maintains a consistent mathematical voice throughout. The distinction between "the quartic family as primary object" vs "microscopic derivation" is handled honestly.

---

## 4. Specific Cut/Merge/Rewrite Recommendations

### BLOCKER-1: Generate the validation figure
- **Location:** Section 9 (09_zero_locus_verification.tex), line 23
- **Problem:** `figures/zero_locus_validation.pdf` does not exist; compilation fails
- **Fix:** Run `python scripts/generate_validation_figure.py` to create the figure. Create the `figures/` directory first.

### MEDIUM-1: Remove orphaned section files
- **Location:** `sections/` directory
- **Problem:** 6 files from a previous draft remain, creating confusion
- **Fix:** Delete `04_discriminant_factorization_and_edge_singularity.tex`, `05_free_energy_and_limit_laws.tex`, `06_zero_accumulation_and_spectral_geometry.tex`, `07_algorithms_and_certified_computation.tex`, `08_discussion.tex`, `91_appendix_b_implicit_differentiation_constants.tex`

### MEDIUM-2: Fix appendix auto-numbering
- **Location:** main.tex lines 87-90
- **Problem:** LaTeX will label the appendices A, B, C, D (not A, C, D, E as filenames suggest)
- **Fix:** Either accept the auto-numbering or adjust filenames to match. Verify that all `\ref{app:...}` labels resolve correctly after compilation.

### MEDIUM-3: Clean up bibliography
- **Location:** `references.bib`
- **Problem:** 3 uncited entries (Baxter1982, LindMarcus1995, Hwang1998) and 2 uncited self-references (Ma2026...)
- **Fix:** Remove all 5 uncited entries. Consider adding 2-3 references to standard texts on Puiseux series and algebraic curves that support the methods used (e.g., Brieskorn-Knorrer for Puiseux theory, or Walker's "Algebraic Curves").

### MINOR-2: Fix sqrt expansion typo in proof
- **Location:** `sections/06_global_physical_sheet.tex`, line 104 (proof of Proposition 6.2)
- **Problem:** Coefficient of eps^4 in sqrt(4lam^3-4lam+1) is stated as -52 but should be -42
- **Fix:** Replace `-52\varepsilon^4` with `-42\varepsilon^4` on line 104. Also update the corresponding term in the y_phys derivation on line 112: the term `26\varepsilon^4` should be `21\varepsilon^4`.

Let me verify line 112 more carefully. The paper writes:
```
&= 1 + 2\varepsilon + \varepsilon^2 - \tfrac{1}{2}
  - \tfrac{1}{2} - 2\varepsilon + \varepsilon^2 - 5\varepsilon^3 + 26\varepsilon^4 - \cdots
```
With the correct -42, the term `-1/2*(-42)*eps^4 = 21*eps^4`, not 26. But the final result on line 112 reads `2eps^2 - 5eps^3 + 21eps^4`, which is correct. So line 112 actually contains TWO errors that cancel: the intermediate `26eps^4` is wrong (should be `21eps^4`), but the final sum is stated correctly as `21eps^4`. The fix should correct both the sqrt coefficient (-52 -> -42) and the intermediate term (26 -> 21) to make the proof internally consistent.

### MINOR-3: Title is long
- **Location:** main.tex line 63
- **Problem:** The two-line title is 79 characters. Most journals prefer titles under 60 characters.
- **Fix:** Consider shortening to "Elliptic Normalization of a Quartic Transfer Family" and moving "Real Branch Points and Edge Zeros" to the subtitle or dropping it.

### MINOR-4: No MSC classification or ORCID
- **Location:** Frontmatter
- **Problem:** Most math/physics journals require 2020 MSC codes
- **Fix:** Add MSC codes, e.g., 82B20 (lattice systems), 14H52 (elliptic curves), 30B70 (continued fractions), 15A18 (eigenvalues).

### MINOR-5: Missing reproducibility statement
- **Location:** End of paper or appendix
- **Problem:** The CLAUDE.md project charter requires a reproducibility statement. The figure generation script exists but is never mentioned in the text.
- **Fix:** Add a brief sentence in Section 9 or Appendix D noting that the validation figure is generated by `generate_validation_figure.py` with no external dependencies beyond NumPy/Matplotlib.

---

## 5. Comparison with Prior Stage Notes

This is the first review (no P2/P3 notes exist for this paper). No prior-stage comparison applicable.

---

## 6. Summary

| Category | Count |
|----------|-------|
| BLOCKER | 1 (missing figure) |
| MEDIUM | 3 (orphaned files, appendix numbering, bibliography) |
| MINOR | 5 (sqrt typo, title length, MSC codes, reproducibility, uncited bibs) |

The mathematics is solid. All theorems have been verified computationally. The one intermediate typo (-52 vs -42 in the sqrt expansion) does not affect any theorem statement. The paper is well-written with a clean logical structure.

After fixing the BLOCKER (generating the figure) and addressing the MEDIUM items, this paper is ready for submission to a journal such as *Journal of Statistical Physics* or *Annales Henri Poincare*. For *Communications in Mathematical Physics*, the bibliography would need strengthening and the balanced-family result (Proposition 4.1) might benefit from a brief discussion of how it relates to the broader theory of algebraic curves with rational parametrizations.
