# P4 Editorial Review -- Gate 3 Independent Review

**Paper:** "Finite-Window Zeckendorf Fibers and the Discrete Thermodynamics of Fibonacci Partition Differences"
**Target journal:** Transactions of the American Mathematical Society (TAMS)
**Reviewer role:** Gate 3 independent editorial reviewer (Claude Opus 4.6)
**Date:** 2026-04-04
**Prior reviews used:** P4 Editorial Review (2026-03-30, decision: MINOR_REVISION), review_notes.txt (pre-revision), PIPELINE.md

---

## 1. Decision

**MAJOR_REVISION**

Rationale: The mathematical content is substantial and, if all issues are resolved, would constitute a credible TAMS-level contribution. However, there are two hard blockers (missing bibliography entry, gap in a proof) and several medium issues that together prevent a MINOR_REVISION verdict. None are fatal enough for REJECT.

---

## 2. Main Mathematical Blockers

### BLOCKER-1: Gap in proof of Hankel principalization (Theorem 7.2 / `thm:principalization`)

**Location:** `sec_chebotarev.tex`, lines 57--76 (proof of Theorem `thm:principalization`)

**Problem:** The proof argues: (i) $\mathcal{M}(P_q) \subseteq \mathrm{NullModes}(q)$, and (ii) both are free $\ZZ$-modules of rank $\kappa_q$, therefore they are equal. This does not follow. For $\ZZ$-modules, $A \subseteq B$ with $\mathrm{rank}(A) = \mathrm{rank}(B)$ implies only that $[B:A] < \infty$, not $[B:A] = 1$. The sublattice $\mathcal{M}(P_q)$ could be a proper finite-index sublattice of $\mathrm{NullModes}(q)$.

**Fix:** Either (a) verify computationally that for each $q = 9,\ldots,17$ the determinants of the two lattices agree (which would prove index 1), or (b) compute the Smith normal form of the matrix whose rows are the generators of $\mathcal{M}(P_q)$ expressed in a basis of $\mathrm{NullModes}(q)$ and verify the resulting diagonal entries are all $\pm 1$, or (c) explicitly state this as a computational verification rather than a pure proof. Since the claim is only made for nine specific values of $q$, option (a) or (b) should be straightforward. The current proof wording must be corrected regardless.

**Severity:** BLOCKER. The principalization theorem is the foundation on which Corollaries 7.3 and 7.4 rest, and indirectly underpins the irreducibility/Galois-group chain.

### BLOCKER-2: Missing bibliography entry (`DixonMortimer1996`)

**Location:** `sec_chebotarev.tex`, line 219; `sec_references.tex` (thebibliography)

**Problem:** The proof of Theorem `thm:galois-sd-window` cites `[DixonMortimer1996, Thm. 3.3A]` for Jordan's theorem. This entry is present in `references.bib` but is absent from the hand-written `\begin{thebibliography}` in `sec_references.tex`. Since the paper does not use BibTeX (see README.md), the citation will produce "[?]" in the compiled PDF. The log file confirms: `Citation 'DixonMortimer1996' on page 32 undefined`.

**Fix:** Add the entry for Dixon--Mortimer 1996 to `sec_references.tex`. This also increments the bibliography count from 12 to 13 (the cover letter already claims 13 references, so this may have been an omission during a prior edit).

**Severity:** BLOCKER. The Jordan-theorem citation is load-bearing for the Galois-group proof.

### MEDIUM-1: Theorem B as stated invokes a forward reference without qualification

**Location:** `sec_introduction.tex`, lines 46--54 (Theorem B statement)

**Problem:** Theorem B states "For $q \ge 2$ the Perron root of the finite-state collision kernel equals $\lambda_q$." But at the point of the introduction where Theorem B is stated, neither the collision kernel nor its Perron root has been defined. The formal version in Section 4 (`thm:all-q-transfer`) resolves this by referencing `thm:collision-kernel`, which comes later in Section 5. The named Theorem B in the introduction should either (a) not include this clause (deferring it to Theorem C's territory) or (b) add a brief forward-reference qualifier such as "of Section 5."

**Fix:** Append "(Section 5)" or "(Theorem C)" after "finite-state collision kernel" in the introduction statement of Theorem B, or move that clause to Theorem C. Currently Theorems B and C overlap in scope.

### MEDIUM-2: Scope overlap between Theorems B and C

**Location:** `sec_introduction.tex`, Theorems B and C

**Problem:** Theorem B already says "$\lambda_q$ is the Perron root of the finite-state collision kernel" and Theorem C says "$\lambda_q$ is the spectral radius of a nonnegative integer matrix of dimension polynomial in $q$; in particular, $\lambda_q$ is an algebraic integer." These are essentially the same assertion with different levels of precision. A TAMS referee would likely ask: what exactly does Theorem C prove that Theorem B does not? The answer is: the polynomial-size bound, the algebraicity conclusion, and the convex pressure. This should be made sharper in the introduction.

**Fix:** In Theorem B, drop the sentence about Perron roots entirely. In Theorem C, absorb it ("the Perron root equals $\lambda_q$") as the bridge statement. This sharpens both named theorems.

### MEDIUM-3: Non-rigorous characterization of $P_q$ as "minimal recurrence polynomial"

**Location:** `sec_chebotarev.tex`, Definition 7.1 (`def:resonance-polynomials`)

**Problem:** The definition says "$P_q(\lambda) \in \ZZ[\lambda]$ denotes the monic minimal recurrence polynomial of the sequence $m \mapsto S_q(m)$." But $S_q(m)$ is defined for $m \ge 1$ (or $m \ge 0$ by `thm:collision-kernel`), and the recurrence is certified only for $m \ge d_q + 2$ or similar (Table B.1 says "valid for $m \ge$" with values 9--15). The definition should specify either (a) the minimal annihilating polynomial of the full sequence starting from some explicit index, or (b) that the polynomial is the characteristic polynomial of the Hankel quotient $H_0^{-1}H_1$ for a suitable data window. As written, the definition is slightly informal for a rigorous Galois-theory section.

**Fix:** Add a sentence clarifying: "Concretely, $P_q$ is the minimal polynomial of the companion matrix of the linear recurrence satisfied by $(S_q(m))_{m \ge m_0(q)}$ with $m_0(q)$ as in Table B.1."

### MEDIUM-4: ChowSlattery2021 and ChowJones2024 bibliographic data discrepancies

**Location:** `sec_references.tex` vs. `references.bib`

**Problem:**
- `ChowSlattery2021` in `sec_references.tex` says: "On Fibonacci partitions, JNT 225 (2021), 310--326." The `.bib` file says: "On the Zeckendorf representation: exact formulas for restricted digit sums, JNT 229 (2021), 265--287." These are different titles, volumes, and page ranges. One of them is wrong.
- `ChowJones2024` in `sec_references.tex` says: "S. Chow and O. Jones, On the variance of the Fibonacci partition function, JNT 257 (2024), 341--353." The `.bib` says: "S. Chow and Reuben Jones, Variance of the Fibonacci representation function, Mathematika 70(2) (2024), e12245." These are different journals and metadata. "O. Jones" vs. "Reuben Jones" is also a discrepancy.
- `Sanna2025` in `sec_references.tex` says: "Discrete Anal. 2025:2." The `.bib` says: "Journal of Integer Sequences 28, Article 25.1.3." These are completely different journals.

**Fix:** Verify each reference against the actual published versions and correct `sec_references.tex`. These are serious metadata errors that a TAMS referee will catch immediately.

**Severity:** MEDIUM verging on BLOCKER. Fabricated or incorrect bibliographic metadata is a serious editorial issue.

### MEDIUM-5: Sanna's theorem is used as a black box without verifiable citation

**Location:** `sec_second_collision.tex`, Theorem `thm:all-q-transfer`, line 88--93

**Problem:** The transfer $T_q^\dagger(N) \asymp_q N^{(\log \lambda_q)/\log \varphi}$ is attributed to "Sanna's partition constant [Sanna2025]." The paper builds its entire moment-transfer architecture on this result. If the citation metadata is wrong (see MEDIUM-4 above), the external reference is unverifiable. Beyond the citation issue, the proof of Theorem `thm:all-q-transfer` uses the comparison $R(n)^q \le R^\dagger(n)^q \le 2^{q-1}(R(n)^q + R(n-1)^q)$ which gives $T_q^\dagger(N) \asymp_q \sum_{n<N} R(n)^q$. The constant in the asymptotic is absorbed into $\asymp_q$. But the claim that $\sum_{n<N} R(n)^q \asymp_q N^{(\log \lambda_q)/\log \varphi}$ is then attributed to Sanna. Since this is a load-bearing external result, the citation must be correct.

**Fix:** (1) Fix the Sanna2025 bibliographic entry. (2) State explicitly which theorem of Sanna's is being used (theorem number, not just the paper).

---

## 3. Editorial Blockers

### EDITORIAL-1: Abstract accuracy

The abstract accurately describes the content of the paper. It mentions Theorems A--F in compressed form, the Galois/Chebotarev arc, and the product density $1/20449$. The abstract is approximately 170 words, well under the 250-word TAMS limit. No overclaiming detected relative to the proven results.

**Verdict:** PASS (no action needed)

### EDITORIAL-2: Introduction structure

The introduction is well-structured: motivating question, six named theorems, related work, organization. The writing is clear and professional. The "related work" subsection properly positions the paper relative to Zeckendorf, Chow--Slattery, Chow--Jones, Sanna, and the symbolic-dynamics tradition.

One minor issue: the phrase "unexpectedly rigid" (line 18) was flagged by the prior P4 review as potential AI-voice. It remains in the manuscript.

**Verdict:** PASS with one MINOR flag (see MINOR-3 below)

### EDITORIAL-3: Section ordering and structural coherence

The section ordering is logical: Preliminaries -> Affine transfer (Thm A) -> Moment transfer (Thm B) -> Finite-state/pressure (Thm C--F) -> Entropy rates -> Galois/Chebotarev -> Conclusion -> Appendix A (transducer) -> Appendix B (certificates). The escalation ladder is clearly motivated and well-signposted.

Two files in the directory (`sec_rewriting.tex`, `sec_appendix_auxiliary.tex`) are NOT included in `main.tex` but are present in the directory. These do not interfere with compilation, but `sec_appendix_auxiliary.tex` line 9 references "Theorems A--G" while the paper only has A--F. This is a stale artifact.

**Verdict:** PASS structurally. MINOR cleanup needed for orphan files.

### EDITORIAL-4: Bibliography scope, recency, and journal coverage

The bibliography has 12 entries (should be 13 after BLOCKER-2 fix). For a TAMS paper of ~40 pages, 13 references is lean. This is acceptable if the paper is genuinely self-contained, which it largely is. However:

- Missing: Miller--Takloo-Bighash (2006) or Grabner--Tichy (1992) for Zeckendorf combinatorics context.
- Missing: Any reference for the Chebotarev density theorem beyond Neukirch's textbook. While Neukirch is standard, a more specific reference (e.g., Lenstra's survey, or Serre's "Lectures on $N_X(p)$") would strengthen the arithmetic section.
- Recency: References span 1952--2025. The bulk of the substantive references (Chow--Slattery 2021, Chow--Jones 2024, Sanna 2025) are recent, which is appropriate.
- The Dembo--Zeitouni and Cover--Thomas citations are for background only and are used appropriately.

**Verdict:** Acceptable but thin. See MINOR-4 below.

### EDITORIAL-5: LaTeX compilation

The log file shows all cross-references and citations are undefined. This is because only one pdflatex pass was run. A second pass would resolve cross-references. However, the `DixonMortimer1996` citation would remain undefined regardless (BLOCKER-2). After fixing BLOCKER-2 and running two passes, compilation should be clean.

**Verdict:** Conditional PASS (fix BLOCKER-2, run two passes)

### EDITORIAL-6: Author attribution

The author is listed as "The Omega Project" with affiliation "The Omega Institute for Mathematical Research." For initial TAMS submission, this is technically acceptable (authors can use pseudonyms/group names at submission). However, TAMS editorial policy may require named individual authors before peer review begins. This is flagged as a risk but not a blocker for the manuscript itself.

---

## 4. Specific Cut/Merge/Rewrite Recommendations

### BLOCKER-2-FIX: Add DixonMortimer1996 to thebibliography

**Location:** `sec_references.tex`, insert after the Dembo--Zeitouni entry (alphabetical order)
**Problem:** Missing bibliography entry for a cited source
**Fix:** Add:
```
\bibitem{DixonMortimer1996}
J.~D.~Dixon and B.~Mortimer,
\textit{Permutation Groups},
Graduate Texts in Mathematics, vol.~163, Springer-Verlag, New York, 1996.
```

### BLOCKER-1-FIX: Repair principalization proof

**Location:** `sec_chebotarev.tex`, lines 70--76
**Problem:** Equal-rank conclusion is insufficient for $\ZZ$-module equality
**Fix:** Replace the sentence "Since $\mathcal{M}(P_q) \subseteq \mathrm{NullModes}(q)$ and both have the same rank, they are equal." with a computational verification. For example: "To verify that the inclusion has index 1, we compute the Smith normal form of the matrix expressing a $\ZZ$-basis of $\mathcal{M}(P_q)$ in a $\ZZ$-basis of $\mathrm{NullModes}(q)$; for each $q = 9,\ldots,17$, all invariant factors equal 1." Alternatively, verify this via determinants.

### MEDIUM-4-FIX: Correct all bibliographic metadata

**Location:** `sec_references.tex`, entries for ChowSlattery2021, ChowJones2024, Sanna2025
**Problem:** Journal names, volumes, page ranges, author initials are inconsistent with the .bib file and possibly with the actual publications
**Fix:** Look up each paper in MathSciNet/zbMATH and correct `sec_references.tex` to match the actual publication data. The `.bib` file and `sec_references.tex` must be consistent. If only `sec_references.tex` is used, it alone must be correct.

### MEDIUM-2-FIX: Sharpen Theorems B and C in the introduction

**Location:** `sec_introduction.tex`, lines 46--62
**Problem:** Scope overlap
**Fix:** In Theorem B, remove the sentence "For $q \ge 2$ the Perron root of the finite-state collision kernel equals $\lambda_q$." In Theorem C, add as the first sentence: "For $q \ge 2$, the Perron root of the finite-state collision kernel equals $\lambda_q$." This makes the escalation cleaner.

### MINOR-1: Corollary `cor:visible-band` is not a proper corollary statement

**Location:** `sec_ledger.tex`, lines 20--52
**Problem:** The corollary begins by defining $V_m(\varepsilon)$ but does not have a "then" clause syntactically. The display after "Then" is the content, but the corollary reads as: "For every $\varepsilon > 0$, [definition of $V_m$]. Then [probability statement]." This is grammatically correct but the "For every $\varepsilon > 0$" is dangling before the definition display.
**Fix:** Restructure as: "For every $\varepsilon > 0$, define $V_m(\varepsilon) := \ldots$. Then $p_m(V_m(\varepsilon)) = \ldots$."

### MINOR-2: Orphan `sec_appendix_auxiliary.tex` references Theorem G

**Location:** `sec_appendix_auxiliary.tex`, line 9
**Problem:** References "Theorems A--G" but the paper only defines A--F
**Fix:** Either delete the file from the submission directory or correct the reference. Since this file is excluded from the compiled paper, deletion is cleanest for submission.

### MINOR-3: "Unexpectedly rigid" phrasing

**Location:** `sec_introduction.tex`, line 18
**Problem:** Flagged by prior P4 review as potential AI-generated-sounding phrasing
**Fix:** Replace "unexpectedly rigid" with "more structured than one might expect" or simply "rigid."

### MINOR-4: Bibliography could cite Miller--Takloo-Bighash or Grabner--Tichy for broader Zeckendorf context

**Location:** `sec_references.tex`
**Problem:** The bibliography is lean for a TAMS paper
**Fix:** Consider adding 2--3 more references to situate the work within the broader Zeckendorf combinatorics literature. This is optional but would strengthen the paper's positioning.

### MINOR-5: Cover letter says 13 references; current bibliography has 12

**Location:** `cover_letter_tams.txt`, line 47
**Problem:** Count mismatch (becomes correct after BLOCKER-2 fix)
**Fix:** Verify the count after adding DixonMortimer1996.

### MINOR-6: `\Cref` formatting with `noabbrev` option

**Location:** Throughout; `main.tex` line 12
**Problem:** The `cleveref` package is loaded with `[nameinlink,noabbrev]`. This means cross-references will be spelled out as "Theorem," "Proposition," etc. in full. Some instances in the text manually write "Theorem~\ref{...}" while others use `\Cref{...}`. Inconsistent usage may produce "Theorem Theorem 3.1" if `\Cref` is used after a manual "Theorem" prefix.
**Fix:** Search for instances of `Theorem~\ref`, `Lemma~\ref`, etc. that should be plain `\Cref` calls (or conversely, ensure `\Cref` is not preceded by the theorem-type word).

---

## 5. Comparison with Prior Stage Notes

### P4 (2026-03-30) MINOR_REVISION issues

| # | Issue | Status |
|---|-------|--------|
| 1 | $\Delta_q$ notation overloaded | RESOLVED: renamed to $\kappa_q$ in chebotarev section |
| 2 | Remark theorem style | RESOLVED: changed to `\theoremstyle{remark}` |
| 3 | Author affiliation/funding | RESOLVED: `\author`, `\address`, `\thanks` present |
| 4 | $m_0(q)$ offset discrepancy | RESOLVED: changed to $m \ge 0$ |
| 5 | Quotient variable $q$ renamed to $b$ | RESOLVED: `prop:single-overflow` uses $b$ |
| 6 | "Then" connector in `cor:visible-band` | PARTIALLY RESOLVED: the grammatical issue remains (see MINOR-1) |
| 7 | `rem:lambda-one` added | RESOLVED |
| 8 | `cor:log-density-additivity` demoted to remark | RESOLVED |

### New issues introduced since P4/P5

1. **BLOCKER-1** (principalization proof gap): This was not flagged by the prior P4 review. The equal-rank-implies-equality argument was present in the original and was not caught.
2. **BLOCKER-2** (missing DixonMortimer bibitem): This may have been introduced during the P3 bibliography cleanup (4 entries added, 4 removed). The `.bib` file has the entry but the handwritten `thebibliography` does not.
3. **MEDIUM-4** (bibliography metadata errors): These may have been present since P3 or earlier. The discrepancies between `.bib` and `sec_references.tex` suggest the two were not synchronized.

### review_notes.txt issues

The pre-revision review (review_notes.txt) identified 6 major weaknesses. Status:

| # | Issue | Status |
|---|-------|--------|
| 1 | Theorem chain weaker than source material | RESOLVED: Full A--F chain with Galois/Chebotarev |
| 2 | Information section incomplete | RESOLVED: sec_ledger has Renyi spectrum and collision entropy rate |
| 3 | Rewriting section incomplete | RESOLVED by exclusion: sec_rewriting excluded from submission (not \input'd) |
| 4 | Moment section missing recoverability | PARTIALLY RESOLVED: capacity/Stieltjes inversion is in sec_appendix_auxiliary (excluded from main paper). The main text has the kernel realization and pressure geometry but not the Hankel recovery theorems. This is an acceptable scope cut for TAMS. |
| 5 | Arithmetic section overclaimed | RESOLVED: Jordan certificates added for q=12,14,15,16,17; claims restricted to audited window |
| 6 | Paper did not read like TAMS submission | RESOLVED: professional register, proper front matter, complete proofs |

---

## 6. Novelty Assessment

**Is the main theorem genuinely new?** Yes. The connection between finite-window Zeckendorf fiber multiplicities and Fibonacci-lag partition differences (Theorem A) appears to be new. The transfer of Sanna's partition constants to collision moments (Theorem B) is new. The finite-state kernel realization and the resulting algebraicity of $\lambda_q$ (Theorem C) is new. The discrete thermodynamic formalism (Theorems D--F) applied to this specific setting is new. The Galois-group and Chebotarev results for the arithmetic window (Section 7) are new.

**Is it a repackaging?** No. While individual techniques (Fourier inversion, Perron--Frobenius, Chebotarev density) are standard, the combination and the specific application to Zeckendorf fiber spectra is original. The escalation from a combinatorial identity to a complete thermodynamic formalism with certified arithmetic content is a genuine contribution.

**TAMS suitability:** The paper combines techniques from combinatorial number theory, symbolic dynamics, and algebraic number theory in a way that is characteristic of TAMS publications. The depth and breadth are appropriate. The paper would benefit from addressing the issues above to ensure it meets the TAMS standard for rigor.

---

## 7. Summary of Issues by Severity

### BLOCKER (must fix before submission)
1. **BLOCKER-1:** Principalization proof has a lattice-index gap
2. **BLOCKER-2:** DixonMortimer1996 missing from thebibliography

### MEDIUM (should fix, may draw referee objection)
3. **MEDIUM-1:** Theorem B forward-references undefined objects
4. **MEDIUM-2:** Theorems B and C overlap in scope
5. **MEDIUM-3:** "Minimal recurrence polynomial" definition slightly informal
6. **MEDIUM-4:** Three bibliography entries have wrong metadata
7. **MEDIUM-5:** Sanna citation needs theorem-level specificity

### MINOR (polish)
8. **MINOR-1:** `cor:visible-band` grammatical structure
9. **MINOR-2:** Orphan file references Theorem G
10. **MINOR-3:** "Unexpectedly rigid" phrasing
11. **MINOR-4:** Bibliography could be slightly expanded
12. **MINOR-5:** Cover letter reference count (auto-fixes with BLOCKER-2)
13. **MINOR-6:** Inconsistent `\Cref` vs manual `\ref` usage

---

## 8. Top-3 Blockers for TRACK_BOARD

1. Principalization proof gap (BLOCKER-1): lattice-index argument is insufficient
2. Missing DixonMortimer1996 bibliography entry (BLOCKER-2): produces [?] in compiled PDF
3. Bibliography metadata errors (MEDIUM-4): three entries have wrong journal/volume/page data
