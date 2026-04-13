# P4 Editorial Review -- 2026-04-04

**Paper:** Scan Error Profiles on Prefix Partitions and Boundary-Controlled Convergence Rates
**Target journal:** Ergodic Theory and Dynamical Systems (ETDS)
**Reviewer role:** Gate 3 independent editorial review (handling editor / senior referee simulation)

---

## 1. Decision

**MAJOR_REVISION**

The mathematical content is correct and the proofs are complete, but the paper in its current form falls short of ETDS publication standards on several fronts: (i) the novelty claim is overstated relative to the actual technical difficulty; (ii) the bibliography is broken and woefully incomplete; (iii) the paper lacks engagement with the existing literature on Bayes risk decay, filtration-based classification, and symbolic boundary growth; (iv) the "Tanaka--Stokes" terminology is misleading; and (v) several structural and editorial issues must be resolved before submission.

---

## 2. Main Mathematical Assessment

### 2.1 Are theorems correctly stated with all hypotheses?

**Verdict: YES, with qualifications.**

All theorems have their hypotheses stated and the proofs are logically complete. The following notes apply:

- **Proposition 2.1 (clopen cylinder unions):** Correct. The equivalence of (1)-(3) is elementary and the proof is clean.
- **Proposition 3.2 (cylinder decomposition):** Correct. This is the standard decomposition of Bayes risk into atom-level contributions. All steps are verified.
- **Proposition 3.3 (Bayes-optimality):** Correct. Part (1) follows from the cylinder decomposition. Part (2) is a standard approximation bound. The tie-breaking convention (threshold at 1/2 with >= rather than >) is adopted implicitly; this is fine but should be noted explicitly since it affects the classifier on atoms with $p_C = 1/2$.
- **Corollary 3.4:** Correct. The monotonicity argument is clean. The zero-error characterization uses finiteness of $\mathcal{F}_m$ correctly.
- **Theorem 4.1 (Tanaka--Stokes representation):** Correct. The discrete Tanaka identity is a tautology (telescoping + splitting absolute value increments). The martingale property is used correctly to zero out the signed-increment sum. The convergence statement uses Levy's martingale convergence theorem (not Walters Chapter 5, which is about ergodic theory -- see issue below).
- **Theorem 5.2 (boundary-dimension upper bound):** Correct. The bound $\min\{a,b\} \le a+b$ restricted to $\le \mu(C)$ is used properly. The passage to the dimension exponent is routine.
- **Theorem 5.3 (exact rate law):** Correct. Both bounds are verified line by line. The lower bound uses the thickness hypothesis correctly. The upper bound uses $\min\{p,1-p\} \le 1/2$.

### 2.2 Are proofs complete or do they rely on unstated assumptions?

**Verdict: Proofs are complete.** No unstated assumptions are used. However:

- The discrete Tanaka identity (lines 395-412) is stated without proof. It is indeed a tautology (just rearranging a telescoping sum), but the paper should either prove it in one line or give a reference. Currently it is presented as a known fact with no citation.
- The claim "$p_m \to \mathbf{1}_{\mathsf{P}}$ almost surely and in $L^1$" (line 439) is attributed to Walters Chapter 5, which covers the ergodic theorem, not the martingale convergence theorem. The correct reference is Levy's upward theorem / Doob's martingale convergence theorem. This is a citation error, not a mathematical error.

### 2.3 Is the main theorem genuinely new?

**Verdict: PARTIALLY.** This is the most serious concern.

The cylinder decomposition (Prop 3.2) and Bayes-optimal characterization (Prop 3.3) are textbook-level results about Bayes risk on finite partitions. They appear in standard nonparametric estimation texts (Tsybakov, Devroye-Gyorfi-Lugosi) and in the pattern recognition literature. The paper cites Tsybakov but does not explain what is new beyond the standard theory.

The "Tanaka--Stokes representation" (Theorem 4.1) is the paper's most distinctive claim. However:
- The identity $\varepsilon_m = \varepsilon_0 - \mathbb{E}[L_m^{1/2}]$ is a direct rewriting of $\mathbb{E}|p_m - 1/2| = |p_0 - 1/2| + \mathbb{E}[L_m^{1/2}]$, which itself is the expectation of the discrete Tanaka formula for submartingales (specifically, the submartingale $|p_m - 1/2|$). The discrete Tanaka formula for martingales is well established; see e.g., Revuz-Yor for continuous time, and various discrete-time treatments in stochastic calculus texts.
- The novelty here is the *application* of discrete Tanaka to the Bayes risk decay in the prefix filtration setting. This is a legitimate observation but calling it a "Tanaka--Stokes representation" is a stretch. The "Stokes" part has no mathematical content in this paper -- the remark on line 449 merely asserts an analogy without justification.

The boundary-dimension theorems (5.2, 5.3) are straightforward bounds once the cylinder decomposition is in place. The two-sided law under the thickness hypothesis is clean but not deep.

**Bottom line:** The paper assembles known ingredients (Bayes risk on partitions, martingale convergence, discrete Tanaka formula) into a coherent framework applied to prefix filtrations. This is a valid organizational contribution, but the paper must honestly position itself as such, rather than claiming the individual results are new theorems.

---

## 3. Editorial Blockers

### 3.1 Abstract vs. actual content

The abstract is mostly accurate but oversells: the phrase "Tanaka--Stokes representation" suggests a result at the level of Tanaka's formula or Stokes' theorem, when the actual content is an application of the discrete Tanaka identity. The abstract should be toned down.

### 3.2 Introduction: reader-friendliness for ETDS audience

**BLOCKER.** The introduction does not engage with any prior work beyond textbook references. An ETDS reader will immediately ask:
- How does this relate to the large literature on symbolic dynamics and boundary sets (e.g., Fischer, Krieger, Boyle-Tuncel)?
- How does this relate to the Bayes risk decay literature in statistical learning theory?
- What is the relationship to entropy and the Shannon-McMillan-Breiman theorem, which also controls cylinder measure decay?
- Is there a connection to the notion of "boundary" in the sense of Furstenberg or Kaimanovich?

The introduction currently says nothing about any of these. This is a hard blocker for an ETDS submission.

### 3.3 Structural problems

1. **Bibliography is broken.** The `\bibliography` path (line 671) uses `../../2026_golden_ratio.../references` which does not resolve from the paper's directory. The correct relative path is `../../../theory/2026_golden_ratio.../references`. Consequently, the compiled PDF has no bibliography at all -- every citation appears as `[?]`. This is a hard blocker.

2. **Bibliography is inherited from a monograph.** The paper cites only 5 works (Walters, Lind-Marcus, Cover-Thomas, Tsybakov, Morse-Hedlund). For an ETDS submission this is drastically insufficient. A typical ETDS paper has 20-40 references. Missing references include:
   - Doob (martingale convergence)
   - Revuz-Yor or Chung-Walsh (Tanaka formula)
   - Devroye-Gyorfi-Lugosi (classification / Bayes risk)
   - Any paper on symbolic boundary sets or coded systems
   - Any paper on filtration convergence rates in dynamical systems
   - Any recent ETDS paper to show awareness of the journal's current scope

3. **No author.** Line 32: `\author{}` is empty. This must be filled before submission.

4. **Section ordering.** Examples (Section 6) come after the boundary-rate theorems (Section 5) and Discussion (Section 7). This is acceptable but the golden-mean example would be better placed immediately after the boundary theorems it illustrates, possibly as a subsection of Section 5.

5. **Label namespace pollution.** Labels like `prop:spg-decidable-clopen`, `def:spg-scan-error-profile`, etc., retain the `spg-` prefix from the parent monograph. These should be cleaned for a standalone paper.

6. **The paper has no section numbering for "Examples and Specializations" examples.** Example 6.1 has a proof block, which is nonstandard -- examples typically do not have formal proofs. Either call it a proposition or drop the proof environment and say "This follows directly from..."

### 3.4 Bibliography assessment

**BLOCKER.** As noted above: 5 references is far below ETDS norms. The bibliography does not demonstrate awareness of:
- The classification/Bayes risk literature beyond Tsybakov
- Symbolic dynamics literature on sofic/coded systems and boundary sets
- Martingale local time in discrete settings
- Any ETDS paper from the last decade

---

## 4. Specific Cut/Merge/Rewrite Recommendations

### Item 1 [BLOCKER] -- Broken bibliography path
- **Location:** Line 671, `\bibliography{...}`
- **Problem:** The relative path `../../2026_golden_ratio.../references` does not resolve. The PDF has no bibliography.
- **Fix:** Either (a) fix the relative path to `../../../theory/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence/references`, or (b) copy the needed .bib entries into a local `references.bib` file. Option (b) is strongly preferred for a standalone paper.

### Item 2 [BLOCKER] -- Missing literature engagement
- **Location:** Section 1 (Introduction), entire bibliography
- **Problem:** The paper cites only 5 works, all textbooks. There is zero engagement with the research literature. An ETDS referee will reject on this basis alone.
- **Fix:** Add a "Related work" paragraph to the introduction covering: (a) Bayes risk on partitions and its decay (Devroye-Gyorfi-Lugosi, Audibert-Tsybakov); (b) symbolic dynamics boundary sets (Boyle, Krieger, Fischer); (c) martingale convergence rates in ergodic theory; (d) discrete Tanaka formula (cite an appropriate source). Expand the bibliography to at least 15-20 entries.

### Item 3 [BLOCKER] -- Misleading "Tanaka--Stokes" terminology
- **Location:** Theorem 4.1 title, abstract, introduction, Remark after Theorem 4.1
- **Problem:** The name "Tanaka--Stokes" suggests a connection to Stokes' theorem that does not exist in this paper. The "Stokes" part is justified only by a vague analogy in the Remark (lines 448-453). This will confuse or annoy an ETDS referee.
- **Fix:** Either (a) rename to "Tanaka representation" or "discrete Tanaka representation" and drop the Stokes claim, or (b) prove an actual Stokes-type boundary integral identity (which would require genuinely new content). Option (a) is the realistic path.

### Item 4 [MEDIUM] -- Misattributed citation for martingale convergence
- **Location:** Line 439-440, proof of Theorem 4.1
- **Problem:** The martingale convergence $p_m \to \mathbf{1}_{\mathsf{P}}$ a.s. is attributed to "Walters, Chapter 5," which covers the pointwise ergodic theorem, not the martingale convergence theorem. Levy's upward theorem is the correct result.
- **Fix:** Replace citation with Doob's martingale convergence theorem (e.g., Durrett, Probability: Theory and Examples, or Williams, Probability with Martingales).

### Item 5 [MEDIUM] -- Novelty positioning is dishonest
- **Location:** Introduction (lines 77-101), abstract
- **Problem:** The "four deliverables" are listed as if they are all new results. Deliverables 1-2 (cylinder decomposition, Bayes rule) are textbook material. This will undermine credibility with a referee.
- **Fix:** Explicitly state in the introduction that the cylinder decomposition and Bayes characterization are well known (with proper citations) and that the paper's contributions are: (a) the discrete Tanaka representation applied to this setting, and (b) the boundary-cylinder rate laws.

### Item 6 [MEDIUM] -- Tie-breaking convention at $p_C = 1/2$
- **Location:** Proposition 3.3, line 266-267
- **Problem:** The classifier $\mathsf{P}_m^\star := \{x : p_m(x) \ge 1/2\}$ uses $\ge$ for the threshold. On atoms where $p_C = 1/2$ exactly, both inclusion and exclusion yield the same error. This is fine but should be stated explicitly (e.g., "the tie-breaking direction is irrelevant since $\min\{p_C, 1-p_C\}$ is the same either way").
- **Fix:** Add a one-sentence remark after the definition of $\mathsf{P}_m^\star$.

### Item 7 [MEDIUM] -- Discrete Tanaka identity needs a reference or proof
- **Location:** Lines 395-412 in the proof of Theorem 4.1
- **Problem:** The discrete Tanaka identity is stated as a known fact but not proved or cited. While it is indeed a tautology (the right-hand side telescopes to the left-hand side), a referee may object.
- **Fix:** Either add a one-line proof ("this follows by summing the tautological identity $|x_{k+1}-a| = |x_k - a| + \text{sgn}(x_k - a)(x_{k+1}-x_k) + (\text{remainder})$") or cite a reference for the discrete Tanaka formula.

### Item 8 [MEDIUM] -- Missing $\mathcal{F}_0$ definition
- **Location:** Section 4, line 342
- **Problem:** $p_0 := \mu(\mathsf{P})$ is defined as a constant, implicitly taking $\mathcal{F}_0$ as the trivial sigma-algebra. But $\mathcal{F}_0$ is never formally defined -- the filtration $(\mathcal{F}_m)_{m \ge 1}$ starts at $m=1$ in Section 2.
- **Fix:** Extend the filtration definition to include $\mathcal{F}_0 := \{\emptyset, X\}$ in Section 2.2.

### Item 9 [MINOR] -- Label namespace cleanup
- **Location:** All labels (e.g., `prop:spg-decidable-clopen`, `def:spg-scan-error-profile`)
- **Problem:** The `spg-` prefix is an artifact from the parent monograph and has no meaning in this standalone paper.
- **Fix:** Remove the `spg-` prefix from all labels, or replace with a meaningful prefix.

### Item 10 [MINOR] -- Example 6.1 has a proof environment
- **Location:** Lines 621-624
- **Problem:** Placing a `\begin{proof}...\end{proof}` block after an example is nonstandard. The content is trivially obvious.
- **Fix:** Either (a) fold the explanation into the example body, or (b) relabel as a Proposition.

### Item 11 [MINOR] -- Empty author field
- **Location:** Line 32
- **Problem:** `\author{}` is blank.
- **Fix:** Fill in author name(s) and affiliation(s).

### Item 12 [MINOR] -- Discussion section is thin
- **Location:** Section 7 (lines 656-668)
- **Problem:** The discussion is only one paragraph and half of it is spent saying what the paper does *not* do. For ETDS, this should include: (a) open questions, (b) connections to entropy theory, (c) possible extensions to non-binary alphabets or continuous-time systems.
- **Fix:** Expand to 3-4 paragraphs with substantive forward-looking content.

### Item 13 [MINOR] -- Table 1 placement
- **Location:** Lines 481-497
- **Problem:** The table summarizing rate regimes appears before the theorems that prove them. Consider moving it after both theorems, or at least after Theorem 5.2.
- **Fix:** Move Table 1 to after Theorem 5.3 or keep it as a summary at the start (acceptable but flag the forward references).

---

## 5. Comparison with Prior Stage Notes

### P1 Traceability notes (from PIPELINE.md)

The PIPELINE.md records the following blocking issues:
1. "No recent target-journal reconnaissance" -- **NOT RESOLVED.** The paper shows no evidence of surveying recent ETDS publications.
2. "No Lean linkage notes" -- **NOT RESOLVED.** No formal verification exists.
3. "Bibliography still inherited from master paper" -- **NOT RESOLVED.** The bibliography path is broken and the content is unchanged from the monograph.
4. "Source line anchors and Lean label attachments pending" -- **NOT RESOLVED.**

### P2/P3 notes

No P2 or P3 notes exist. The pipeline shows P2 and P3 as "pending." This means the paper has reached P4 review without completing P2 (Research Extension) or P3 (Journal-Fit Rewrite). This is irregular and explains many of the issues found.

### New issues introduced

Since no P2/P3 rewriting occurred, there are no regression issues. All problems are inherited from the original extraction.

---

## 6. Summary of Blockers

| # | Severity | Issue |
|---|----------|-------|
| 1 | BLOCKER | Bibliography path broken; PDF has no references |
| 2 | BLOCKER | Only 5 textbook citations; no engagement with research literature |
| 3 | BLOCKER | "Tanaka--Stokes" terminology is misleading; the Stokes part is unjustified |
| 4 | MEDIUM | Wrong citation for martingale convergence (Walters vs. Doob/Levy) |
| 5 | MEDIUM | Novelty oversold; textbook results presented as new |
| 6 | MEDIUM | Tie-breaking at $p_C = 1/2$ not discussed |
| 7 | MEDIUM | Discrete Tanaka identity used without proof or citation |
| 8 | MEDIUM | $\mathcal{F}_0$ never defined |
| 9 | MINOR | Label namespace pollution (spg- prefix) |
| 10 | MINOR | Proof environment after Example 6.1 |
| 11 | MINOR | Empty author field |
| 12 | MINOR | Discussion section too thin |
| 13 | MINOR | Table 1 placement (forward reference) |

---

## 7. Recommendation

**MAJOR_REVISION.** The mathematical core is sound but the paper is not ready for ETDS submission due to three hard blockers (broken bibliography, missing literature, misleading terminology) and five medium issues. The paper should return to P2 (Research Extension) to:

1. Fix the bibliography infrastructure and add 15+ research references.
2. Write a proper "Related work" discussion in the introduction.
3. Rename the "Tanaka--Stokes" result and honestly position the novelty.
4. Fix the martingale convergence citation.
5. Define $\mathcal{F}_0$ and address the minor structural issues.

After these fixes, a P3 (Journal-Fit Rewrite) pass should reshape the introduction and discussion for the ETDS audience before returning to P4.
