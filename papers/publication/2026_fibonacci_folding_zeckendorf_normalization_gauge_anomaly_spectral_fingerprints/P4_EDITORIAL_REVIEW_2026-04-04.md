# P4 Editorial Review -- 2026-04-04

**Paper:** Fibonacci Folding under Zeckendorf Normalization: Multiscale Consistency, a Gauge-Anomaly Constant Law, and Generating-Function Spectral Fingerprints

**Target journal:** Not specified in manuscript. Assessed for a strong combinatorics / number theory journal (e.g., *Journal of Combinatorial Theory Ser. A*, *Advances in Applied Mathematics*, *Ergodic Theory and Dynamical Systems*).

**Review round:** First (R1).

---

## 1. Decision

**MAJOR_REVISION**

The paper contains a genuinely interesting collection of results connecting Zeckendorf normalization, symbolic dynamics, and spectral theory. The core mathematical content is computationally verified and internally consistent. However, the manuscript has critical structural deficiencies that would lead to immediate desk rejection at any serious journal: (a) 14 out of 18 formal statements lack proofs, (b) the bibliography contains only 1 citation actually used in the text, and (c) Sections 7--8 feel grafted on with insufficient motivation. These are fixable problems, but they require substantial work.

---

## 2. Main Mathematical Blockers

### 2.1 Massive proof deficit -- BLOCKER

The paper states 10 theorems, 7 propositions, and 1 lemma (18 total formal statements). Of these, only 4 have proof environments:

| Statement | Has proof? | Notes |
|-----------|-----------|-------|
| Prop 3.1 (idempotent, surjective) | No | Informal paragraph after App A, not a proof environment |
| Lemma 3.2 (strict commutation) | **Yes** | Complete |
| Prop 4.1 (extensive worst case) | No | Remark gives explicit family but no formal proof |
| Prop 4.2 (no bounded tail patch) | No | No proof at all |
| Thm 4.1 (bulk joint law) | No | Remark outlines sofic derivation; not a proof |
| Thm 4.2 (LLN and CLT) | No | Remark discusses tilted transfer matrix; not a proof |
| Thm 4.3 (autocovariance and PSD) | No | Remark discusses consistency; not a proof |
| Prop 5.1 (sofic model) | **Yes** | Construction given |
| Thm 5.1 (conjugacy m>=3) | No | Deferred to App C, which gives only a 3-line sketch |
| Thm 5.2 (m=2 degeneracy) | No | Deferred to App C, which gives only a 2-line sketch |
| Thm 6.1 (fourth-order recurrence) | No | Deferred to App D sketch |
| Thm 6.2 (discriminant factorization) | No | App D says "direct symbolic computation" |
| Thm 6.3 (weight stats LLN/CLT) | No | No proof, no sketch, no reference |
| Prop 7.1 (q=2 fingerprint) | No | No proof |
| Thm 8.1 (information ledger) | No | No proof |
| Thm 8.2 (union bound) | No | No proof |
| Prop A.1 (termination) | **Yes** | Complete |
| Prop A.2 (confluence) | **Yes** | Proof sketch citing ShallitShan2023 |

**Verdict:** The paper reads as an extended research announcement, not a journal article. A journal submission requires proofs of all stated theorems.

### 2.2 Specific proof gaps that are non-trivial

- **Theorem 4.1 (bulk joint law):** The claim that the Parry measure on the given 4-state edge shift produces the stated joint law requires proving that the sofic presentation in Remark 4.2 is correct. The remark asserts the labeled-edge structure but does not derive it from the definitions. This is the central statistical result of the paper and must have a complete proof.

- **Proposition 4.2 (no bounded tail patch):** This is stated without proof. The assertion that no bounded-memory correction can uniformly eliminate the anomaly is a meaningful negative result that needs a formal argument. A counting or information-theoretic argument should be provided.

- **Theorem 5.1 (conjugacy for m>=3):** Appendix C states that "the labeled graph admits a finite synchronization delay" and "after observing a block of labels of length m-1, the underlying vertex path becomes uniquely determined." This is a sketch at best. A proper proof must verify that the graph is right-resolving after delay m-1 and that the inverse block code is well-defined. The claim that Psi_m can be chosen with memory m-1 needs justification.

- **Theorem 6.3 (weight stats):** This theorem states a LLN, CLT, and large deviation principle for |X|_1 under the pushforward measure w_m. There is no proof, no sketch, and no appendix reference. The LDP claim in particular requires identifying a rate function. This is the weakest-supported statement in the paper.

- **Theorem 8.1 (information ledger):** This is a Shannon-entropy decomposition. The proof is a standard calculation (expand H(mu) via the fiber structure), but it must be written out. A reviewer will not accept a theorem with no proof even if it is "standard."

- **Theorem 8.2 (union bound and budgets):** The union bound itself is trivial, but the asymptotic budget claim requires specifying the scaling regime and verifying the conditions. The quantities T_m, nu_m, varepsilon_m, C_m, h_2(u) are introduced in the theorem statement without prior definition. This section reads as if it belongs to a different paper.

### 2.3 Are theorems correctly stated with all hypotheses?

- **Theorem 4.1:** The "bulk" regime is described informally as "k -> infinity and m-k -> infinity" but the theorem statement says "the bulk joint distribution of (X,Y) is [table]" without specifying the limiting regime precisely. The theorem should state: "For fixed k, as m -> infinity with k/m -> alpha in (0,1), the joint distribution of (X,Y) converges to..." or give the precise stationary-measure interpretation.

- **Theorem 4.2 (LLN/CLT):** The sum G_m is defined in subsection 4.4 as involving the "stationary discrepancy indicator process in the bulk." But the theorem claims almost-sure convergence and a CLT. The a.s. convergence needs a probability space. Under what measure? The uniform measure on Omega_{m+1} for each m, or the stationary measure on the bi-infinite shift? This conflation between finite-window and infinite-sequence perspectives is present throughout Section 4 and must be resolved.

- **Theorem 8.2:** The quantities nu_m, T_m, nu_{u,m}, h_2(u), varepsilon_m, C_m are all introduced in the theorem statement itself rather than in preceding definitions. This makes the theorem nearly unreadable.

### 2.4 Novelty assessment

The core results (Sections 3--4) are genuinely new. I am not aware of prior work computing the exact gauge anomaly for Fibonacci/Zeckendorf folding at this level of detail. The sofic presentation and spectral analysis are solid contributions. The partition-function analysis (Section 6) is interesting but feels like a collection of computations rather than a theorem with conceptual depth.

The "discriminant fingerprint" (Section 7) and "information ledger" (Section 8) are shallow additions. Section 7 introduces a definition, computes one example (q=2 gives 37), and makes a vague connection to Chebotarev density. Section 8 proves a standard entropy decomposition and a union bound. These sections dilute the paper's focus without adding proportionate depth.

### 2.5 Computational verification

All numerical claims that the paper's scripts verify pass correctly:
- Sofic joint law: PASS (all 4 probabilities match)
- Spectrum and CLT consistency: PASS (autocovariances match to j=59, variance=118/243, PSD formula correct, S(0) matches)
- Discriminant factorization: PASS (quartic disc, cubic root y_LY, P2 disc=148, sf=37)
- Worst-case family: PASS (G_m = m for m=1..400)

Additional independent verification performed during this review:
- Proposition 3.1 (idempotence, surjectivity): verified for m=1..7 by exhaustive enumeration
- Lemma 3.2 (strict commutation): verified for m=1..6 by exhaustive enumeration
- Proposition 4.2 (non-patchability): verified by counterexample for ell=1..4
- Information ledger identity (Theorem 8.1): verified numerically for m=1..7 with random distributions
- Partition function recurrence (Theorem 6.1): verified for m=4..12 by direct computation
- Weight statistics LLN (Theorem 6.3): convergence to 5/18 confirmed for m=1..13

**No fabricated or unverifiable claims detected.** All stated numerical constants are correct.

---

## 3. Editorial Blockers

### 3.1 Bibliography is critically underdeveloped -- BLOCKER

The paper cites exactly **1 source** in the body text (ShallitShan2023). The .bib file contains 4 entries, of which 3 are unused (Lekkerkerker1952, LindMarcus1995, LeeYang1952).

A paper touching Zeckendorf representations, Fibonacci numeration, golden-mean shifts, sofic shifts, sliding block codes, Lee-Yang theory, transfer matrices, and Shannon entropy must cite the relevant literature. At minimum:

- **Zeckendorf representations:** Zeckendorf (1972), Lekkerkerker (1952) [already in bib but unused], Fraenkel (1985), Brown (1964)
- **Fibonacci numeration and automata:** Shallit (various), Berstel (2001), Frougny (1992)
- **Symbolic dynamics / sofic shifts:** Lind-Marcus (1995) [already in bib but unused], Kitchens (1998), Weiss (1973)
- **Transfer matrices and thermodynamic formalism:** Parry-Pollicott (1990), Ruelle (2004), Bowen (2008)
- **Lee-Yang theory:** Lee-Yang (1952) [already in bib but unused], Ruelle (2010), Lebowitz-Penrose (1968)
- **CLTs for Markov chains:** Billingsley (1961), Gordin (1969), or any standard reference
- **Information theory / entropy decomposition:** Cover-Thomas (2006)

The paper must position itself relative to existing work on Fibonacci representations in combinatorics on words, on multiscale analysis in symbolic dynamics, and on transfer-matrix spectral methods. Currently it exists in a citation vacuum.

### 3.2 Abstract is accurate but overloaded

The abstract is 1 sentence (plus 6 sub-claims). It is technically accurate -- every claim (i)--(vi) is supported by the body -- but it reads like a laundry list rather than a scientific abstract. The abstract should lead with the main conceptual contribution (the gauge anomaly framework and its exact constants) and relegate the partition function and fingerprint results to a secondary clause.

### 3.3 Introduction lacks context

The introduction states contributions clearly but provides zero comparison with existing work. There is no "related work" discussion. A reader encountering this paper would have no idea whether:
- Multiscale consistency for numeration-based projections has been studied before
- The gauge anomaly concept is new or borrowed from physics/information theory
- The sofic conjugacy result extends known results on Fibonacci sliding block codes

### 3.4 Section 8 (information ledger) is disconnected

Section 8 introduces a different notational layer (probability simplices, lifting kernels, synchronization times, collision probabilities, temperature-gated distributions) with no connection to the preceding sections. The quantities T_m, nu_m, nu_{u,m}, h_2(u), Fail_{m,n,N} appear without definition. This section reads as if it was imported from a different paper.

### 3.5 No author information

The \author{} field is empty. This is fine for review stage but should be noted.

---

## 4. Specific Cut/Merge/Rewrite Recommendations

### BLOCKER-1: Add proofs for all 14 proof-less statements

- **Location:** Sections 3--8 and Appendices C--E
- **Problem:** 14 of 18 formal statements lack proofs
- **Fix:** Write complete proofs. For the transfer-matrix results (Theorems 4.1--4.3), the sofic graph must be derived from first principles and the Parry-measure computation shown in full. For Theorem 6.3, either provide a tilted-transfer-matrix proof analogous to the anomaly CLT or cite a general theorem from thermodynamic formalism. For Theorem 8.1, write the 5-line entropy calculation. For Theorem 8.2, define all quantities before the statement and give the elementary probability argument.

### BLOCKER-2: Expand bibliography to >= 15 references

- **Location:** references.bib
- **Problem:** 1 citation used; no positioning relative to prior work
- **Fix:** Add references for Zeckendorf representations, Fibonacci numeration, symbolic dynamics (especially Lind-Marcus which is already in the bib), transfer matrices, Lee-Yang theory, and CLTs for Markov chains. Cite them at appropriate points in the text. The unused bib entries (Lekkerkerker1952, LindMarcus1995, LeeYang1952) should be cited where relevant.

### BLOCKER-3: Derive the sofic graph in Remark 4.2 from the definitions

- **Location:** Section 4.3 (Remark 4.2, lines 74--96)
- **Problem:** The 4-state edge shift with its specific adjacency matrix and edge labels is asserted without derivation. This is the foundation for Theorems 4.1--4.3.
- **Fix:** Show how the 4 states arise (they should correspond to the carry/borrow states of Zeckendorf normalization interacting with truncation), derive the transitions, and verify the edge labels. This can go in an appendix if space is tight, but the derivation must exist.

### MEDIUM-1: Clarify probability space for Section 4 limit theorems

- **Location:** Section 4.4 (subsec:lln-clt)
- **Problem:** The paper conflates finite-window uniform measure on Omega_{m+1} with the stationary process on the bi-infinite shift. The sum G_m = sum Delta_t is defined using the "stationary bulk discrepancy indicator process" but the theorem claims a.s. convergence and CLT for a finite-window quantity.
- **Fix:** State precisely: either (a) the CLT is for the stationary Markov chain on the sofic graph with growing observation window, or (b) give the finite-m statement with explicit error terms. The LLN should clarify whether "a.s." means along a sequence of windows or in the bi-infinite shift.

### MEDIUM-2: Cut or substantially expand Sections 7 and 8

- **Location:** Sections 7 (discriminant fingerprint) and 8 (information ledger)
- **Problem:** Section 7 introduces a definition, computes one value (37), and speculates about Chebotarev. Section 8 proves a standard entropy identity and a trivial union bound. Neither section has the depth expected of a journal contribution.
- **Fix:** Option A (preferred): Remove Sections 7--8 entirely and reposition the paper as a focused contribution on Fibonacci folding, gauge anomaly, and sofic structure (Sections 1--6 + discussion). This yields a tighter, more publishable paper. Option B: If kept, Section 7 needs at least 2--3 more fingerprint computations (q=3,4,...) and a theorem connecting the fingerprint to some structural property. Section 8 needs all quantities properly defined before the theorem statements.

### MEDIUM-3: Proposition 4.1 needs a proof, not just an example

- **Location:** Section 4.2
- **Problem:** Proposition 4.1 states G_m(omega*) = m for some omega*. Remark 4.1 gives the explicit family. But the proof that this family achieves G_m = m is missing.
- **Fix:** Prove that the explicit family in Remark 4.1 satisfies G_m = m. This requires showing that (a) Fold_{m+1}(omega*) has a specific form, and (b) naive truncation and fold-aware restriction disagree at every coordinate. The computational verification (m=1..400) is not a proof.

### MEDIUM-4: Expand Appendix C (sofic conjugacy)

- **Location:** Appendix C (13 lines total)
- **Problem:** This appendix is supposed to contain "structural proofs and an explicit inverse-code construction" (per the remark in Section 5) but contains only 3 paragraphs of hand-waving.
- **Fix:** Give the explicit inverse block code Psi_m for m=3. Prove that the labeled graph is right-resolving after delay m-1. Show the failure of right-resolvability for m=2 and identify the two colliding periodic orbits.

### MINOR-1: Fix the title

- **Location:** main.tex line 3--4
- **Problem:** The title is 19 words long and includes 3 technical compound nouns separated by commas. It is unwieldy.
- **Fix:** Shorten to something like "Fibonacci Folding and Zeckendorf Normalization: Gauge Anomaly, Spectral Analysis, and Sofic Structure."

### MINOR-2: Remove "Draft consistency check" remark

- **Location:** Section 4.5 (Remark after Theorem 4.3, line 156--158)
- **Problem:** The remark is labeled "Draft consistency check" which signals unfinished work.
- **Fix:** Either remove the remark or rename it (e.g., "Remark (Internal consistency)").

### MINOR-3: Theorem 5.1/5.2 section title uses "m >= 3" not math mode

- **Location:** Section 5.3 title (line 35 of 05-sequence-level.tex)
- **Problem:** The subsection title reads "A conjugacy threshold at m >= 3" in plain text rather than math mode.
- **Fix:** Use `$m \ge 3$` in the title.

### MINOR-4: Clarify the Fibonacci evaluation weight convention

- **Location:** Section 2.2 (Definition, eq. (1))
- **Problem:** The weight F_{k+1} for position k means position 1 has weight F_2=1, position 2 has weight F_3=2, etc. This is non-standard (most references use F_k or position-index starting at 0). The convention is correct but should be flagged as non-standard.
- **Fix:** Add a brief remark: "We adopt the convention that position k carries weight F_{k+1}, so that position 1 carries weight 1 and position 2 carries weight 2."

### MINOR-5: Missing label on Section 9

- **Location:** Section 9 (discussion)
- **Problem:** Section 9 has label \label{sec:discussion} which is defined but never referenced. Not an error, just housekeeping.
- **Fix:** No action needed.

### MINOR-6: Notation nu_{u,m} undefined in Theorem 8.2

- **Location:** Section 8.2, line 26--29
- **Problem:** The symbol nu_{u,m} is introduced as "a temperature-gated pushforward distribution" without defining what "temperature-gated" means.
- **Fix:** Define nu_{u,m} explicitly or remove the terminology.

---

## 5. Comparison with Prior Stage Notes

This is the first review (R1). No prior P2/P3 notes exist for this paper. No comparison applicable.

---

## 6. Summary of Blockers

| # | Severity | Issue |
|---|----------|-------|
| B1 | BLOCKER | 14/18 formal statements lack proofs |
| B2 | BLOCKER | Bibliography has 1 used citation; no positioning vs prior work |
| B3 | BLOCKER | Central sofic graph (Remark 4.2) asserted without derivation |
| M1 | MEDIUM | Probability space for limit theorems unclear |
| M2 | MEDIUM | Sections 7--8 are shallow/disconnected; cut or expand |
| M3 | MEDIUM | Proposition 4.1 lacks proof (computational check is not proof) |
| M4 | MEDIUM | Appendix C is a 3-paragraph sketch, not a proof |
| m1 | MINOR | Title too long |
| m2 | MINOR | "Draft consistency check" remark |
| m3 | MINOR | Plain-text "m >= 3" in section title |
| m4 | MINOR | Weight convention non-standard; add clarification |
| m5 | MINOR | Undefined notation in Theorem 8.2 |

---

## 7. Recommendation

The mathematical content is sound and computationally verified. The paper has a clear, coherent story through Sections 1--6 with genuine novelty. However, in its current form it is a research announcement, not a journal article. The 3 blockers (missing proofs, absent bibliography, unsubstantiated sofic graph) must be resolved before resubmission.

**Suggested action plan:**
1. Write proofs for all 14 proof-less statements. Priority: Theorems 4.1--4.3 (the paper's central results).
2. Add 15+ references and a "Related work" paragraph in the introduction.
3. Consider cutting Sections 7--8 to produce a focused 15--20 page paper on Fibonacci folding, gauge anomaly, and sofic structure.
4. Fix all MEDIUM and MINOR items.

After these revisions, the paper would be competitive for *Advances in Applied Mathematics* or *Journal of Combinatorial Theory Ser. A*.
