<!-- paper: 2026_prefix_scan_error_boundary_rates_dynamical_systems | review: prefix_scan_gate_R6.md | elapsed: 69s | rc: 0 -->

Using using-superpowers skill to comply with the mandatory skill-invocation rule before delivering analysis.

## 1. Root cause of rejection
The referee is fundamentally rejecting because the manuscript makes no research-level advance: every highlighted “result” in `main.tex` is either a classical Bayes-risk identity, a restatement of Tanaka’s formula, or a corollary that falls out immediately once strong thickness and cylinder-comparability assumptions are imposed, and the paper openly concedes this. Worse, Example 6.5 (boundary growth without thickness) contains an actual probabilistic error, so even the pedagogical component is unreliable. Without a genuinely new theorem that derives thickness/boundary growth intrinsically for a recognized class (hidden Markov, Gibbs, etc.), the paper is perceived as tidy repackaging rather than research, and the demonstrable mistake erodes whatever credibility remained.

## 2. Options
1. **Deep mathematical rewrite (hidden-Markov/Gibbs theorem path)**
   - Subtasks: (a) choose an intrinsic class (e.g., primitive hidden Markov filters or factors of mixing SFTs) and prove a theorem that derives uniform thickness and/or quantitative boundary growth without assuming it; (b) rebuild Section 5 so that the finite-state posterior machinery becomes a corollary of that theorem; (c) fix Example 6.5 and audit all examples; (d) integrate the missing literature (Boyle–Petersen, Pollicott–Kempton, Verbitskiy, probabilistic automata).
   - Effort: 120–160 focused hours (new theory, proofs, rewrites).
   - Probability of eventual acceptance: ~0.35 (success hinges on delivering a real theorem competitive with current literature).
   - Downside risk: after heavy investment the new result might still be deemed incremental, delaying other projects.

2. **Scope reduction (convert to an expository/notes article)**
   - Subtasks: (a) strip Sections 3–5 down to concise, well-referenced summaries labeled as classical; (b) reframe the paper explicitly as a conditional framework plus curated examples, demoting multiple “theorems” to lemmas/corollaries; (c) repair Example 6.5 and ensure every computation is double-checked; (d) pitch to venues that welcome expository probability/dynamics notes (e.g., Expositiones Mathematicae, American Mathematical Monthly, or Probability Surveys if expanded).
   - Effort: 40–60 hours.
   - Probability of acceptance at an expository venue: ~0.5 (clarity is a strength, but even notes demand accurate statements and a clear raison d’être).
   - Downside risk: the main target journal goal is forfeited; note-style venues may still expect a sharper pedagogical hook.

3. **Venue change (probability/dynamics short-note outlet without major rewrites)**
   - Subtasks: (a) fix Example 6.5 and small inaccuracies; (b) emphasize the Tanaka-style identity plus weighted-boundary viewpoint as a short “Observation” and resubmit to a rapid-communication venue such as Electronic Communications in Probability or Stochastics and Dynamics; (c) tighten the abstract/introduction to be honest about conditional scope; (d) add the missing hidden-Markov/Gibbs citations.
   - Effort: 25–35 hours.
   - Probability of acceptance: ~0.2 (these venues still expect a nontrivial insight; without a new theorem the editor may reach the same verdict).
   - Downside risk: repeated rejections damage credibility and waste cycles while the core deficiency (novelty) remains.

4. **Abandon / park**
   - Subtasks: (a) archive the LaTeX, referee report, and notes; (b) document the useful lemmata/examples for future reference; (c) redirect effort toward projects with clearer innovation paths.
   - Effort: 6–8 hours.
   - Probability of eventual publication (if revisited later with new results): unknown; near zero without new math.
   - Downside risk: sunk cost is unrecovered and any potential niche utility of the framework is delayed indefinitely.

## 3. Recommendation
Pursue Option 1 (deep mathematical rewrite). The rejection is driven by a novelty vacuum, not by presentation; only a substantive new theorem that derives thickness/boundary growth for a recognized class (hidden Markov/sofic/Gibbs) can move the manuscript back into research territory. Scope reduction or venue shopping merely concedes the research goal, while abandoning wastes the structural insights already collected. Although Option 1 is high effort, it is the only path that addresses both blockers simultaneously: it supplies independent mathematical content and forces a thorough audit that will eliminate the Example 6.5 error.

## 4. If chosen, the first 3 concrete actions
1. **Example audit sprint:** Recompute Example 6.5 (and every other worked example) with symbolic scripts to ensure all conditional probabilities and rate claims are correct before layering new theory.
2. **Theorem target decision:** Within one week, convene the team to pick the precise intrinsic class (e.g., primitive hidden Markov chains with positive transition matrices) and draft a formal theorem statement specifying the desired automatic thickness/boundary-growth conclusion.
3. **Literature bridge + scaffolding:** Build a detailed outline linking existing hidden-Markov/sofic and Gibbs factor results to the desired theorem (state space graphs, spectral radii, potential weights), so the proof plan is anchored in recognized machinery rather than bespoke definitions.

## 5. Red flags
- Even with a new theorem, referees may still deem the result incremental unless it clearly outperforms known hidden-Markov or Gibbs factor theorems.
- Proving uniform thickness for a natural class may simply be false without additional irreducibility/nondegeneracy hypotheses; discovering this late would waste the rewrite effort.
- The team must be prepared to demote or delete large swaths of the current “theorem” numbering; clinging to the existing structure will make the rewrite incoherent.
- If the new theorem leans on heavy spectral or thermodynamic formalism, the paper may balloon beyond a “note,” potentially exceeding the original venue’s expectations.
- Resource risk: dedicating 150+ hours could stall other submissions; if staffing is thin, Option 1 might be impractical despite being strategically correct.

