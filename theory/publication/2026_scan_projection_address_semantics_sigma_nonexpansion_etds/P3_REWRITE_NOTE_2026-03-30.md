# P3 Rewrite Note

Date: `2026-03-30`
Stage: `P3 Journal-Fit Rewrite`

## What was restructured and why

### Abstract (main.tex)

The abstract was compressed from four long paragraphs (with two displayed equations) to a single paragraph stating one problem, one theorem package, and one payoff.  The old abstract enumerated too many coequal results (Tanaka identity, Markov boundary automaton, Renyi spectrum, hidden entropy) in a way that read as a catalog rather than a focused contribution.  The new abstract opens with a question ("what does the Bayes error detect about the open dynamics?"), answers it with three concrete claims (escape rate, quasistationary amplitude, cyclotomic resolvent), and closes with the thermodynamic consequence (survivor Renyi spectrum and Poisson birthday threshold).

### Introduction (sec_introduction.tex)

Completely rewritten.  The old introduction opened with general language about open dynamical systems and then described a "short structural component and a longer open-system component," which read as two separate papers merged.  The new introduction is organized as:

1. **Problem** -- one paragraph defining the Bayes error and stating the central question.
2. **Setting** -- one paragraph fixing the Markov/Gibbs setup.
3. **Main results** -- all three main theorems stated upfront with a one-sentence bridge between each.
4. **Context and comparison** -- literature positioning, unchanged in substance.
5. **Why the open-system lane belongs in this paper** -- explicit justification, as required by the task card.
6. **Organization** -- section-by-section guide.

This structure follows the ETDS profile: problem in dynamical-systems language from page one, principal theorem package stated early, secondary interpretation deferred.

### Section openings (sec_recursive_addressing, sec_clarity, sec_open_system, sec_double_budget)

Each section's opening paragraph was tightened to state its role relative to the main theorem arc rather than describing itself as a separate thematic center.  Specifically:

- `sec_recursive_addressing`: Reduced the opening to one sentence saying this is preparatory factor-theoretic background.  The closing remark was shortened to avoid restating the section's contents in list form.
- `sec_clarity`: Opening now names the tools (Bayes formula, Tanaka identity, boundary transfer) and forward-references Section 5 as the target application.
- `sec_open_system`: Opening now says "this section applies the weighted boundary transfer theorem to the principal setting of the paper" rather than "we now pass from general boundary transfer to the central open-system specialization."
- `sec_double_budget`: Opening now directly names the survivor Renyi pressure spectrum instead of framing it as "turning the open-system analysis into a pressure spectrum."

### Conclusion (sec_conclusion.tex)

Rewritten to mirror the tightened theorem arc.  Removed the paragraph about "a short structural section records that recursive visible refinements remain internal" -- that information is now in the section itself.  The two open questions are unchanged.

## What was cut and why

- **Displayed equations in the abstract**: The two displayed formulas for the Renyi partition function and its limit were removed.  They duplicated material from Theorem 1.2 and made the abstract too long for ETDS conventions.
- **"The paper has a short structural component and a longer open-system component"**: This sentence in the old introduction signaled a merged manuscript.  Replaced by the explicit "Why the open-system lane belongs" subsection.
- **"We will not use these statements as headline results below"**: The closing remark in sec_recursive_addressing was rewritten to avoid this self-deprecating formulation.
- **"supplementary information-theoretic statement"** phrasing in sec_double_budget: Replaced with a direct statement of what the subsection does.

## What was preserved exactly

- All theorem statements, proofs, definitions, and propositions are unchanged in mathematical content.
- All cross-references and label names are unchanged.
- The bibliography is unchanged.
- The section ordering is unchanged.
- Keywords and MSC codes are unchanged.

## Remaining style issues that need human judgment

1. **Title length**: The current title is 11 words with a subtitle.  An ETDS referee may prefer a shorter title.  A candidate: "Finite observation detects escape rates and cyclotomic resonances of open symbolic dynamics."  This is a human-judgment call.

2. **Sturmian section placement**: Section 3 (visible words and Sturmian illustration) is brief and somewhat peripheral.  A referee might ask whether the Sturmian material could be moved to an appendix or shortened further.  The mathematical content is clean, so the decision is editorial.

3. **Hidden-entropy subsection**: The final subsection of Section 7 (restoring collapsed Renyi spectra) is a supplementary information-theoretic result.  It is clearly subordinated now, but a referee might still ask whether it belongs in a dynamical-systems paper.  The case for keeping it: it closes the logical loop on the collision spectrum.  The case for cutting it: it is the most information-theoretic part of an otherwise dynamical paper.

4. **Bibliography width**: BIB_SCOPE notes that 5 of 22 entries are unused.  A bibliography cleanup pass should remove them, but this is a mechanical task best done after all content edits are final.
