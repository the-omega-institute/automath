# P3 Journal-Fit Rewrite Note: ETDS

**Date**: 2026-03-30
**Target journal**: Ergodic Theory and Dynamical Systems (ETDS)
**Paper direction**: H

---

## Changes made

### 1. Abstract (main.tex)

Rewritten to ~150 words. Changes:
- Opens with the subshift of finite type and primitive adjacency matrix (ETDS context).
- States the three main contributions concisely: finite-part formula, cyclic reconstruction, Adams--Mobius primitive inversion.
- Removes the displayed equations (inappropriate length for ETDS abstracts).
- Mentions the S3-example as a concrete result, not a summary paragraph.
- Removes the closing "manifesto" sentence ("Thus cyclic lifts and finite-group extensions become...").

### 2. Introduction (sec_introduction.tex)

Fully rewritten to follow ETDS conventions:
- Opens with the mathematical context: dynamical zeta-functions, Bowen--Lanford, Manning, Ruelle, Parry--Pollicott, Baladi.
- Main results stated as Theorem A, Theorem B, Theorem C (standard ETDS style for the introduction).
- Theorem A: Finite-part formula at the Perron pole, including the Mertens asymptotic.
- Theorem B: Cyclic reconstruction of the reduced spectrum, with all three parts (full sequence, one layer, exponential fingerprint).
- Theorem C: Primitive determinant calculus for finite-group extensions, with three clearly labelled parts (Adams--Mobius inversion, class Mertens constants, quotient functoriality).
- Connection to the ETDS tradition is made explicit throughout: Parry--Pollicott 1986 (published in ETDS), Boyle--Schmieding 2017 (published in ETDS), Ruelle's programme, Baladi's transfer-operator theory.
- Added citation to Lind--Marcus 1995 for inverse spectral context.
- Added citation to Baladi 2000 for transfer-operator context.
- "What is standard and what is new" section replaced with "Relation to existing work" -- same comparison table but with neutral headers ("What is proved here" instead of "New theorem-level input").
- "Organisation" section renamed to "Plan of the paper" and references concrete theorem labels (Theorem A, Theorem B).
- Removed the sentence "Accordingly, the finite-group part of the paper is not another Chebotarev statement in disguise. Its novelty lies in..." -- promotional language.

### 3. Conclusion (sec_conclusion.tex)

Expanded from 25 lines to 72 lines with proper ETDS-style discussion:
- Subsection "Summary of the main contributions" -- concise recap referencing theorem labels.
- Subsection "Open problems" with three specific problems:
  1. Dynamical criteria for the twisted spectral gap (connects to Parry--Pollicott 1986 and Boyle--Schmieding 2017).
  2. Non-abelian analogues of the arithmetic appendix.
  3. Transfer-operator extensions (connects to Baladi, Ruelle--Pollicott resonances, countable-state shifts).
- This gives ETDS readers clear next directions and ties the paper to the broader dynamical-systems programme.

### 4. Bibliography (references.bib)

- Removed 15 uncited entries: CuntzKrieger1980, DemboZeitouni2010LargeDeviations, BrinStuck2002, Karp1978MinCycleMean, Ziemian1995RotationSFT, ChazottesGambaudoUgalde2011ZeroTempLocConst, LevinPeresWilmer2009MarkovMixing, MorseHedlund1940, Zeckendorf1972, WaltersErgodicTheory, Kitchens1998, Bowen1975EquilStates, SkolemMahlerLech, Parry1964Intrinsic.
- Retained all 15 entries that are actually cited in the included .tex files.
- Kept Baladi2000PositiveTransfer (now cited in intro and conclusion).
- Kept LindMarcus1995 (now cited in intro for inverse spectral context).
- Final count: 15 entries, all cited.

### 5. Style pass

- sec_chebotarev.tex: Changed "The genuinely new ingredient begins when the determinant data are pushed..." to "The specific content of the present paper begins when the determinant data are pushed..." (line 101).
- sec_appendices.tex: Removed informal/chatty appendix openers:
  - "The results collected here are technically useful but are no longer part of the main narrative." -> neutral opening.
  - "This appendix gathers the arithmetic consequences of the cyclic reconstruction theorem that were removed from the main text in order to keep the principal abelian spine short." -> removed revision-trace language ("removed from the main text").
  - "The final appendix records the growing-family statements that are downstream from the cyclic reconstruction machinery but are not needed for the core finite-part / finite-group bridge developed in the main text." -> neutral opening.
- No AI-voice issues (novel framework, paradigm shift, groundbreaking, etc.) were found in any included file.
- No revision-trace language was found in any .tex file.

### 6. File length check

All .tex files are under 800 lines:
- main.tex: 100
- sec_introduction.tex: 276
- sec_preliminaries.tex: 194
- sec_finite_part.tex: 418
- sec_chebotarev.tex: 619
- sec_shadows.tex: 653
- sec_conclusion.tex: 72
- sec_appendices.tex: 718 (three appendix sections; largest included file, still under limit)

No splits needed.

---

## Items NOT changed (deliberate)

- sec_preliminaries.tex: Clean, standard notation section. No changes needed.
- sec_finite_part.tex: Proofs are self-contained and cleanly written. No style issues found.
- sec_chebotarev.tex: One minor style fix (above). Otherwise clean.
- sec_shadows.tex: Clean. The S3-example is well-presented. "Genuinely non-abelian" language in the section opener is standard mathematical usage (describing the content of the orthogonal complement), not promotional.
- sec_appendices.tex: Three minor opener fixes (above). Otherwise clean.
- Excluded files (sec_syntax_zeta.tex, sec_operator.tex, sec_online_kernel.tex): Not touched, as they are excluded from main.tex.
