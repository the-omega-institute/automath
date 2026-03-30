# P3 Journal-Fit Rewrite Note -- 2026-03-30

Paper: `2026_projection_ontological_mathematics_core_tams`
Target journal: Transactions of the American Mathematical Society

---

## 1. Structural changes to main.tex

- **sec_chebotarev.tex** included in the main line, placed between sec_ledger and sec_conclusion.
- **sec_appendix.tex** included as Appendix B (after Appendix A = sec_appendix_transducer.tex).
- **sec_rewriting.tex** and **sec_appendix_auxiliary.tex** confirmed excluded (not referenced from main.tex).
- MSC code `11R32` (Galois theory of global fields) added to `\subjclass`.
- Keywords updated to include "Galois groups" and "Chebotarev density".

## 2. Abstract rewrite

Rewrote from ~350 words to ~170 words. The new abstract:
- Opens with the main structural result (fiber multiplicities = partition derivatives).
- States the moment transfer and finite-state realization.
- Describes the pressure/canonical formalism concisely.
- Closes with the arithmetic payoff: Galois groups $\cong S_{d_q}$, linear disjointness, product Chebotarev densities $1/20449$.

## 3. Introduction rewrite (sec_introduction.tex)

Complete rewrite:
- Opens with Zeckendorf representations and the finite-window fold.
- Previews Theorems A--F with compact one-line statements.
- Summarizes the escalation ladder: single fibers, moment transfer, finite-state realization, canonical selection, zero-temperature, arithmetic payoff.
- Related work subsection: cites Zeckendorf, Lekkerkerker, Chow--Slattery, Chow--Jones, Sanna with precise theorem-level positioning.
- Section roadmap at end covers all sections including sec_chebotarev and both appendices.

## 4. Bibliography changes (sec_references.tex)

### Added (4 entries)
| Key | Where cited |
|-----|-------------|
| `Neukirch1999` | sec_chebotarev (Cor. 7.6, Cor. 7.11) |
| `LindMarcus1995` | sec_moment_kernel (preamble), sec_introduction |
| `CoverThomas2006` | sec_ledger (preamble) |
| `DemboZeitouni2010` | sec_moment_kernel (preamble) |

### Removed (4 entries)
| Key | Reason |
|-----|--------|
| `AhlbachUsatineFrougnyPippenger2013` | Uncited |
| `Kempton2023` | Uncited |
| `ShallitShan2023` | Uncited |
| `BaaderNipkow1998` | Only cited in excluded sec_rewriting.tex |

### Final bibliography
13 entries, all cited in the included .tex files.

## 5. Conclusion rewrite (sec_conclusion.tex)

Shortened to ~15 lines. Now mentions:
- The affine-permutation bridge and pressure transfer.
- The canonical/microcanonical formalism.
- The arithmetic window results (Galois groups, linear disjointness).
- Remaining open problems (extension beyond $q=17$, symbolic root-isolation).

## 6. Style pass

- Removed all "present version", "new contribution", "genuinely discrete" and similar revision-trace language.
- sec_moment_kernel preamble now cites Lind--Marcus, Seneta, and Dembo--Zeitouni for the symbolic dynamics and large-deviation framework.
- sec_ledger preamble shortened: opens directly with the $q=1$ canonical identification and cites Cover--Thomas.
- No manifesto language detected in any section file.
- All files under 800 lines (largest: sec_moment_kernel at 682 lines).

## 7. Cross-reference audit

- `app:certification` (sec_appendix.tex) resolves correctly from sec_chebotarev.tex and sec_introduction.tex.
- `app:transducer` (sec_appendix_transducer.tex) resolves correctly from sec_moment_kernel.tex.
- `sec:chebotarev` resolves correctly from sec_appendix.tex and sec_introduction.tex.
- All 13 \bibitem keys have corresponding \cite commands; no orphan entries.
