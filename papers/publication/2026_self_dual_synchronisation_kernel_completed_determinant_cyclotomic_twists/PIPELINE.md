# Pipeline: Self-Dual Synchronisation Kernel / Completed Determinant / Cyclotomic Twists
Target: IMRN (International Mathematics Research Notices)
Status: P4 MAJOR_REVISION; P5--P7 pending

## Stage Progress

| Stage | Status | Date | Notes |
|---|---|---|---|
| P0 Intake and Contract | completed | -- | IMRN primary; ETDS or J. Algebraic Combinatorics as alternatives |
| P1 Traceability | completed | -- | 13 theorem-level claims, all proved |
| P2 Research Extension | completed | 2026-03-30 | Case study: one 10-state kernel through to full explicitness; genus-6 curve, S6 Galois, 6-term asymptotics |
| P3 Journal-Fit Rewrite | pending | -- | |
| P4 Editorial Review | MAJOR_REVISION | 2026-04-04 | All math verified correct; 4 blockers: kernel motivation, S6 proof, smoothness check, bibliography |
| P5 Integration | pending | -- | |
| P6 Lean Sync | pending | -- | |
| P7 Submission Pack | pending | -- | |

### Blocking Issues (P4, 2026-04-04)

- [BLOCKER] No motivation for the synchronisation kernel in the introduction; reader cannot assess significance
- [BLOCKER] S6 Galois group proof (Prop 3.6) incomplete: specific specialisation values and factorisations not recorded
- [BLOCKER] Quartic smoothness verification (Prop 3.4) not exhibited; proof outsources check to reader
- [BLOCKER] Bibliography has only 4 references (all pre-2000); needs expansion to 10-12 with recent work and technique citations
- [MEDIUM] Branch point at infinity (Prop 3.5) not exhibited
- [MEDIUM] 10x10 determinant computation (Prop 3.1) has no verification note
- [MEDIUM] Asymptotic coefficients (Thm 3.10) have no numerical validation

## Theorem Inventory

### Tier A: Headline results

- `prop:sync-hatdelta-double-cover` + `prop:sync-hatdelta-quotient`: Normalisation has genus 6; quotient by involution is smooth plane quartic (genus 3)
- `prop:sync-hatdelta-galois-s6-generic`: Generic Galois group is S6
- `thm:rho-gap-m12`: Full asymptotic expansion of twisted Perron roots to O(m^{-14}); leading gap 3 - rho_m ~ 11 pi^2/(17 m^2)

### Tier B: Essential supporting results

- `prop:sync-self-duality`: Self-duality Delta(z,u) = Delta(uz, u^{-1}) via explicit state-space involution
- `prop:sync-hatdelta-completion`: Completed determinant and parity relation
- `thm:sync-cyclotomic-degree-law`: Degree law deg_w R_m = 3 phi(2m) for m >= 4
- `cor:rho-m2-closed-form`: Closed form rho_2 = sqrt(2 + sqrt(3))
- `prop:sync-endpoint-jet`: Endpoint jet of analytic branch rho(s) near s=2

### Tier C: Standard / auxiliary

- `lem:primitive-orbit-asymptotic`: Standard prime orbit theorem
- `prop:cyclic-lift-primitive-asymptotics`: Direct consequence of Mobius inversion for tensor products with cyclic permutation matrices

### Additional results

- `prop:kernel-delta-explicit`: Explicit closed form of Delta(z,u) as degree-6 polynomial
- `prop:sync-kernel-spectrum`: det(I-zB) factorisation, rho(B)=3, C_B = 243/272

**Total:** 13 theorem-level claims (2 theorems, 8 propositions, 1 corollary, 1 lemma, 1 definition). All proved.

## Source Map

| File | Key content |
|------|-------------|
| `sec_introduction.tex` | Umbrella theorems: `thm:intro-kernel-geometry`, `thm:intro-kernel-cyclotomic` |
| `sec_preliminaries.tex` | Primitive orbits, sync kernel definition, self-duality |
| `sec_kernel.tex` | All body results: explicit determinant, spectrum, completion, quotient, double cover, Galois group, cyclotomic degree law, closed form, endpoint jet, asymptotic expansion, cyclic lift |
| `sec_conclusion.tex` | Follow-up questions |
| `references.bib` | 4 entries (pruned from 24; now too sparse) |

### Dependency graph

```
def:sync-kernel
  -> prop:sync-self-duality
      -> prop:kernel-delta-explicit
          -> prop:sync-kernel-spectrum
          -> prop:sync-hatdelta-completion
              -> prop:sync-hatdelta-quotient
                  -> prop:sync-hatdelta-double-cover
              -> prop:sync-hatdelta-galois-s6-generic
              -> thm:sync-cyclotomic-degree-law
                  -> cor:rho-m2-closed-form
                  -> thm:rho-gap-m12  (also depends on prop:sync-endpoint-jet)
              -> prop:sync-endpoint-jet

eq:primitive-mobius
  -> lem:primitive-orbit-asymptotic
      -> prop:cyclic-lift-primitive-asymptotics
```

## Stage Notes

### P2 Research Extension

**Assessment:** The paper is a case study -- one 10-state weighted synchronisation kernel carried through to full explicitness. The novelty lies in the completeness of the computation rather than in new general methods. This is a legitimate contribution for the right venue.

**Novelty by result:**
- Self-duality relation: Medium. Kernel-specific, verified by inspection.
- Completed determinant: Medium-High. Natural algebraic simplification carried out in full for this kernel.
- Genus computation: High for this context. Hurwitz applied to double cover of genus-3 quartic.
- S6 Galois group: Medium. Standard strategy (discriminant + specialisation), kernel-specific execution.
- Cyclotomic degree law: Medium. Straightforward Sylvester-matrix argument.
- Asymptotic expansion: High. Six explicit terms with exact rational coefficients; most labour-intensive and distinctive result.
- Primitive orbit asymptotics: Low. Standard.

**Gaps identified:**
1. Quartic smoothness (Prop 6): Projective closure smoothness asserted without displayed computation. Needs explicit partial-derivative check or companion script.
2. Branch points at infinity (Prop 7): Behaviour at infinity not exhibited. One sentence needed.
3. S6 Galois proof (Prop 8): Discriminant and specialisation values not recorded. Needs 3-5 additional lines.
4. 10x10 determinant (Prop 3): No verification script. Self-duality check provides partial validation.
5. Asymptotic coefficients (Thm 12): Large integer coefficients (numerators up to 19 digits). No verification script.
6. Primitivity of B(1): Asserted but not proved. Immediate from transition structure (self-loop + strong connectivity).
7. Analytic branch selection: Continuity argument for rho_m = rho(s_m) valid for large m; small-m range not addressed.

**Recommendations:**
- High priority: Exhibit smoothness check, complete Galois proof, provide verification script, prune bibliography.
- Medium priority: Verify primitivity explicitly, add Hurwitz formula citation, clarify branch locus at infinity.
- Low priority: Add numerical validation table (rho_m exact vs asymptotic for m=4,6,8,10,12).

**Bibliography:** 24 entries. Only Bowen-Lanford, Manning, Lind-Marcus, Kitchens actually cited. Many entries inherited from parent manuscript. Missing: resultant/elimination theory reference, Hurwitz formula textbook citation, Jordan's theorem reference.

**Journal targeting:** IMRN recommended. The genus computation and Galois group determination provide enough algebraic geometry content. Alternatives: Journal of Algebraic Combinatorics, ETDS.

### P4 Editorial Review (2026-04-04)

**Decision: MAJOR_REVISION**

**Verification summary:** All 13 theorem-level claims independently verified by symbolic computation (sympy). Delta(z,u) confirmed against the explicit 10x10 matrix. Self-duality confirmed at matrix level. Completed determinant, parity, quotient curve, smoothness, genus, Galois group, degree law, R_2, endpoint jet, and all 6 asymptotic coefficients confirmed. No mathematical errors found.

**Top 3 blockers:**
1. No motivation for the kernel (introduction does not explain origin or significance)
2. S_6 Galois proof and quartic smoothness proof are skeletons (conclusions correct but computations not exhibited)
3. Bibliography inadequate (4 entries, all pre-2000; needs 10-12 with technique citations)

**P2 gap resolution:** Bibliography pruning resolved the "uncited entries" problem but created a new "too few entries" problem. All other P2 gaps remain open.

**Recommendation:** Address blockers, then re-review. Expected second-pass verdict: MINOR_REVISION or ACCEPT.

### Backflow to Core

| Result | Core target section | Status |
|---|---|---|
| `thm:intro-kernel-geometry` | `zeta_finite_part/` | pending |
| `thm:intro-kernel-cyclotomic` | `zeta_finite_part/` | pending |
| `prop:kernel-delta-explicit` | `zeta_finite_part/` | pending |
| `prop:sync-kernel-spectrum` | `zeta_finite_part/` | pending |
| `prop:sync-hatdelta-completion` | `zeta_finite_part/` | pending |
| `prop:sync-hatdelta-quotient` | `zeta_finite_part/` | pending |
| `prop:sync-hatdelta-double-cover` | `zeta_finite_part/` | pending |
| `prop:sync-hatdelta-galois-s6-generic` | `zeta_finite_part/` | pending |
| `thm:sync-cyclotomic-degree-law` | `zeta_finite_part/` | pending |
| `cor:rho-m2-closed-form` | `zeta_finite_part/` | pending |
| `prop:sync-endpoint-jet` | `zeta_finite_part/` | pending |
| `lem:root-separation` | `zeta_finite_part/` | pending |
| `thm:rho-gap-m12` | `zeta_finite_part/` | pending |
| `prop:cyclic-lift-primitive-asymptotics` | `zeta_finite_part/` | pending |
| `lem:primitive-orbit-asymptotic` | `zeta_finite_part/` | pending |
| `prop:sync-self-duality` | `zeta_finite_part/` | pending |
