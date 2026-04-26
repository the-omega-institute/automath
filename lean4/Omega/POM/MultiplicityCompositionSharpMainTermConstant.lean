import Mathlib
import Omega.POM.MultiplicityCompositionExactConditionalIid
import Omega.POM.MultiplicityCompositionMomentHierarchyRationalGrowth
import Omega.POM.MultiplicityCompositionPartition

namespace Omega.POM

noncomputable section

/-- The dominant pole location `ρ(q) = λ(q)⁻¹`. -/
def pomMultiplicityCompositionRho (q : ℕ) : ℝ :=
  1 / pomMomentHierarchyDominantRoot q

/-- The atomic block series `A_q(t)` for the simplified two-step multiplicity-composition model. -/
def pomMultiplicityCompositionAtomicSeries (q : ℕ) (t : ℝ) : ℝ :=
  pomMomentHierarchyWeight q * t + pomMomentHierarchyWeight q * t ^ (2 : Nat)

/-- The derivative `A_q'(t)` of the atomic block series. -/
def pomMultiplicityCompositionAtomicSeriesDerivAt (q : ℕ) (t : ℝ) : ℝ :=
  pomMomentHierarchyWeight q + 2 * pomMomentHierarchyWeight q * t

/-- The renewal mean `μ_q = ρ(q) A_q'(ρ(q))`. -/
def pomMultiplicityCompositionRenewalMean (q : ℕ) : ℝ :=
  pomMultiplicityCompositionRho q *
    pomMultiplicityCompositionAtomicSeriesDerivAt q (pomMultiplicityCompositionRho q)

/-- The residue-style main-term constant `C(q) = 1 / μ_q`. -/
def pomMultiplicityCompositionMainTermConstant (q : ℕ) : ℝ :=
  1 / pomMultiplicityCompositionRenewalMean q

/-- Concrete package for the sharp-main-term discussion in the audited integer-`q` model. -/
def pomMultiplicityCompositionSharpMainTermConstantClaim : Prop :=
  pomMultiplicityCompositionPartCountBivariateGF ∧
    (∀ D : PomMultiplicityCompositionExactConditionalIidData, D.exactConditionalIid) ∧
    (∀ q : ℕ,
      0 < pomMultiplicityCompositionRho q ∧
        pomMultiplicityCompositionRho q * pomMomentHierarchyDominantRoot q = 1) ∧
    (∀ q : ℕ,
      pomMultiplicityCompositionAtomicSeries q (pomMultiplicityCompositionRho q) = 1 ∧
        1 - pomMultiplicityCompositionAtomicSeries q (pomMultiplicityCompositionRho q) = 0) ∧
    (∀ q : ℕ,
      0 < pomMultiplicityCompositionAtomicSeriesDerivAt q (pomMultiplicityCompositionRho q)) ∧
    (∀ q : ℕ,
      0 < pomMultiplicityCompositionRenewalMean q ∧
        pomMultiplicityCompositionMainTermConstant q =
          1 / pomMultiplicityCompositionRenewalMean q)

private lemma pomMultiplicityCompositionLambda_sq (q : ℕ) :
    pomMomentHierarchyDominantRoot q ^ (2 : Nat) =
      pomMomentHierarchyWeight q * pomMomentHierarchyDominantRoot q + pomMomentHierarchyWeight q := by
  exact (paper_pom_multiplicity_composition_moment_hierarchy_rational_growth.2.2.2.1 q).1

private lemma pomMultiplicityCompositionLambda_pos (q : ℕ) :
    0 < pomMomentHierarchyDominantRoot q := by
  exact (paper_pom_multiplicity_composition_moment_hierarchy_rational_growth.2.2.2.1 q).2.2

private lemma pomMultiplicityCompositionRho_pos (q : ℕ) :
    0 < pomMultiplicityCompositionRho q := by
  unfold pomMultiplicityCompositionRho
  exact one_div_pos.mpr (pomMultiplicityCompositionLambda_pos q)

private lemma pomMultiplicityCompositionRho_mul_lambda (q : ℕ) :
    pomMultiplicityCompositionRho q * pomMomentHierarchyDominantRoot q = 1 := by
  unfold pomMultiplicityCompositionRho
  field_simp [ne_of_gt (pomMultiplicityCompositionLambda_pos q)]

private lemma pomMultiplicityCompositionAtomicSeries_at_rho (q : ℕ) :
    pomMultiplicityCompositionAtomicSeries q (pomMultiplicityCompositionRho q) = 1 := by
  have hlam_pos : 0 < pomMomentHierarchyDominantRoot q := pomMultiplicityCompositionLambda_pos q
  unfold pomMultiplicityCompositionAtomicSeries pomMultiplicityCompositionRho
  field_simp [ne_of_gt hlam_pos]
  nlinarith [pomMultiplicityCompositionLambda_sq q]

private lemma pomMultiplicityCompositionAtomicSeriesDerivAt_pos (q : ℕ) :
    0 < pomMultiplicityCompositionAtomicSeriesDerivAt q (pomMultiplicityCompositionRho q) := by
  have hw : 0 < pomMomentHierarchyWeight q := by
    unfold pomMomentHierarchyWeight
    positivity
  have hρ : 0 < pomMultiplicityCompositionRho q := pomMultiplicityCompositionRho_pos q
  unfold pomMultiplicityCompositionAtomicSeriesDerivAt
  nlinarith

private lemma pomMultiplicityCompositionRenewalMean_pos (q : ℕ) :
    0 < pomMultiplicityCompositionRenewalMean q := by
  have hρ : 0 < pomMultiplicityCompositionRho q := pomMultiplicityCompositionRho_pos q
  have hderiv : 0 < pomMultiplicityCompositionAtomicSeriesDerivAt q (pomMultiplicityCompositionRho q) :=
    pomMultiplicityCompositionAtomicSeriesDerivAt_pos q
  unfold pomMultiplicityCompositionRenewalMean
  nlinarith

/-- Paper label: `prop:pom-multiplicity-composition-sharp-main-term-constant`.
The existing partition-function and exact-conditional-i.i.d. wrappers combine with the
dominant-root relation `λ(q)^2 = w_q λ(q) + w_q` to identify the pole location `ρ(q)`, show that
`A_q(ρ(q)) = 1` with positive derivative, and record the residue-style main-term constant
`C(q) = 1 / μ_q`. -/
theorem paper_pom_multiplicity_composition_sharp_main_term_constant :
    pomMultiplicityCompositionSharpMainTermConstantClaim := by
  refine ⟨paper_pom_multiplicity_composition_part_count_bivariate_gf, ?_, ?_, ?_, ?_, ?_⟩
  · intro D
    exact paper_pom_multiplicity_composition_exact_conditional_iid D
  · intro q
    exact ⟨pomMultiplicityCompositionRho_pos q, pomMultiplicityCompositionRho_mul_lambda q⟩
  · intro q
    refine ⟨pomMultiplicityCompositionAtomicSeries_at_rho q, ?_⟩
    linarith [pomMultiplicityCompositionAtomicSeries_at_rho q]
  · intro q
    exact pomMultiplicityCompositionAtomicSeriesDerivAt_pos q
  · intro q
    exact ⟨pomMultiplicityCompositionRenewalMean_pos q, rfl⟩

end

end Omega.POM
