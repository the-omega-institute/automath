import Mathlib
import Omega.POM.MultiplicityCompositionPartition
import Omega.POM.MultiplicityCompositionSharpMainTermConstant

namespace Omega.POM

noncomputable section

/-- The two-point renewal increment probability `p_q(1)`. -/
def pomMultiplicityCompositionIncrementProbOne (q : ℕ) : ℝ :=
  pomMomentHierarchyWeight q * pomMultiplicityCompositionRho q

/-- The two-point renewal increment probability `p_q(2)`. -/
def pomMultiplicityCompositionIncrementProbTwo (q : ℕ) : ℝ :=
  pomMomentHierarchyWeight q * pomMultiplicityCompositionRho q ^ (2 : Nat)

/-- The renewal variance of the increment law. -/
def pomMultiplicityCompositionRenewalVariance (q : ℕ) : ℝ :=
  pomMultiplicityCompositionIncrementProbOne q + 4 * pomMultiplicityCompositionIncrementProbTwo q -
    pomMultiplicityCompositionRenewalMean q ^ (2 : Nat)

/-- The LLN density `1 / μ_q` for the number of parts. -/
def pomMultiplicityCompositionPartCountLlnDensity (q : ℕ) : ℝ :=
  1 / pomMultiplicityCompositionRenewalMean q

/-- The CLT/LLT variance density `σ_q² / μ_q^3`. -/
def pomMultiplicityCompositionPartCountVarianceDensity (q : ℕ) : ℝ :=
  pomMultiplicityCompositionRenewalVariance q /
    pomMultiplicityCompositionRenewalMean q ^ (3 : Nat)

/-- The tilted dominant root obtained from the bivariate partition function. -/
def pomMultiplicityCompositionPartCountTiltedRoot (q : ℕ) (t : ℝ) : ℝ :=
  pomCompositionDominantRoot (Real.exp t * pomMomentHierarchyWeight q)

/-- The normalized cumulant-generating function for the part count. -/
def pomMultiplicityCompositionPartCountCgf (q : ℕ) (t : ℝ) : ℝ :=
  Real.log (pomMultiplicityCompositionPartCountTiltedRoot q t) -
    Real.log (pomMomentHierarchyDominantRoot q)

/-- The Gaussian local-limit kernel with the audited LLN/CLT constants. -/
def pomMultiplicityCompositionPartCountLocalGaussian (q : ℕ) (L : ℕ) (r : ℝ) : ℝ :=
  1 / Real.sqrt
        (2 * Real.pi * pomMultiplicityCompositionPartCountVarianceDensity q * (L : ℝ)) *
      Real.exp
        (-(r - pomMultiplicityCompositionPartCountLlnDensity q * (L : ℝ)) ^ (2 : Nat) /
          (2 * pomMultiplicityCompositionPartCountVarianceDensity q * (L : ℝ)))

/-- Concrete q-parameterized LLN/CLT/LLT package for the audited two-step model. -/
def pomMultiplicityCompositionPartcountGeneralqLLTClaim : Prop :=
  pomMultiplicityCompositionSharpMainTermConstantClaim ∧
    (∀ q : ℕ,
      pomMultiplicityCompositionIncrementProbOne q +
          pomMultiplicityCompositionIncrementProbTwo q = 1 ∧
        0 < pomMultiplicityCompositionIncrementProbOne q ∧
        0 < pomMultiplicityCompositionIncrementProbTwo q) ∧
    (∀ q : ℕ,
      pomMultiplicityCompositionRenewalMean q =
          pomMultiplicityCompositionIncrementProbOne q +
            2 * pomMultiplicityCompositionIncrementProbTwo q ∧
        pomMultiplicityCompositionRenewalVariance q =
          pomMultiplicityCompositionIncrementProbOne q *
            pomMultiplicityCompositionIncrementProbTwo q ∧
        0 < pomMultiplicityCompositionRenewalVariance q) ∧
    (∀ q : ℕ,
      pomMultiplicityCompositionPartCountLlnDensity q =
          1 / pomMultiplicityCompositionRenewalMean q ∧
        pomMultiplicityCompositionPartCountVarianceDensity q =
          pomMultiplicityCompositionRenewalVariance q /
            pomMultiplicityCompositionRenewalMean q ^ (3 : Nat) ∧
        0 < pomMultiplicityCompositionPartCountVarianceDensity q) ∧
    (∀ q : ℕ,
      pomMultiplicityCompositionPartCountTiltedRoot q 0 = pomMomentHierarchyDominantRoot q ∧
        pomMultiplicityCompositionPartCountCgf q 0 = 0) ∧
    (∀ q : ℕ, ∀ L : ℕ, ∀ r : ℝ,
      pomMultiplicityCompositionPartCountLocalGaussian q L r =
        1 / Real.sqrt
              (2 * Real.pi * pomMultiplicityCompositionPartCountVarianceDensity q * (L : ℝ)) *
            Real.exp
              (-(r - pomMultiplicityCompositionPartCountLlnDensity q * (L : ℝ)) ^ (2 : Nat) /
                (2 * pomMultiplicityCompositionPartCountVarianceDensity q * (L : ℝ))))

private lemma pomMultiplicityCompositionIncrementProbOne_pos (q : ℕ) :
    0 < pomMultiplicityCompositionIncrementProbOne q := by
  have hw : 0 < pomMomentHierarchyWeight q := by
    unfold pomMomentHierarchyWeight
    positivity
  have hρ : 0 < pomMultiplicityCompositionRho q :=
    (paper_pom_multiplicity_composition_sharp_main_term_constant.2.2.1 q).1
  unfold pomMultiplicityCompositionIncrementProbOne
  nlinarith

private lemma pomMultiplicityCompositionIncrementProbTwo_pos (q : ℕ) :
    0 < pomMultiplicityCompositionIncrementProbTwo q := by
  have hw : 0 < pomMomentHierarchyWeight q := by
    unfold pomMomentHierarchyWeight
    positivity
  have hρ : 0 < pomMultiplicityCompositionRho q :=
    (paper_pom_multiplicity_composition_sharp_main_term_constant.2.2.1 q).1
  have hρsq : 0 < pomMultiplicityCompositionRho q ^ (2 : Nat) := by
    positivity
  unfold pomMultiplicityCompositionIncrementProbTwo
  nlinarith

private lemma pomMultiplicityCompositionIncrementProb_sum (q : ℕ) :
    pomMultiplicityCompositionIncrementProbOne q +
        pomMultiplicityCompositionIncrementProbTwo q = 1 := by
  have h :=
    (paper_pom_multiplicity_composition_sharp_main_term_constant.2.2.2.1 q).1
  simpa [pomMultiplicityCompositionIncrementProbOne, pomMultiplicityCompositionIncrementProbTwo,
    pomMultiplicityCompositionAtomicSeries] using h

private lemma pomMultiplicityCompositionRenewalMean_eq (q : ℕ) :
    pomMultiplicityCompositionRenewalMean q =
      pomMultiplicityCompositionIncrementProbOne q +
        2 * pomMultiplicityCompositionIncrementProbTwo q := by
  unfold pomMultiplicityCompositionRenewalMean pomMultiplicityCompositionIncrementProbOne
    pomMultiplicityCompositionIncrementProbTwo pomMultiplicityCompositionAtomicSeriesDerivAt
  ring

private lemma pomMultiplicityCompositionRenewalVariance_eq (q : ℕ) :
    pomMultiplicityCompositionRenewalVariance q =
      pomMultiplicityCompositionIncrementProbOne q *
        pomMultiplicityCompositionIncrementProbTwo q := by
  have hsum := pomMultiplicityCompositionIncrementProb_sum q
  have hmean := pomMultiplicityCompositionRenewalMean_eq q
  have hone :
      pomMultiplicityCompositionIncrementProbOne q =
        1 - pomMultiplicityCompositionIncrementProbTwo q := by
    linarith
  unfold pomMultiplicityCompositionRenewalVariance
  rw [hmean]
  rw [hone]
  ring

private lemma pomMultiplicityCompositionRenewalVariance_pos (q : ℕ) :
    0 < pomMultiplicityCompositionRenewalVariance q := by
  rw [pomMultiplicityCompositionRenewalVariance_eq]
  exact mul_pos (pomMultiplicityCompositionIncrementProbOne_pos q)
    (pomMultiplicityCompositionIncrementProbTwo_pos q)

private lemma pomMultiplicityCompositionPartCountVarianceDensity_pos (q : ℕ) :
    0 < pomMultiplicityCompositionPartCountVarianceDensity q := by
  have hσ : 0 < pomMultiplicityCompositionRenewalVariance q :=
    pomMultiplicityCompositionRenewalVariance_pos q
  have hμ : 0 < pomMultiplicityCompositionRenewalMean q :=
    (paper_pom_multiplicity_composition_sharp_main_term_constant.2.2.2.2.2 q).1
  unfold pomMultiplicityCompositionPartCountVarianceDensity
  exact div_pos hσ (by positivity)

private lemma pomMultiplicityCompositionPartCountTiltedRoot_zero (q : ℕ) :
    pomMultiplicityCompositionPartCountTiltedRoot q 0 = pomMomentHierarchyDominantRoot q := by
  simp [pomMultiplicityCompositionPartCountTiltedRoot, pomMomentHierarchyDominantRoot,
    pomCompositionDominantRoot]

/-- Paper label: `thm:pom-multiplicity-composition-partcount-generalq-llt`.
In the audited q-tilted two-step model, the renewal increment law is the concrete two-point law
on `{1,2}` with probabilities summing to `1`; its mean and variance determine the LLN density
`1 / μ_q`, the CLT/LLT variance density `σ_q² / μ_q^3`, and the normalized cumulant-generating
function is anchored by the tilted dominant root at `t = 0`. -/
theorem paper_pom_multiplicity_composition_partcount_generalq_llt :
    pomMultiplicityCompositionPartcountGeneralqLLTClaim := by
  refine ⟨paper_pom_multiplicity_composition_sharp_main_term_constant, ?_, ?_, ?_, ?_, ?_⟩
  · intro q
    exact ⟨pomMultiplicityCompositionIncrementProb_sum q,
      pomMultiplicityCompositionIncrementProbOne_pos q,
      pomMultiplicityCompositionIncrementProbTwo_pos q⟩
  · intro q
    exact ⟨pomMultiplicityCompositionRenewalMean_eq q,
      pomMultiplicityCompositionRenewalVariance_eq q,
      pomMultiplicityCompositionRenewalVariance_pos q⟩
  · intro q
    exact ⟨rfl, rfl, pomMultiplicityCompositionPartCountVarianceDensity_pos q⟩
  · intro q
    refine ⟨pomMultiplicityCompositionPartCountTiltedRoot_zero q, ?_⟩
    simp [pomMultiplicityCompositionPartCountCgf, pomMultiplicityCompositionPartCountTiltedRoot_zero q]
  · intro q L r
    rfl

end

end Omega.POM
