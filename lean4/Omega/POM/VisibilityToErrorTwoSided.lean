import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators
noncomputable section

/-- Concrete finite fold-level data for the two-sided comparison between the Bayes-optimal
threshold classifier and the Bernoulli residual variance term `p * (1 - p)`. -/
structure VisibilityToErrorTwoSidedData where
  Y : Type
  [fintypeY : Fintype Y]
  [decidableEqY : DecidableEq Y]
  fiberWeight : Y → ℝ
  posterior : Y → ℝ
  weight_nonneg : ∀ y, 0 ≤ fiberWeight y
  posterior_mem_unitInterval : ∀ y, 0 ≤ posterior y ∧ posterior y ≤ 1

attribute [instance] VisibilityToErrorTwoSidedData.fintypeY
attribute [instance] VisibilityToErrorTwoSidedData.decidableEqY

namespace VisibilityToErrorTwoSidedData

/-- The Bayes-optimal fold-level classifier thresholds the posterior at `1 / 2`. -/
def thresholdClassifier (D : VisibilityToErrorTwoSidedData) (y : D.Y) : Prop :=
  (1 / 2 : ℝ) ≤ D.posterior y

/-- Error rate of the threshold classifier on a single fold. -/
def foldErrorTerm (D : VisibilityToErrorTwoSidedData) (y : D.Y) : ℝ :=
  if (1 / 2 : ℝ) ≤ D.posterior y then 1 - D.posterior y else D.posterior y

/-- Residual Bernoulli variance of the indicator observable on a single fold. -/
def visibilityResidualTerm (D : VisibilityToErrorTwoSidedData) (y : D.Y) : ℝ :=
  D.posterior y * (1 - D.posterior y)

/-- Weighted Bayes error profile of the threshold classifier. -/
def foldError (D : VisibilityToErrorTwoSidedData) : ℝ :=
  ∑ y : D.Y, D.fiberWeight y * D.foldErrorTerm y

/-- Weighted residual-variance profile attached to the indicator observable. -/
def foldVisibilityResidual (D : VisibilityToErrorTwoSidedData) : ℝ :=
  ∑ y : D.Y, D.fiberWeight y * D.visibilityResidualTerm y

/-- Exact foldwise Bayes error formula: thresholding the posterior gives `min(p, 1 - p)` on each
fold, hence also after weighted averaging. -/
def foldErrorExact (D : VisibilityToErrorTwoSidedData) : Prop :=
  D.foldError = ∑ y : D.Y, D.fiberWeight y * min (D.posterior y) (1 - D.posterior y)

/-- Lower bound: the residual Bernoulli variance is bounded above by the Bayes error. -/
def foldErrorLowerBound (D : VisibilityToErrorTwoSidedData) : Prop :=
  D.foldVisibilityResidual ≤ D.foldError

/-- Upper bound: the Bayes error is bounded above by twice the residual Bernoulli variance. -/
def foldErrorUpperBound (D : VisibilityToErrorTwoSidedData) : Prop :=
  D.foldError ≤ 2 * D.foldVisibilityResidual

lemma threshold_error_eq_min (D : VisibilityToErrorTwoSidedData) (y : D.Y) :
    D.foldErrorTerm y = min (D.posterior y) (1 - D.posterior y) := by
  rcases D.posterior_mem_unitInterval y with ⟨hp0, hp1⟩
  by_cases hhalf : (1 / 2 : ℝ) ≤ D.posterior y
  · have hmin : min (D.posterior y) (1 - D.posterior y) = 1 - D.posterior y := by
      apply min_eq_right
      nlinarith
    rw [foldErrorTerm, if_pos hhalf, hmin]
  · have hlt : D.posterior y < 1 / 2 := by
      linarith
    have hmin : min (D.posterior y) (1 - D.posterior y) = D.posterior y := by
      apply min_eq_left
      nlinarith
    rw [foldErrorTerm, if_neg hhalf, hmin]

lemma residual_le_min (D : VisibilityToErrorTwoSidedData) (y : D.Y) :
    D.visibilityResidualTerm y ≤ min (D.posterior y) (1 - D.posterior y) := by
  rcases D.posterior_mem_unitInterval y with ⟨hp0, hp1⟩
  by_cases hhalf : (1 / 2 : ℝ) ≤ D.posterior y
  · have hmin : min (D.posterior y) (1 - D.posterior y) = 1 - D.posterior y := by
      apply min_eq_right
      nlinarith
    rw [hmin, visibilityResidualTerm]
    nlinarith
  · have hlt : D.posterior y < 1 / 2 := by
      linarith
    have hmin : min (D.posterior y) (1 - D.posterior y) = D.posterior y := by
      apply min_eq_left
      nlinarith
    rw [hmin, visibilityResidualTerm]
    nlinarith

lemma min_le_two_residual (D : VisibilityToErrorTwoSidedData) (y : D.Y) :
    min (D.posterior y) (1 - D.posterior y) ≤ 2 * D.visibilityResidualTerm y := by
  rcases D.posterior_mem_unitInterval y with ⟨hp0, hp1⟩
  by_cases hhalf : (1 / 2 : ℝ) ≤ D.posterior y
  · have hmin : min (D.posterior y) (1 - D.posterior y) = 1 - D.posterior y := by
      apply min_eq_right
      nlinarith
    rw [hmin, visibilityResidualTerm]
    nlinarith
  · have hlt : D.posterior y < 1 / 2 := by
      linarith
    have hmin : min (D.posterior y) (1 - D.posterior y) = D.posterior y := by
      apply min_eq_left
      nlinarith
    rw [hmin, visibilityResidualTerm]
    nlinarith

lemma foldErrorExact_proof (D : VisibilityToErrorTwoSidedData) : D.foldErrorExact := by
  unfold foldErrorExact foldError
  refine Finset.sum_congr rfl ?_
  intro y hy
  rw [D.threshold_error_eq_min y]

lemma foldErrorLowerBound_proof (D : VisibilityToErrorTwoSidedData) : D.foldErrorLowerBound := by
  unfold foldErrorLowerBound foldVisibilityResidual
  rw [D.foldErrorExact_proof]
  exact Finset.sum_le_sum fun y hy =>
    mul_le_mul_of_nonneg_left (D.residual_le_min y) (D.weight_nonneg y)

lemma foldErrorUpperBound_proof (D : VisibilityToErrorTwoSidedData) : D.foldErrorUpperBound := by
  unfold foldErrorUpperBound foldVisibilityResidual
  rw [D.foldErrorExact_proof]
  calc
    (∑ y : D.Y, D.fiberWeight y * min (D.posterior y) (1 - D.posterior y)) ≤
        ∑ y : D.Y, D.fiberWeight y * (2 * D.visibilityResidualTerm y) := by
          refine Finset.sum_le_sum ?_
          intro y hy
          exact mul_le_mul_of_nonneg_left (D.min_le_two_residual y) (D.weight_nonneg y)
    _ = 2 * ∑ y : D.Y, D.fiberWeight y * D.visibilityResidualTerm y := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro y hy
          ring

end VisibilityToErrorTwoSidedData

open VisibilityToErrorTwoSidedData

/-- Thresholding the posterior gives the exact foldwise Bayes error `min(p, 1 - p)`, and this
error is sandwiched between the residual Bernoulli variance and twice that residual variance.
    thm:pom-visibility-to-error-two-sided -/
theorem paper_pom_visibility_to_error_two_sided (D : VisibilityToErrorTwoSidedData) :
    D.foldErrorExact ∧ D.foldErrorLowerBound ∧ D.foldErrorUpperBound := by
  exact ⟨D.foldErrorExact_proof, D.foldErrorLowerBound_proof, D.foldErrorUpperBound_proof⟩

end

end Omega.POM
