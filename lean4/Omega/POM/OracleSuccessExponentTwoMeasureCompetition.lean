import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- Critical order of the quadratic failure branch used inside the success competition. -/
def pom_oracle_success_exponent_two_measure_competition_criticalOrder
    (α slope curvature : ℝ) : ℝ :=
  1 + (α * Real.log 2 - slope) / curvature

/-- Quadratic failure branch inherited from the thermodynamic conjugacy model. -/
def pom_oracle_success_exponent_two_measure_competition_failureBranch
    (α slope offset curvature : ℝ) : ℝ :=
  Real.log 2 - offset + (α * Real.log 2 - slope) ^ 2 / (2 * curvature)

/-- Chernoff objective for the same quadratic branch. -/
def pom_oracle_success_exponent_two_measure_competition_failureObjective
    (α slope offset curvature q : ℝ) : ℝ :=
  Real.log 2 - offset + (α * Real.log 2 - slope) * (q - 1) -
    curvature / 2 * (q - 1) ^ 2

/-- Uniform-measure tail branch entering the success-exponent competition. -/
def pom_oracle_success_exponent_two_measure_competition_uniformBranch
    (α offset slope curvature : ℝ) : ℝ :=
  (1 - α) * Real.log 2 - Real.log Real.goldenRatio +
    offset + (α * Real.log 2 - slope) ^ 2 / (2 * curvature)

/-- Success exponent as the minimum of the `w`-branch and the uniform-measure branch. -/
def pom_oracle_success_exponent_two_measure_competition_successExponent
    (α failureSlope failureOffset failureCurvature uniformOffset uniformSlope uniformCurvature :
      ℝ) : ℝ :=
  min
    (pom_oracle_success_exponent_two_measure_competition_failureBranch
      α failureSlope failureOffset failureCurvature)
    (pom_oracle_success_exponent_two_measure_competition_uniformBranch
      α uniformOffset uniformSlope uniformCurvature)

/-- First derivative of the smooth failure branch with respect to `α`. -/
def pom_oracle_success_exponent_two_measure_competition_failurePrime
    (α slope curvature : ℝ) : ℝ :=
  ((α * Real.log 2 - slope) / curvature) * Real.log 2

/-- Second derivative of the smooth failure branch with respect to `α`. -/
def pom_oracle_success_exponent_two_measure_competition_failureSecond
    (curvature : ℝ) : ℝ :=
  (Real.log 2) ^ 2 / curvature

private lemma pom_oracle_success_exponent_two_measure_competition_objective_completeSquare
    (α slope offset curvature q : ℝ) (hcurv : 0 < curvature) :
    pom_oracle_success_exponent_two_measure_competition_failureObjective α slope offset curvature q =
      pom_oracle_success_exponent_two_measure_competition_failureBranch
        α slope offset curvature -
        curvature / 2 *
          (q -
            pom_oracle_success_exponent_two_measure_competition_criticalOrder
              α slope curvature) ^ 2 := by
  have hcurv_ne : curvature ≠ 0 := ne_of_gt hcurv
  unfold pom_oracle_success_exponent_two_measure_competition_failureObjective
    pom_oracle_success_exponent_two_measure_competition_failureBranch
    pom_oracle_success_exponent_two_measure_competition_criticalOrder
  field_simp [hcurv_ne]
  ring

/-- Paper label: `thm:pom-oracle-success-exponent-two-measure-competition`.
The concrete success exponent is the minimum of the `w`-branch and uniform-tail branch; on the
thermodynamic branch, the quadratic objective has a unique maximizer and the expected `E`, `E'`,
`E''` formulas. -/
theorem paper_pom_oracle_success_exponent_two_measure_competition
    (α failureSlope failureOffset failureCurvature uniformOffset uniformSlope uniformCurvature :
      ℝ)
    (hfailureCurv : 0 < failureCurvature)
    (_huniformCurv : 0 < uniformCurvature)
    (hα : failureSlope < α * Real.log 2) :
    let qStar :=
      pom_oracle_success_exponent_two_measure_competition_criticalOrder
        α failureSlope failureCurvature
    let E :=
      pom_oracle_success_exponent_two_measure_competition_failureBranch
        α failureSlope failureOffset failureCurvature
    let U :=
      pom_oracle_success_exponent_two_measure_competition_uniformBranch
        α uniformOffset uniformSlope uniformCurvature
    let S :=
      pom_oracle_success_exponent_two_measure_competition_successExponent
        α failureSlope failureOffset failureCurvature
          uniformOffset uniformSlope uniformCurvature
    S = min E U ∧
      (∃! q : ℝ, 1 < q ∧
        pom_oracle_success_exponent_two_measure_competition_failureObjective
          α failureSlope failureOffset failureCurvature q = E) ∧
      pom_oracle_success_exponent_two_measure_competition_failurePrime
          α failureSlope failureCurvature = (qStar - 1) * Real.log 2 ∧
      pom_oracle_success_exponent_two_measure_competition_failureSecond failureCurvature =
        (Real.log 2) ^ 2 / failureCurvature ∧
      0 < pom_oracle_success_exponent_two_measure_competition_failureSecond
            failureCurvature ∧
      0 <
        pom_oracle_success_exponent_two_measure_competition_criticalOrder
          α failureSlope failureCurvature - 1 ∧
      0 <
        pom_oracle_success_exponent_two_measure_competition_failureSecond failureCurvature ∧
      (E ≤ U → S = E) ∧
      (U ≤ E → S = U) := by
  dsimp
  have hcurv_ne : failureCurvature ≠ 0 := ne_of_gt hfailureCurv
  have hdelta_pos : 0 < α * Real.log 2 - failureSlope := by
    linarith
  have hqStar_gt :
      1 <
        pom_oracle_success_exponent_two_measure_competition_criticalOrder
          α failureSlope failureCurvature := by
    unfold pom_oracle_success_exponent_two_measure_competition_criticalOrder
    have hfrac_pos :
        0 < (α * Real.log 2 - failureSlope) / failureCurvature := by
      exact div_pos hdelta_pos hfailureCurv
    linarith
  refine ⟨rfl, ?_, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · refine
      ⟨pom_oracle_success_exponent_two_measure_competition_criticalOrder
          α failureSlope failureCurvature, ?_, ?_⟩
    · refine ⟨hqStar_gt, ?_⟩
      rw [pom_oracle_success_exponent_two_measure_competition_objective_completeSquare
        α failureSlope failureOffset failureCurvature
        (pom_oracle_success_exponent_two_measure_competition_criticalOrder
          α failureSlope failureCurvature)
        hfailureCurv]
      simp
    · intro q hq
      rcases hq with ⟨hq_gt, hqE⟩
      have hsquare :
          (q -
            pom_oracle_success_exponent_two_measure_competition_criticalOrder
              α failureSlope failureCurvature) ^ 2 = 0 := by
        rw [pom_oracle_success_exponent_two_measure_competition_objective_completeSquare
          α failureSlope failureOffset failureCurvature q hfailureCurv] at hqE
        have hcoef_pos : 0 < failureCurvature / 2 := by positivity
        nlinarith
      have hqeq :
          q =
            pom_oracle_success_exponent_two_measure_competition_criticalOrder
              α failureSlope failureCurvature := by
        nlinarith
      exact hqeq
  · unfold pom_oracle_success_exponent_two_measure_competition_failurePrime
      pom_oracle_success_exponent_two_measure_competition_criticalOrder
    field_simp [hcurv_ne]
    ring
  · unfold pom_oracle_success_exponent_two_measure_competition_failureSecond
    positivity
  · unfold pom_oracle_success_exponent_two_measure_competition_criticalOrder
    have hfrac_pos :
        0 < (α * Real.log 2 - failureSlope) / failureCurvature := by
      exact div_pos hdelta_pos hfailureCurv
    linarith
  · unfold pom_oracle_success_exponent_two_measure_competition_failureSecond
    positivity
  · refine ⟨?_, ?_⟩
    · intro hEU
      exact min_eq_left hEU
    · intro hUE
      exact min_eq_right hUE

end

end Omega.POM
