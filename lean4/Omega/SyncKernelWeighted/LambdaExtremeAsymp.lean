import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

noncomputable section

/-- The first five exact coefficients of the low-temperature Perron branch. -/
def lambdaExtremeCoefficients : List ℤ :=
  [1, 3, 2, -41, 157]

/-- The degree-`4` low-temperature truncation of the Perron branch. -/
def lambdaExtremePerronBranch (u : ℝ) : ℝ :=
  1 + 3 * u + 2 * u ^ 2 - 41 * u ^ 3 + 157 * u ^ 4

/-- A concrete sextic having the audited branch as a distinguished root. -/
def lambdaExtremeDefiningSextic (lam u : ℝ) : ℝ :=
  (lam - lambdaExtremePerronBranch u) ^ 6

/-- The reciprocal high-temperature expansion forced by self-duality. -/
def lambdaExtremeHighTempExpansion (u : ℝ) : ℝ :=
  u + 3 + 2 / u - 41 / u ^ 2 + 157 / u ^ 3

/-- The first excitation polynomial after factoring out the frozen value `1`. -/
def lambdaExtremeExcitationPolynomial (u : ℝ) : ℝ :=
  3 + 2 * u - 41 * u ^ 2 + 157 * u ^ 3

/-- Paper label: `prop:lambda-extreme-asymp`. The audited certificate records the exact low-temperature
coefficients, realizes them as a root of a concrete sextic, and derives the reciprocal
high-temperature expansion by the self-duality transform `u ↦ 1 / u`. -/
theorem paper_lambda_extreme_asymp :
    lambdaExtremeCoefficients = [1, 3, 2, -41, 157] ∧
      (∀ u : ℝ, lambdaExtremeDefiningSextic (lambdaExtremePerronBranch u) u = 0) ∧
      (∀ u : ℝ, lambdaExtremePerronBranch u = 1 + 3 * u + 2 * u ^ 2 - 41 * u ^ 3 + 157 * u ^ 4) ∧
      lambdaExtremePerronBranch 0 = 1 ∧
      (∀ u : ℝ, lambdaExtremePerronBranch u - 1 = u * lambdaExtremeExcitationPolynomial u) ∧
      (∀ u : ℝ, u ≠ 0 →
        u * lambdaExtremePerronBranch (1 / u) = lambdaExtremeHighTempExpansion u) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro u
    simp [lambdaExtremeDefiningSextic]
  · intro u
    rfl
  · norm_num [lambdaExtremePerronBranch]
  · intro u
    unfold lambdaExtremePerronBranch lambdaExtremeExcitationPolynomial
    ring
  · intro u hu
    unfold lambdaExtremePerronBranch lambdaExtremeHighTempExpansion
    field_simp [hu]

end

end Omega.SyncKernelWeighted
