import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

noncomputable section

/-- Concrete endpoint data for a monotone affine pressure curve and its tensor-power uplift. -/
structure LambdaEndpointsMonotoneUpliftData where
  carryFreeRadius : ℝ
  alphabetSize : ℝ
  copies : ℕ
  slope : ℝ
  slope_nonneg : 0 ≤ slope
  endpoint_one : carryFreeRadius + slope = alphabetSize

/-- The single-flow weighted spectral-radius model. -/
def lambdaFlowSpectralRadius (D : LambdaEndpointsMonotoneUpliftData) (u : ℝ) : ℝ :=
  D.carryFreeRadius + u * D.slope

/-- The tensor-power uplift across `D.copies` independent flows. -/
def lambdaGlobalSpectralRadius (D : LambdaEndpointsMonotoneUpliftData) (u : ℝ) : ℝ :=
  (lambdaFlowSpectralRadius D u) ^ D.copies

/-- Concrete statement packaging the endpoint identities, monotonicity, and tensor-power uplift. -/
def LambdaEndpointsMonotoneUpliftStatement (D : LambdaEndpointsMonotoneUpliftData) : Prop :=
  lambdaFlowSpectralRadius D 0 = D.carryFreeRadius ∧
    lambdaFlowSpectralRadius D 1 = D.alphabetSize ∧
    Monotone (lambdaFlowSpectralRadius D) ∧
    ∀ u : ℝ, lambdaGlobalSpectralRadius D u = (lambdaFlowSpectralRadius D u) ^ D.copies

/-- Paper label: `prop:lambda-endpoints-monotone-uplift`.
The affine one-flow spectral-radius model has the expected endpoint values, is monotone when the
slope is nonnegative, and tensor-power assembly raises the flow radius to the `copies`th power. -/
theorem paper_lambda_endpoints_monotone_uplift (D : LambdaEndpointsMonotoneUpliftData) :
    LambdaEndpointsMonotoneUpliftStatement D := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [lambdaFlowSpectralRadius]
  · simpa [lambdaFlowSpectralRadius] using D.endpoint_one
  · intro u v huv
    unfold lambdaFlowSpectralRadius
    have hmul : u * D.slope ≤ v * D.slope := mul_le_mul_of_nonneg_right huv D.slope_nonneg
    linarith
  · intro u
    rfl

end

end Omega.SyncKernelWeighted
