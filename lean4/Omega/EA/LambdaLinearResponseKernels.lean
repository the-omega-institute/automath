import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic
import Omega.EA.KernelOneSiteBernoulliClass

namespace Omega.EA

noncomputable section

/-- First-order linear response at `u = 0` for a one-state kernel family. -/
def LambdaLinearResponse (K : KernelPressureFamily) (c : ℝ) : Prop :=
  HasDerivAt (fun u => perronRoot K u) c 0

/-- The audited `K9` endpoint family. -/
def k9LinearResponseFamily : KernelPressureFamily where
  zeroWeight := 7
  oneWeight := k9Endpoint
  monotone_weights := by
    rw [k9_endpoint_value]
    norm_num

/-- The audited `K13` endpoint family. -/
def k13LinearResponseFamily : KernelPressureFamily where
  zeroWeight := 3
  oneWeight := k13Endpoint
  monotone_weights := by
    norm_num [k13Endpoint]

/-- The audited `K21` endpoint family. -/
def k21LinearResponseFamily : KernelPressureFamily where
  zeroWeight := 1
  oneWeight := k21Endpoint
  monotone_weights := by
    norm_num [k21Endpoint]

/-- The first-order coefficient for the `K9` kernel is `14`. -/
def LambdaLinearResponseK9 : Prop :=
  LambdaLinearResponse k9LinearResponseFamily 14

/-- The first-order coefficient for the `K13` kernel is `10`. -/
def LambdaLinearResponseK13 : Prop :=
  LambdaLinearResponse k13LinearResponseFamily 10

/-- The first-order coefficient for the `K21` kernel is `4`. -/
def LambdaLinearResponseK21 : Prop :=
  LambdaLinearResponse k21LinearResponseFamily 4

lemma kernelPressure_linearResponse (K : KernelPressureFamily) :
    LambdaLinearResponse K (K.oneWeight - K.zeroWeight) := by
  simpa [LambdaLinearResponse, perronRoot, weightedKernel, sub_eq_add_neg, add_assoc, add_comm,
    add_left_comm, mul_assoc, mul_comm, mul_left_comm] using
    (((hasDerivAt_id 0).const_mul (K.oneWeight - K.zeroWeight)).const_add K.zeroWeight)

/-- Paper label: `cor:lambda-linear-response-kernels`. The audited kernels `K9`, `K13`, and `K21`
inherit the linear-response coefficient given by the endpoint difference of their one-state kernel
interpolations. -/
theorem paper_lambda_linear_response_kernels :
    LambdaLinearResponseK9 ∧ LambdaLinearResponseK13 ∧ LambdaLinearResponseK21 := by
  refine ⟨?_, ?_, ?_⟩
  · have hcoeff : k9LinearResponseFamily.oneWeight - k9LinearResponseFamily.zeroWeight = 14 := by
      norm_num [k9LinearResponseFamily, k9_endpoint_value]
    simpa [LambdaLinearResponseK9] using hcoeff ▸
      kernelPressure_linearResponse k9LinearResponseFamily
  · have hcoeff : k13LinearResponseFamily.oneWeight - k13LinearResponseFamily.zeroWeight = 10 := by
      norm_num [k13LinearResponseFamily, k13Endpoint]
    simpa [LambdaLinearResponseK13] using hcoeff ▸
      kernelPressure_linearResponse k13LinearResponseFamily
  · have hcoeff : k21LinearResponseFamily.oneWeight - k21LinearResponseFamily.zeroWeight = 4 := by
      norm_num [k21LinearResponseFamily, k21Endpoint]
    simpa [LambdaLinearResponseK21] using hcoeff ▸
      kernelPressure_linearResponse k21LinearResponseFamily

end

end Omega.EA
