import Omega.OperatorAlgebra.HzomCommutingPolarForcesCriticalLine

namespace Omega.OperatorAlgebra

/-- Paper-facing wrapper for the common unitary dilation criterion in the HZOM framework.
    prop:op-algebra-common-unitary-dilation-criterion -/
theorem paper_op_algebra_common_unitary_dilation_criterion {lam theta κ : ℝ}
    (hdilation : hzomStrictPolarContraction κ)
    (hreflect : hzomReflectionSymmetricZeroSet lam theta κ) :
    hzomRightHalfPlaneZeroFree lam theta κ ∧ hzomCriticalLineConcentration lam theta κ := by
  exact paper_op_algebra_hzom_commuting_polar_forces_critical_line hdilation hreflect

end Omega.OperatorAlgebra
