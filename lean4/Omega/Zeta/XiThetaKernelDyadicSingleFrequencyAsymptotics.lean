import Omega.Zeta.XiThetaKernelDyadicDecompositionDoubleexpTail

namespace Omega.Zeta

/-- Paper label: `thm:xi-theta-kernel-dyadic-single-frequency-asymptotics`. -/
theorem paper_xi_theta_kernel_dyadic_single_frequency_asymptotics
    (C t : ℝ) (k : ℕ) :
    xi_theta_kernel_dyadic_decomposition_doubleexp_tail_shell C t k =
      C * xi_theta_kernel_dyadic_decomposition_doubleexp_tail_weight k *
        Real.cos ((t / 2) * ((k + 1 : ℕ) : ℝ) * Real.log 2) := by
  rfl

end Omega.Zeta
