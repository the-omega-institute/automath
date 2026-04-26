import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete error-control package for the de Branges zero-process limit. The horizon error is
the audited uniformity defect, while the determinantal and sine-kernel errors are bounded by it. -/
structure xi_debranges_dpp_sine_kernel_limit_data where
  xi_debranges_dpp_sine_kernel_limit_horizonError : ℕ → ℚ
  xi_debranges_dpp_sine_kernel_limit_zeroProcessError : ℕ → ℚ
  xi_debranges_dpp_sine_kernel_limit_sineKernelError : ℕ → ℚ
  xi_debranges_dpp_sine_kernel_limit_zeroProcessError_le_horizonError :
    ∀ n : ℕ,
      xi_debranges_dpp_sine_kernel_limit_zeroProcessError n ≤
        xi_debranges_dpp_sine_kernel_limit_horizonError n
  xi_debranges_dpp_sine_kernel_limit_sineKernelError_le_horizonError :
    ∀ n : ℕ,
      xi_debranges_dpp_sine_kernel_limit_sineKernelError n ≤
        xi_debranges_dpp_sine_kernel_limit_horizonError n

namespace xi_debranges_dpp_sine_kernel_limit_data

/-- Horizon uniformity is encoded as nonpositive uniformity defect at every finite horizon. -/
def horizonUniformity (D : xi_debranges_dpp_sine_kernel_limit_data) : Prop :=
  ∀ n : ℕ, D.xi_debranges_dpp_sine_kernel_limit_horizonError n ≤ 0

/-- The determinantal zero-process conclusion is vanishing of the corresponding defect. -/
def determinantalZeroProcess (D : xi_debranges_dpp_sine_kernel_limit_data) : Prop :=
  ∀ n : ℕ, D.xi_debranges_dpp_sine_kernel_limit_zeroProcessError n ≤ 0

/-- The sine-kernel scaling conclusion is vanishing of the local scaling defect. -/
def sineKernelScalingLimit (D : xi_debranges_dpp_sine_kernel_limit_data) : Prop :=
  ∀ n : ℕ, D.xi_debranges_dpp_sine_kernel_limit_sineKernelError n ≤ 0

end xi_debranges_dpp_sine_kernel_limit_data

open xi_debranges_dpp_sine_kernel_limit_data

/-- Paper label: `prop:xi-debranges-dpp-sine-kernel-limit`. Horizon-uniform error control
simultaneously bounds the determinantal zero-process defect and the sine-kernel scaling defect. -/
theorem paper_xi_debranges_dpp_sine_kernel_limit
    (D : xi_debranges_dpp_sine_kernel_limit_data) :
    D.horizonUniformity → D.determinantalZeroProcess ∧ D.sineKernelScalingLimit := by
  intro hhorizon
  constructor
  · intro n
    exact le_trans
      (D.xi_debranges_dpp_sine_kernel_limit_zeroProcessError_le_horizonError n)
      (hhorizon n)
  · intro n
    exact le_trans
      (D.xi_debranges_dpp_sine_kernel_limit_sineKernelError_le_horizonError n)
      (hhorizon n)

end Omega.Zeta
