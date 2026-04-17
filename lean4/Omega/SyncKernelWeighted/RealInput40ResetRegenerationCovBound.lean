import Mathlib.Tactic
import Omega.SyncKernelWeighted.RealInput40ResetRegenerationConstants
import Omega.SyncKernelWeighted.RealInput40ResetRegenerationTail

namespace Omega.SyncKernelWeighted

noncomputable section

/-- Numerical Perron-root certificate recorded in the reset-regeneration tail audit. -/
def realInput40ResetRegenerationPerronRoot : ℝ :=
  0.99287370928195

/-- Numerical geometric prefactor recorded in the reset-regeneration tail audit. -/
def realInput40ResetRegenerationTailConstant : ℝ :=
  1.00034766355732

/-- Concrete data for the reset-regeneration covariance estimate. `covariance n` records the
lag-`n` covariance of a bounded observable and `tailProb n` records the regeneration tail
probability `P(T > n)`. -/
structure RealInput40ResetRegenerationCovBoundData where
  observableSup : ℝ
  covariance : ℕ → ℝ
  tailProb : ℕ → ℝ
  tailControlsCovariance :
    ∀ n, |covariance n| ≤ 2 * observableSup ^ 2 * tailProb n
  tailProb_le_geometric :
    ∀ n,
      tailProb n ≤ realInput40ResetRegenerationTailConstant *
        realInput40ResetRegenerationPerronRoot ^ n

namespace RealInput40ResetRegenerationCovBoundData

/-- The covariance is controlled by the regeneration-tail event `{T > n}`. -/
def pointwiseCovarianceBound (D : RealInput40ResetRegenerationCovBoundData) : Prop :=
  ∀ n, |D.covariance n| ≤ 2 * D.observableSup ^ 2 * D.tailProb n

/-- Combining the tail-event control with the explicit Perron-root tail law yields a geometric
covariance decay bound. -/
def exponentialCovarianceBound (D : RealInput40ResetRegenerationCovBoundData) : Prop :=
  ∀ n,
    |D.covariance n| ≤
      2 * realInput40ResetRegenerationTailConstant * D.observableSup ^ 2 *
        realInput40ResetRegenerationPerronRoot ^ n

end RealInput40ResetRegenerationCovBoundData

open RealInput40ResetRegenerationCovBoundData

/-- Reset-regeneration covariance control for bounded observables in the real-input-40 model:
first by the tail event `{T > n}`, then by the explicit geometric tail bound.
    cor:real-input-40-reset-regeneration-cov-bound -/
theorem paper_real_input_40_reset_regeneration_cov_bound
    (D : RealInput40ResetRegenerationCovBoundData) :
    D.pointwiseCovarianceBound ∧ D.exponentialCovarianceBound := by
  constructor
  · exact D.tailControlsCovariance
  · intro n
    have hScale : 0 ≤ 2 * D.observableSup ^ 2 := by
      nlinarith [sq_nonneg D.observableSup]
    calc
      |D.covariance n| ≤ 2 * D.observableSup ^ 2 * D.tailProb n := D.tailControlsCovariance n
      _ ≤ 2 * D.observableSup ^ 2 *
          (realInput40ResetRegenerationTailConstant *
            realInput40ResetRegenerationPerronRoot ^ n) :=
        mul_le_mul_of_nonneg_left (D.tailProb_le_geometric n) hScale
      _ = 2 * realInput40ResetRegenerationTailConstant * D.observableSup ^ 2 *
          realInput40ResetRegenerationPerronRoot ^ n := by ring

end

end Omega.SyncKernelWeighted
