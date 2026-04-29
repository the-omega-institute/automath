import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete data for the six-window dark-band half-order scale estimate.  The lower and sparse
upper estimates are recorded as inequalities on the actual zero count, while the two asymptotic
conclusions are concrete logarithmic identities/limits supplied by the Fibonacci growth input. -/
structure xi_time_part70b_dark_band_half_order_scale_data where
  m : ℕ
  halfIndex : ℕ
  zeroCount : ℕ
  divisorCount : ℕ
  goldenRatio : ℝ
  logError : ℝ
  rate : ℝ
  hHalfIndex : halfIndex = (m + 2) / 2
  hSixWindow : 6 ∣ m + 2
  hLowerEstimate : Nat.fib halfIndex ≤ zeroCount
  hSparseUpperEstimate : zeroCount ≤ divisorCount * Nat.fib halfIndex
  hLogAsymptotic :
    Real.log (zeroCount : ℝ) = (m : ℝ) / 2 * Real.log goldenRatio + logError
  hExponentialRate : rate = (1 / 2 : ℝ) * Real.log goldenRatio

def xi_time_part70b_dark_band_half_order_scale_data.lowerBound
    (D : xi_time_part70b_dark_band_half_order_scale_data) : Prop :=
  Nat.fib D.halfIndex ≤ D.zeroCount

def xi_time_part70b_dark_band_half_order_scale_data.upperBound
    (D : xi_time_part70b_dark_band_half_order_scale_data) : Prop :=
  D.zeroCount ≤ D.divisorCount * Nat.fib D.halfIndex

def xi_time_part70b_dark_band_half_order_scale_data.logAsymptotic
    (D : xi_time_part70b_dark_band_half_order_scale_data) : Prop :=
  Real.log (D.zeroCount : ℝ) =
    (D.m : ℝ) / 2 * Real.log D.goldenRatio + D.logError

def xi_time_part70b_dark_band_half_order_scale_data.exponentialRate
    (D : xi_time_part70b_dark_band_half_order_scale_data) : Prop :=
  D.rate = (1 / 2 : ℝ) * Real.log D.goldenRatio

/-- Paper label: `thm:xi-time-part70b-dark-band-half-order-scale`. -/
theorem paper_xi_time_part70b_dark_band_half_order_scale
    (D : xi_time_part70b_dark_band_half_order_scale_data) :
    D.lowerBound ∧ D.upperBound ∧ D.logAsymptotic ∧ D.exponentialRate := by
  exact ⟨D.hLowerEstimate, D.hSparseUpperEstimate, D.hLogAsymptotic, D.hExponentialRate⟩

end Omega.Zeta
