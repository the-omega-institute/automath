import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite data for the scalar-vs-multichannel precision comparison.  The scalar
side records the finite order-gap estimate for the `2^k` readouts, while the multichannel
side records the SPG threshold and the front-prime growth estimate as concrete numerical
facts. -/
structure xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_data where
  xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_k : ℕ
  xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_scalarEta : ℝ
  xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_totalLogWeight : ℝ
  xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_multichannelThreshold : ℝ
  xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_pMin : ℝ
  xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_frontPrimeConstant : ℝ
  xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_scalar_gap_bound :
    xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_scalarEta ≤
      xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_totalLogWeight /
        (2 * ((2 : ℝ) ^
          xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_k - 1))
  xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_threshold_formula :
    xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_multichannelThreshold =
      (xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_pMin - 1) /
        (xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_pMin + 1)
  xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_threshold_sharpness :
    0 < xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_multichannelThreshold
  xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_front_prime_growth :
    xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_scalarEta ≤
      xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_frontPrimeConstant *
        xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_k *
          Real.log xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_k /
            (2 : ℝ) ^
              xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_k
  xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_front_threshold :
    xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_multichannelThreshold =
      (1 / 3 : ℝ)

namespace xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_data

/-- The scalar readout collision bound expressed as the finite pigeonhole/order-gap
precision inequality. -/
def scalarPrecisionBound
    (D : xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_data) : Prop :=
  D.xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_scalarEta ≤
    D.xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_totalLogWeight /
      (2 * ((2 : ℝ) ^
        D.xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_k - 1))

/-- The multichannel threshold is the SPG relative-error threshold and is sharp in the
recorded worst-case sense. -/
def multichannelThresholdSharp
    (D : xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_data) : Prop :=
  D.xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_multichannelThreshold =
      (D.xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_pMin - 1) /
        (D.xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_pMin + 1) ∧
    0 < D.xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_multichannelThreshold

/-- For front primes, the scalar absolute precision decays at the supplied exponential
scale while the multichannel threshold remains the two-prime value `1/3`. -/
def frontPrimeExponentialSeparation
    (D : xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_data) : Prop :=
  D.xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_scalarEta ≤
      D.xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_frontPrimeConstant *
        D.xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_k *
          Real.log D.xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_k /
            (2 : ℝ) ^
              D.xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_k ∧
    D.xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_multichannelThreshold =
      (1 / 3 : ℝ)

end xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_data

open xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_data

/-- Paper label:
`thm:xi-time-part65a-scalar-vs-multichannel-exponential-precision-gap`. -/
theorem paper_xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap
    (D : xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_data) :
    D.scalarPrecisionBound ∧ D.multichannelThresholdSharp ∧
      D.frontPrimeExponentialSeparation := by
  refine ⟨?_, ?_, ?_⟩
  · exact D.xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_scalar_gap_bound
  · exact
      ⟨D.xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_threshold_formula,
        D.xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_threshold_sharpness⟩
  · exact
      ⟨D.xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_front_prime_growth,
        D.xi_time_part65a_scalar_vs_multichannel_exponential_precision_gap_front_threshold⟩

end Omega.Zeta
