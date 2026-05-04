import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

open Filter

namespace Omega.Zeta

/-- A finite endpoint heat probe split into its endpoint atom and a single dominated tail mass. -/
def xi_endpoint_heat_probe_monotone_limit_gap_sequence
    (endpointMass tailMass r : ℝ) (N : ℕ) : ℝ :=
  endpointMass + tailMass * r ^ N

/-- The tail error after subtracting the endpoint atom. -/
def xi_endpoint_heat_probe_monotone_limit_gap_error
    (endpointMass tailMass r : ℝ) (N : ℕ) : ℝ :=
  xi_endpoint_heat_probe_monotone_limit_gap_sequence endpointMass tailMass r N - endpointMass

/-- Paper label: `cor:xi-endpoint-heat-probe-monotone-limit-gap`.
For an endpoint atom plus a nonnegative tail dominated by a ratio `r < 1`, the heat-probe sequence
is decreasing, converges to the endpoint atom mass, and its spectral-gap error is exponentially
bounded by the dominated tail. -/
theorem paper_xi_endpoint_heat_probe_monotone_limit_gap
    (endpointMass tailMass r : ℝ) (htail : 0 ≤ tailMass) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Antitone (xi_endpoint_heat_probe_monotone_limit_gap_sequence endpointMass tailMass r) ∧
      Tendsto (xi_endpoint_heat_probe_monotone_limit_gap_sequence endpointMass tailMass r) atTop
        (nhds endpointMass) ∧
      ∀ N : ℕ,
        0 ≤ xi_endpoint_heat_probe_monotone_limit_gap_error endpointMass tailMass r N ∧
          xi_endpoint_heat_probe_monotone_limit_gap_error endpointMass tailMass r N ≤
            r ^ N * tailMass := by
  have hr_le_one : r ≤ 1 := le_of_lt hr1
  have hanti :
      Antitone (xi_endpoint_heat_probe_monotone_limit_gap_sequence endpointMass tailMass r) := by
    intro m n hmn
    have hpow : r ^ n ≤ r ^ m := pow_le_pow_of_le_one hr0 hr_le_one hmn
    have hmul : tailMass * r ^ n ≤ tailMass * r ^ m :=
      mul_le_mul_of_nonneg_left hpow htail
    simpa [xi_endpoint_heat_probe_monotone_limit_gap_sequence] using
      add_le_add_left hmul endpointMass
  have hpow_zero : Tendsto (fun N : ℕ => r ^ N) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  have hlimit :
      Tendsto (xi_endpoint_heat_probe_monotone_limit_gap_sequence endpointMass tailMass r) atTop
        (nhds endpointMass) := by
    have htail_zero : Tendsto (fun N : ℕ => tailMass * r ^ N) atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul hpow_zero
    simpa [xi_endpoint_heat_probe_monotone_limit_gap_sequence] using
      tendsto_const_nhds.add htail_zero
  refine ⟨hanti, hlimit, ?_⟩
  intro N
  have hpow_nonneg : 0 ≤ r ^ N := pow_nonneg hr0 N
  constructor
  · simp [xi_endpoint_heat_probe_monotone_limit_gap_error,
      xi_endpoint_heat_probe_monotone_limit_gap_sequence, mul_nonneg htail hpow_nonneg]
  · have hcomm : tailMass * r ^ N = r ^ N * tailMass := mul_comm tailMass (r ^ N)
    simp [xi_endpoint_heat_probe_monotone_limit_gap_error,
      xi_endpoint_heat_probe_monotone_limit_gap_sequence, hcomm]

end Omega.Zeta
