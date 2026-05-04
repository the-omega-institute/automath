import Mathlib.Tactic

noncomputable section

namespace Omega.Zeta

/-- The reciprocal endpoint probe model with leading power `p = 1`. -/
def xi_endpoint_heat_probe_powerlaw_differences_model (m c : ℝ) (N : ℕ) : ℝ :=
  m + c / ((N : ℝ) + 1)

/-- First forward finite difference for endpoint probe samples. -/
def xi_endpoint_heat_probe_powerlaw_differences_firstDiff (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  a N - a (N + 1)

/-- Centered second finite difference for endpoint probe samples. -/
def xi_endpoint_heat_probe_powerlaw_differences_secondDiff (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  a (N - 1) - 2 * a N + a (N + 1)

/-- Concrete finite-difference statement for the reciprocal power-law endpoint model.
The exact formulas are the discrete main terms whose large-`N` expansions give
`c * N⁻²` and `2 * c * N⁻³`, i.e. the paper's formulas at `p = 1`. -/
def xi_endpoint_heat_probe_powerlaw_differences_statement : Prop :=
  ∀ (m c : ℝ) (N : ℕ), 0 < N →
    xi_endpoint_heat_probe_powerlaw_differences_firstDiff
        (xi_endpoint_heat_probe_powerlaw_differences_model m c) N =
      c / (((N : ℝ) + 1) * ((N : ℝ) + 2)) ∧
    xi_endpoint_heat_probe_powerlaw_differences_secondDiff
        (xi_endpoint_heat_probe_powerlaw_differences_model m c) N =
      2 * c / ((N : ℝ) * ((N : ℝ) + 1) * ((N : ℝ) + 2))

/-- Paper label: `prop:xi-endpoint-heat-probe-powerlaw-differences`. -/
theorem paper_xi_endpoint_heat_probe_powerlaw_differences :
    xi_endpoint_heat_probe_powerlaw_differences_statement := by
  intro m c N hN
  have hNm1 : N - 1 + 1 = N := Nat.sub_add_cancel (Nat.succ_le_of_lt hN)
  have hNm1_cast_sum : ((N - 1 + 1 : ℕ) : ℝ) = (N : ℝ) := by
    exact_mod_cast hNm1
  have hNm1_cast : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by
    simpa [Nat.cast_add] using hNm1_cast_sum
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN
  have hN1 : (N : ℝ) + 1 ≠ 0 := by positivity
  have hN2 : (N : ℝ) + 2 ≠ 0 := by positivity
  constructor
  · simp [xi_endpoint_heat_probe_powerlaw_differences_firstDiff,
      xi_endpoint_heat_probe_powerlaw_differences_model]
    field_simp [hN1, hN2]
    ring
  · simp [xi_endpoint_heat_probe_powerlaw_differences_secondDiff,
      xi_endpoint_heat_probe_powerlaw_differences_model, hNm1_cast]
    field_simp [hN0, hN1, hN2]
    ring_nf

end Omega.Zeta
