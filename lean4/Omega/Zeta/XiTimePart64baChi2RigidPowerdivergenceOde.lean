import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- The golden parameter recovered from the chi-square limit constant. -/
def xi_time_part64ba_chi2_rigid_powerdivergence_ode_phi (χ : ℝ) : ℝ :=
  (5 * χ + 3) / 2

/-- The first exponential rate in the recovered power-divergence family. -/
def xi_time_part64ba_chi2_rigid_powerdivergence_ode_c (χ : ℝ) : ℝ :=
  Real.log (((5 * χ + 3) ^ 2) / (4 * Real.sqrt 5))

/-- The second exponential rate in the recovered power-divergence family. -/
def xi_time_part64ba_chi2_rigid_powerdivergence_ode_d (χ : ℝ) : ℝ :=
  Real.log ((5 * χ + 3) / (2 * Real.sqrt 5))

/-- The recovered two-exponential value `E(α) = D_{f_α,∞} + 1`. -/
def xi_time_part64ba_chi2_rigid_powerdivergence_ode_E (χ α : ℝ) : ℝ :=
  (xi_time_part64ba_chi2_rigid_powerdivergence_ode_phi χ)⁻¹ *
      Real.exp (xi_time_part64ba_chi2_rigid_powerdivergence_ode_c χ * α) +
    (xi_time_part64ba_chi2_rigid_powerdivergence_ode_phi χ)⁻¹ ^ (2 : ℕ) *
      Real.exp (xi_time_part64ba_chi2_rigid_powerdivergence_ode_d χ * α)

/-- The corresponding recovered power-divergence constant. -/
def xi_time_part64ba_chi2_rigid_powerdivergence_ode_powerD (χ α : ℝ) : ℝ :=
  xi_time_part64ba_chi2_rigid_powerdivergence_ode_E χ α - 1

/-- The formal first derivative of the two-exponential recovered value. -/
def xi_time_part64ba_chi2_rigid_powerdivergence_ode_Eprime (χ α : ℝ) : ℝ :=
  (xi_time_part64ba_chi2_rigid_powerdivergence_ode_phi χ)⁻¹ *
      xi_time_part64ba_chi2_rigid_powerdivergence_ode_c χ *
        Real.exp (xi_time_part64ba_chi2_rigid_powerdivergence_ode_c χ * α) +
    (xi_time_part64ba_chi2_rigid_powerdivergence_ode_phi χ)⁻¹ ^ (2 : ℕ) *
      xi_time_part64ba_chi2_rigid_powerdivergence_ode_d χ *
        Real.exp (xi_time_part64ba_chi2_rigid_powerdivergence_ode_d χ * α)

/-- The formal second derivative of the two-exponential recovered value. -/
def xi_time_part64ba_chi2_rigid_powerdivergence_ode_Esecond (χ α : ℝ) : ℝ :=
  (xi_time_part64ba_chi2_rigid_powerdivergence_ode_phi χ)⁻¹ *
      (xi_time_part64ba_chi2_rigid_powerdivergence_ode_c χ) ^ (2 : ℕ) *
        Real.exp (xi_time_part64ba_chi2_rigid_powerdivergence_ode_c χ * α) +
    (xi_time_part64ba_chi2_rigid_powerdivergence_ode_phi χ)⁻¹ ^ (2 : ℕ) *
      (xi_time_part64ba_chi2_rigid_powerdivergence_ode_d χ) ^ (2 : ℕ) *
        Real.exp (xi_time_part64ba_chi2_rigid_powerdivergence_ode_d χ * α)

/-- Concrete statement for chi2 recovery and the second-order annihilator. -/
def xi_time_part64ba_chi2_rigid_powerdivergence_ode_statement : Prop :=
  ∀ χ α : ℝ,
    xi_time_part64ba_chi2_rigid_powerdivergence_ode_phi χ = (5 * χ + 3) / 2 ∧
      xi_time_part64ba_chi2_rigid_powerdivergence_ode_powerD χ α + 1 =
        xi_time_part64ba_chi2_rigid_powerdivergence_ode_E χ α ∧
      xi_time_part64ba_chi2_rigid_powerdivergence_ode_Esecond χ α -
          (xi_time_part64ba_chi2_rigid_powerdivergence_ode_c χ +
              xi_time_part64ba_chi2_rigid_powerdivergence_ode_d χ) *
            xi_time_part64ba_chi2_rigid_powerdivergence_ode_Eprime χ α +
          xi_time_part64ba_chi2_rigid_powerdivergence_ode_c χ *
            xi_time_part64ba_chi2_rigid_powerdivergence_ode_d χ *
              xi_time_part64ba_chi2_rigid_powerdivergence_ode_E χ α = 0

/-- Paper label: `thm:xi-time-part64ba-chi2-rigid-powerdivergence-ode`. -/
theorem paper_xi_time_part64ba_chi2_rigid_powerdivergence_ode :
    xi_time_part64ba_chi2_rigid_powerdivergence_ode_statement := by
  intro χ α
  constructor
  · rfl
  constructor
  · simp [xi_time_part64ba_chi2_rigid_powerdivergence_ode_powerD]
  · simp [xi_time_part64ba_chi2_rigid_powerdivergence_ode_Esecond,
      xi_time_part64ba_chi2_rigid_powerdivergence_ode_Eprime,
      xi_time_part64ba_chi2_rigid_powerdivergence_ode_E]
    ring

end

end Omega.Zeta
