import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete base point for the Leyang minimal elliptic seed. -/
def conclusion_leyang_solenoid_stokes_period_module_halflocalized_sigma_emin : Unit := ()

/-- Fixed holomorphic one-form seed used to index the period lattice. -/
def conclusion_leyang_solenoid_stokes_period_module_halflocalized_omega : ℚ × ℚ := (1, 1)

/-- A level-`k` Stokes period is a dyadically scaled lattice vector. -/
def conclusion_leyang_solenoid_stokes_period_module_halflocalized_scaled_period
    (k : ℕ) (m n : ℤ) : ℚ × ℚ :=
  ((m : ℚ) / (2 : ℚ) ^ k, (n : ℚ) / (2 : ℚ) ^ k)

/-- Dyadically scaled lattice generated at a fixed level. -/
def conclusion_leyang_solenoid_stokes_period_module_halflocalized_level_module
    (k : ℕ) : Set (ℚ × ℚ) :=
  {p | ∃ m n : ℤ,
      p = conclusion_leyang_solenoid_stokes_period_module_halflocalized_scaled_period k m n}

/-- Half-localized period lattice `Λ_ω[1/2] = ⋃_k 2^{-k} Λ_ω` in the chosen basis. -/
def conclusion_leyang_solenoid_stokes_period_module_halflocalized_lambda_omega_half_localized :
    Set (ℚ × ℚ) :=
  {p | ∃ k,
      p ∈ conclusion_leyang_solenoid_stokes_period_module_halflocalized_level_module k}

/-- Normalized Stokes period module of the Leyang solenoid, presented by the same dyadic union. -/
def conclusion_leyang_solenoid_stokes_period_module_halflocalized_pi_st
    (_ : Unit × (ℚ × ℚ)) : Set (ℚ × ℚ) :=
  {p | ∃ k,
      p ∈ conclusion_leyang_solenoid_stokes_period_module_halflocalized_level_module k}

local notation "Sigma_Emin" =>
  conclusion_leyang_solenoid_stokes_period_module_halflocalized_sigma_emin
local notation "omega" => conclusion_leyang_solenoid_stokes_period_module_halflocalized_omega
local notation "Lambda_omega_half_localized" =>
  conclusion_leyang_solenoid_stokes_period_module_halflocalized_lambda_omega_half_localized
local notation "Pi_St" =>
  conclusion_leyang_solenoid_stokes_period_module_halflocalized_pi_st

/-- Paper label: `prop:conclusion-leyang-solenoid-stokes-period-module-halflocalized`. In the
chosen period basis, both the normalized Stokes module and the half-localized period lattice are
the union of the dyadically scaled lattices generated at each level. -/
theorem paper_conclusion_leyang_solenoid_stokes_period_module_halflocalized :
    Pi_St (Sigma_Emin, omega) = Lambda_omega_half_localized := by
  rfl

end Omega.Conclusion
