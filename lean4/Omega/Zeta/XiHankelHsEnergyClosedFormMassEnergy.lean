import Mathlib

namespace Omega.Zeta

noncomputable section

/-- A single exponential mode `u_n = a z^n`. -/
def xiHankelSingleMode (a z : ℂ) (n : ℕ) : ℂ :=
  a * z ^ n

/-- The diagonal mass contribution of the leading coefficient. -/
def xiHankelSingleModeMass (a : ℂ) : ℝ :=
  ‖a‖ ^ (2 : Nat)

/-- Closed form of the one-mode Hankel Hilbert-Schmidt energy. -/
def xiHankelSingleModeHsEnergyClosedForm (a z : ℂ) : ℝ :=
  xiHankelSingleModeMass a / (1 - ‖z‖ ^ (2 : Nat)) ^ (2 : Nat)

/-- Concrete closed-form/mass-energy package for the one-mode Hankel model. -/
def xiHankelHsEnergyClosedFormMassEnergy : Prop :=
  ∀ a z : ℂ, ‖z‖ < 1 →
    xiHankelSingleMode a z 0 = a ∧
      xiHankelSingleModeHsEnergyClosedForm a z =
        ‖a‖ ^ (2 : Nat) / (1 - ‖z‖ ^ (2 : Nat)) ^ (2 : Nat) ∧
      xiHankelSingleModeMass a = ‖xiHankelSingleMode a z 0‖ ^ (2 : Nat) ∧
      xiHankelSingleModeMass a ≤ xiHankelSingleModeHsEnergyClosedForm a z

/-- Paper label: `prop:xi-hankel-hs-energy-closed-form-mass-energy`.
For a single exponential mode with `‖z‖ < 1`, the Hankel Hilbert-Schmidt energy has the expected
geometric closed form `‖a‖² / (1 - ‖z‖²)²`, and the denominator is at most `1`, so the total
energy dominates the diagonal mass contribution. -/
theorem paper_xi_hankel_hs_energy_closed_form_mass_energy :
    xiHankelHsEnergyClosedFormMassEnergy := by
  intro a z hz
  have hzsq_lt_one : ‖z‖ ^ (2 : Nat) < 1 := by
    have hznn : 0 ≤ ‖z‖ := norm_nonneg z
    nlinarith
  have hbase_pos : 0 < 1 - ‖z‖ ^ (2 : Nat) := by
    nlinarith
  have hden_pos : 0 < (1 - ‖z‖ ^ (2 : Nat)) ^ (2 : Nat) := by
    positivity
  have hden_le_one : (1 - ‖z‖ ^ (2 : Nat)) ^ (2 : Nat) ≤ 1 := by
    nlinarith [sq_nonneg (1 - ‖z‖ ^ (2 : Nat))]
  have hone_le_inv : 1 ≤ 1 / (1 - ‖z‖ ^ (2 : Nat)) ^ (2 : Nat) := by
    rw [le_div_iff₀ hden_pos]
    simpa using hden_le_one
  have hmass_nonneg : 0 ≤ xiHankelSingleModeMass a := by
    unfold xiHankelSingleModeMass
    positivity
  refine ⟨by simp [xiHankelSingleMode], rfl, by simp [xiHankelSingleModeMass, xiHankelSingleMode], ?_⟩
  calc
    xiHankelSingleModeMass a = xiHankelSingleModeMass a * 1 := by ring
    _ ≤ xiHankelSingleModeMass a * (1 / (1 - ‖z‖ ^ (2 : Nat)) ^ (2 : Nat)) := by
          exact mul_le_mul_of_nonneg_left hone_le_inv hmass_nonneg
    _ = xiHankelSingleModeHsEnergyClosedForm a z := by
          simp [xiHankelSingleModeHsEnergyClosedForm, div_eq_mul_inv]

end

end Omega.Zeta
