import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

/-- Concrete closed-orbit count package for the real-input-40 arity-charge collision audit. -/
structure RealInput40ArityChargeCycle where
  Ne : ℤ
  N2 : ℤ
  real_input_40_arity_charge_collision_le_output_charge_nonnegative : 0 ≤ Ne - N2

/-- The audited closed-orbit arity charge is the difference between the output count and the
collision count. -/
def real_input_40_arity_charge_collision_le_output_charge
    (γ : RealInput40ArityChargeCycle) : ℤ :=
  γ.Ne - γ.N2

/-- The cycle package already records the nonnegativity of the closed-orbit arity charge. -/
lemma real_input_40_arity_charge_collision_le_output_closed_orbit_arity_charge_nonnegative
    (γ : RealInput40ArityChargeCycle) :
    0 ≤ real_input_40_arity_charge_collision_le_output_charge γ := by
  simpa [real_input_40_arity_charge_collision_le_output_charge] using
    γ.real_input_40_arity_charge_collision_le_output_charge_nonnegative

/-- Paper label: `cor:real-input-40-arity-charge-collision-le-output`. Writing the closed-orbit
charge as `χ(γ) = Nₑ - N₂`, its nonnegativity forces the collision count to be at most the output
count. -/
theorem paper_real_input_40_arity_charge_collision_le_output
    (γ : RealInput40ArityChargeCycle) : γ.N2 <= γ.Ne := by
  have hcharge :
      0 ≤ real_input_40_arity_charge_collision_le_output_charge γ :=
    real_input_40_arity_charge_collision_le_output_closed_orbit_arity_charge_nonnegative γ
  exact sub_nonneg.mp (by
    simpa [real_input_40_arity_charge_collision_le_output_charge] using hcharge)

end Omega.SyncKernelRealInput
