import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

/-- Paper label: `prop:primitive-orbit-surgery`. -/
theorem paper_primitive_orbit_surgery
    (euler_factor_count primitive_split abel_correction : Prop)
    (h_euler_factor_count : euler_factor_count)
    (h_primitive_split : primitive_split)
    (h_abel_correction : abel_correction) :
    euler_factor_count ∧ primitive_split ∧ abel_correction := by
  exact ⟨h_euler_factor_count, h_primitive_split, h_abel_correction⟩

end Omega.SyncKernelRealInput
