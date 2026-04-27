import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:selfdual-implies-kappa0`. -/
theorem paper_selfdual_implies_kappa0 {Obj : Type*} (selfDual : Obj → Prop)
    (wind degree blaschkeDefect kappa : Obj → Nat)
    (hWind : ∀ F, selfDual F → wind F = 0)
    (hIdentity : ∀ F, wind F = degree F ∧ degree F = blaschkeDefect F ∧
      blaschkeDefect F = kappa F)
    {F : Obj} (hF : selfDual F) :
    degree F = 0 ∧ blaschkeDefect F = 0 ∧ kappa F = 0 := by
  rcases hIdentity F with ⟨h_wind_degree, h_degree_defect, h_defect_kappa⟩
  have h_degree_zero : degree F = 0 := by
    rw [← h_wind_degree]
    exact hWind F hF
  have h_defect_zero : blaschkeDefect F = 0 := by
    rw [← h_degree_defect]
    exact h_degree_zero
  have h_kappa_zero : kappa F = 0 := by
    rw [← h_defect_kappa]
    exact h_defect_zero
  exact ⟨h_degree_zero, h_defect_zero, h_kappa_zero⟩

end Omega.Zeta
