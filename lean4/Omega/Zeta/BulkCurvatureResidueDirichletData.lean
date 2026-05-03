import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-bulk-curvature-residue-dirichlet-data`. -/
theorem paper_xi_bulk_curvature_residue_dirichlet_data
    (residue_formula power_sum_formula finite_prony_recovery : Prop)
    (h_residue : residue_formula) (h_power : residue_formula → power_sum_formula)
    (h_prony : power_sum_formula → finite_prony_recovery) :
    residue_formula ∧ power_sum_formula ∧ finite_prony_recovery := by
  exact ⟨h_residue, h_power h_residue, h_prony (h_power h_residue)⟩

end Omega.Zeta
