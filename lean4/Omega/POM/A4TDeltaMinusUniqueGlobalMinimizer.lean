import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `thm:pom-a4t-delta-minus-unique-global-minimizer`. Once the elimination witness
and uniqueness certificate produce the unique positive critical point, the packaged minimizer
implication upgrades it to strict global minimality. -/
theorem paper_pom_a4t_delta_minus_unique_global_minimizer
    (has_polynomial_witness unique_positive_root strict_global_minimizer : Prop)
    (h_witness : has_polynomial_witness)
    (h_root : has_polynomial_witness → unique_positive_root)
    (h_min : unique_positive_root → strict_global_minimizer) :
    unique_positive_root ∧ strict_global_minimizer := by
  have h_unique : unique_positive_root := h_root h_witness
  exact ⟨h_unique, h_min h_unique⟩

end Omega.POM
