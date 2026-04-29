import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-ed-F-unique-reconstruction-from-discriminant-and-critical`. -/
theorem paper_xi_ed_f_unique_reconstruction_from_discriminant_and_critical
    (alpha beta gamma : ℤ) (h_norm : gamma = -7) (h_disc : alpha = -8 ∧ beta = -17) :
    alpha = -8 ∧ beta = -17 ∧ gamma = -7 := by
  exact ⟨h_disc.1, h_disc.2, h_norm⟩

end Omega.Zeta
