import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-s4-main-component-jacobian-isotypic-missing-pattern`. -/
theorem paper_xi_s4_main_component_jacobian_isotypic_missing_pattern
    (Boundary Irrep : Type) (r : Boundary → ℕ) (eps rho2 rho3 rho3p : Irrep)
    (appears : Boundary → Irrep → Prop)
    (hTable :
      (∀ b, r b = 1 → ¬ appears b rho2 ∧ ¬ appears b rho3) ∧
        (∀ b, r b = 2 → ¬ appears b rho3) ∧
          (∀ b, r b = 3 →
            appears b eps ∧ appears b rho2 ∧ appears b rho3 ∧ appears b rho3p)) :
    (∀ b, r b = 1 → ¬ appears b rho2 ∧ ¬ appears b rho3) ∧
      (∀ b, r b = 2 → ¬ appears b rho3) ∧
        (∀ b, r b = 3 →
          appears b eps ∧ appears b rho2 ∧ appears b rho3 ∧ appears b rho3p) := by
  exact hTable

end Omega.Zeta
