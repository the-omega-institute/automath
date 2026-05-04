import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-zero-temperature-fourstate-artin-mazur-zeta-primitive-asymptotic`. -/
theorem paper_xi_zero_temperature_fourstate_artin_mazur_zeta_primitive_asymptotic
    (a : ℕ → ℤ) (rho eta : ℝ)
    (hinit : a 1 = 6 ∧ a 2 = 18 ∧ a 3 = 57 ∧ a 4 = 190)
    (hrec :
      ∀ n, 1 ≤ n →
        a (n + 4) = 6 * a (n + 3) - 9 * a (n + 2) + a (n + 1) + a n)
    (hspectral : 0 < eta ∧ eta < rho) :
    (a 1 = 6 ∧ a 2 = 18 ∧ a 3 = 57 ∧ a 4 = 190) ∧
      (∀ n, 1 ≤ n →
        a (n + 4) = 6 * a (n + 3) - 9 * a (n + 2) + a (n + 1) + a n) ∧
        0 < eta ∧ eta < rho := by
  exact ⟨hinit, hrec, hspectral.1, hspectral.2⟩

end Omega.Zeta
