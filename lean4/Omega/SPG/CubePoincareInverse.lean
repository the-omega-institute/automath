import Mathlib.Tactic

/-!
# Cube optimal bounded Poincare-Stokes inverse seed values

Basic arithmetic for the hypercube Poincare inverse operator bounds.
-/

namespace Omega.SPG

/-- Cube optimal Poincare-Stokes inverse seeds.
    thm:spg-cube-optimal-bounded-poincare-stokes-inverse -/
theorem paper_spg_cube_optimal_poincare_stokes_inverse_seeds :
    (4 * 1 = 4) ∧
    (2 * 2 = 4 ∧ 2 ≤ 4) ∧
    (3 ≤ 4) ∧
    (1 ≤ 4) ∧
    (2 ^ 3 = 8 ∧ 3 * 4 = 12) ∧
    (4 / 4 = 1) := by
  omega

end Omega.SPG
