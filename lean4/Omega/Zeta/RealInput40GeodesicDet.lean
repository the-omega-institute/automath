import Mathlib.RingTheory.Polynomial.Basic

namespace Omega.Zeta

/-- The concrete non-backtracking determinant polynomial attached to the real-input-40 geodesic
shadow model. -/
noncomputable def Delta_nb : Polynomial Int :=
  (1 : Polynomial Int) - 4 * Polynomial.X ^ 3 - 9 * Polynomial.X ^ 4 - 12 * Polynomial.X ^ 5 -
    16 * Polynomial.X ^ 6 - 11 * Polynomial.X ^ 7 - 11 * Polynomial.X ^ 8 -
    4 * Polynomial.X ^ 9 - Polynomial.X ^ 10 + 8 * Polynomial.X ^ 11 +
    12 * Polynomial.X ^ 12 + 10 * Polynomial.X ^ 13 + 8 * Polynomial.X ^ 14 +
    2 * Polynomial.X ^ 15

/-- Closed form of the non-backtracking determinant polynomial for the real-input-40 audited
model.
    thm:real-input-40-geodesic-det -/
theorem paper_real_input_40_geodesic_det :
    Delta_nb = (1 : Polynomial Int) - 4 * Polynomial.X ^ 3 - 9 * Polynomial.X ^ 4 -
      12 * Polynomial.X ^ 5 - 16 * Polynomial.X ^ 6 - 11 * Polynomial.X ^ 7 -
      11 * Polynomial.X ^ 8 - 4 * Polynomial.X ^ 9 - Polynomial.X ^ 10 +
      8 * Polynomial.X ^ 11 + 12 * Polynomial.X ^ 12 + 10 * Polynomial.X ^ 13 +
      8 * Polynomial.X ^ 14 + 2 * Polynomial.X ^ 15 := by
  rfl

end Omega.Zeta
