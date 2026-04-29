import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic
import Omega.Zeta.XiTerminalZmExteriorSquareCurveGenus2
import Omega.Zeta.XiTerminalZmLeyangMonodromyS4

namespace Omega.Zeta

open Polynomial

noncomputable section

/-- The cubic branch polynomial `P_LY(y)` used in the exterior-square bookkeeping model. -/
def xi_terminal_zm_exterior_square_finite_ramification_index_ideal_p_ly : Polynomial ℤ :=
  X ^ 3 - X - 1

/-- The finite branch-locus polynomial `y (y - 1) P_LY(y)`. -/
def xi_terminal_zm_exterior_square_finite_ramification_index_ideal_branch_polynomial :
    Polynomial ℤ :=
  X * (X - 1) * xi_terminal_zm_exterior_square_finite_ramification_index_ideal_p_ly

/-- The finite discriminant ideal `(y (y - 1) P_LY(y))²`, recorded by its principal generator. -/
def xi_terminal_zm_exterior_square_finite_ramification_index_ideal_finite_discriminant :
    Polynomial ℤ :=
  xi_terminal_zm_exterior_square_finite_ramification_index_ideal_branch_polynomial ^ 2

/-- The finite index ideal `[B : A]_{fin}` recorded by its principal generator. -/
def xi_terminal_zm_exterior_square_finite_ramification_index_ideal_index_polynomial :
    Polynomial ℤ :=
  X ^ 3 * (X + 1) ^ 3 * (X ^ 2 + X - 1)

/-- The finite discriminant of the monogenic order `A[μ]`. -/
def xi_terminal_zm_exterior_square_finite_ramification_index_ideal_order_discriminant :
    Polynomial ℤ :=
  xi_terminal_zm_exterior_square_finite_ramification_index_ideal_finite_discriminant *
    xi_terminal_zm_exterior_square_finite_ramification_index_ideal_index_polynomial ^ 2

/-- Paper label: `thm:xi-terminal-zm-exterior-square-finite-ramification-index-ideal`.
The existing `S₄` monodromy package supplies the Galois group, the exterior-square genus-two audit
supplies the five finite branch values of contribution `2`, and the finite discriminant / index
generators are the explicit principal polynomials displayed in the paper. -/
theorem paper_xi_terminal_zm_exterior_square_finite_ramification_index_ideal :
    xiLeyangGeometricMonodromyGroup = ⊤ ∧
      xiLeyangFunctionFieldGaloisGroup = ⊤ ∧
      xi_terminal_zm_exterior_square_curve_genus2_finite_branch_point_count = 5 ∧
      xi_terminal_zm_exterior_square_curve_genus2_finite_branch_contribution = 2 ∧
      xi_terminal_zm_exterior_square_finite_ramification_index_ideal_finite_discriminant =
        (X * (X - 1) * xi_terminal_zm_exterior_square_finite_ramification_index_ideal_p_ly) ^ 2 ∧
      xi_terminal_zm_exterior_square_finite_ramification_index_ideal_index_polynomial =
        X ^ 3 * (X + 1) ^ 3 * (X ^ 2 + X - 1) ∧
      xi_terminal_zm_exterior_square_finite_ramification_index_ideal_order_discriminant =
        xi_terminal_zm_exterior_square_finite_ramification_index_ideal_finite_discriminant *
          xi_terminal_zm_exterior_square_finite_ramification_index_ideal_index_polynomial ^ 2 ∧
      ∃ Q₁ Q₂ : Polynomial ℤ,
        xi_terminal_zm_exterior_square_finite_ramification_index_ideal_index_polynomial =
          (X + 1) * Q₁ ∧
          xi_terminal_zm_exterior_square_finite_ramification_index_ideal_index_polynomial =
            (X ^ 2 + X - 1) * Q₂ := by
  rcases paper_xi_terminal_zm_leyang_monodromy_s4 with ⟨hGeo, hGal⟩
  refine ⟨hGeo, hGal, rfl, rfl, rfl, rfl, rfl, ?_⟩
  refine ⟨X ^ 3 * (X + 1) ^ 2 * (X ^ 2 + X - 1), X ^ 3 * (X + 1) ^ 3, ?_, ?_⟩
  · unfold xi_terminal_zm_exterior_square_finite_ramification_index_ideal_index_polynomial
    ring
  · unfold xi_terminal_zm_exterior_square_finite_ramification_index_ideal_index_polynomial
    ring

end

end Omega.Zeta
