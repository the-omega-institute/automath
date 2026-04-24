import Mathlib.Data.Rat.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Surrogate area of the rational ellipse `E_A = A(D)` obtained from determinant scaling. -/
def xi_terminal_ellipse_area_euler_prime_law_area (A : Matrix (Fin 2) (Fin 2) ℚ) : ℝ :=
  Real.pi * |(A.det : ℝ)|

def xi_terminal_ellipse_area_euler_prime_law_statement : Prop :=
  ∀ A : Matrix (Fin 2) (Fin 2) ℚ, A.det ≠ 0 →
    xi_terminal_ellipse_area_euler_prime_law_area A = Real.pi * |(A.det : ℝ)| ∧
      (Int.natAbs A.det.num).factorization.prod (· ^ ·) = Int.natAbs A.det.num ∧
      A.det.den.factorization.prod (· ^ ·) = A.det.den

/-- Paper label: `thm:xi-terminal-ellipse-area-euler-prime-law`. The ellipse area scales by the
Jacobian factor `|det A|`, and for a nonzero rational determinant its numerator and denominator are
recovered multiplicatively from their prime factorizations. -/
theorem paper_xi_terminal_ellipse_area_euler_prime_law :
    xi_terminal_ellipse_area_euler_prime_law_statement := by
  intro A hdet
  refine ⟨rfl, ?_, ?_⟩
  · have hnum_ne_zero : A.det.num ≠ 0 := by
      intro hnum
      exact hdet (Rat.zero_of_num_zero hnum)
    exact Nat.factorization_prod_pow_eq_self (Int.natAbs_ne_zero.mpr hnum_ne_zero)
  · exact Nat.factorization_prod_pow_eq_self A.det.den_ne_zero

end
end Omega.Zeta
