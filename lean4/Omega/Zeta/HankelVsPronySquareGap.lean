import Mathlib.Tactic
import Omega.Zeta.HankelVandermonde2
import Omega.Zeta.HankelVandermonde3
import Omega.Zeta.HankelVandermonde4

namespace Omega.Zeta

/-- Paper-facing Vandermonde-square package for the `κ = 2, 3, 4` Hankel blocks. -/
theorem paper_xi_hankel_vs_prony_square_gap :
    (∀ ω1 ω2 a1 a2 : ℤ, hankel2 ω1 ω2 a1 a2 = ω1 * ω2 * (a2 - a1)^2) ∧
      (∀ ω1 ω2 ω3 a1 a2 a3 : ℤ, (hankel3 ω1 ω2 ω3 a1 a2 a3).det =
        ω1 * ω2 * ω3 * (a2 - a1)^2 * (a3 - a1)^2 * (a3 - a2)^2) ∧
      (∀ ω1 ω2 ω3 ω4 a1 a2 a3 a4 : ℤ, (hankel4 ω1 ω2 ω3 ω4 a1 a2 a3 a4).det =
        ω1 * ω2 * ω3 * ω4 * (a2 - a1)^2 * (a3 - a1)^2 * (a4 - a1)^2 *
          (a3 - a2)^2 * (a4 - a2)^2 * (a4 - a3)^2) := by
  exact ⟨hankel2_vandermonde_square, hankel3_vandermonde_square, hankel4_vandermonde_square⟩

end Omega.Zeta
