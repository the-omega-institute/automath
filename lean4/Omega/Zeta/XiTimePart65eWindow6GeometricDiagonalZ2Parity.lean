import Mathlib.Tactic
import Omega.Conclusion.Window6BoundaryC3DiagonalIrreducibleSplitting

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part65e-window6-geometric-diagonal-z2-parity`. -/
theorem paper_xi_time_part65e_window6_geometric_diagonal_z2_parity :
    let P6 := Fin 3 → ZMod 2
    (∀ x : P6, (∃ a : ZMod 2, x = a • Omega.Conclusion.boundaryDiagonal) ↔
        x = 0 ∨ x = Omega.Conclusion.boundaryDiagonal) ∧
      Fintype.card {x : P6 // ∃ a : ZMod 2, x = a • Omega.Conclusion.boundaryDiagonal} = 2 ∧
      Fintype.card P6 = 8 := by
  native_decide

end Omega.Zeta
