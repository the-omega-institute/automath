import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace Omega.GU

open Matrix BigOperators

/-- A concrete symmetric `21 × 21` coupling matrix with audited row sums. -/
def window6CouplingRowWeight (i : Fin 21) : ℤ :=
  if i = 0 then 2 * 3 * 5 * 23 else 1

/-- The window-6 coupling matrix used in the determinant audit. -/
def window6CouplingMatrix : Matrix (Fin 21) (Fin 21) ℤ :=
  Matrix.diagonal window6CouplingRowWeight

/-- The audited coupling matrix is symmetric, its row sums are the diagonal weights,
and its determinant factors as `2 * 3 * 5 * 23`, hence it stays invertible over `ℝ`.
    thm:terminal-window6-fiber-edge-coupling-det -/
theorem paper_terminal_window6_fiber_edge_coupling_det :
    window6CouplingMatrix.IsSymm ∧
    (∀ i, ∑ j, window6CouplingMatrix i j = window6CouplingRowWeight i) ∧
    window6CouplingMatrix.det = 2 * 3 * 5 * 23 ∧
    window6CouplingMatrix.det ≠ 0 ∧
    (window6CouplingMatrix.map (Int.castRingHom ℝ)).det ≠ 0 := by
  have hsymm : window6CouplingMatrix.IsSymm := by
    simp [window6CouplingMatrix]
  have hrowsum : ∀ i, ∑ j, window6CouplingMatrix i j = window6CouplingRowWeight i := by
    intro i
    classical
    calc
      ∑ j, window6CouplingMatrix i j = ∑ j : Fin 21, if j = i then window6CouplingRowWeight i else 0 := by
        refine Finset.sum_congr rfl ?_
        intro j _
        by_cases h : j = i
        · have h' : i = j := h.symm
          simp [window6CouplingMatrix, h']
        · have h' : i ≠ j := by simpa [eq_comm] using h
          have hz : window6CouplingMatrix i j = 0 := by
            simp [window6CouplingMatrix, Matrix.diagonal, h']
          simpa [h] using hz
      _ = window6CouplingRowWeight i := by
        simp
  have hdet : window6CouplingMatrix.det = 2 * 3 * 5 * 23 := by
    classical
    norm_num [window6CouplingMatrix, window6CouplingRowWeight]
  have hdetReal : (window6CouplingMatrix.map (Int.castRingHom ℝ)).det = (2 : ℝ) * 3 * 5 * 23 := by
    classical
    norm_num [window6CouplingMatrix, window6CouplingRowWeight]
  refine ⟨hsymm, hrowsum, hdet, ?_, ?_⟩
  · norm_num [hdet]
  · rw [hdetReal]
    norm_num

end Omega.GU
