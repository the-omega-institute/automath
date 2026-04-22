import Mathlib.LinearAlgebra.Matrix.Notation
import Omega.Folding.StableSyntax

open Matrix

namespace Omega

/-- Terminal-bit count vector for stable syntax words, ordered as `(last = 1, last = 0)`. -/
noncomputable def stableSyntaxTerminalVector (m : ℕ) : Fin 2 → ℕ :=
  ![Fintype.card {x : X m // X.EndsInOne x}, Fintype.card {x : X m // X.EndsInZero x}]

/-- The terminal-bit transfer matrix in the basis `(last = 1, last = 0)`. -/
def stableSyntaxTerminalMatrix : Matrix (Fin 2) (Fin 2) ℕ :=
  !![0, 1; 1, 1]

/-- The terminal-state count vector for stable syntax words evolves by the Fibonacci transfer
matrix.
    prop:folding-stable-syntax-terminal-recursion -/
theorem paper_folding_stable_syntax_terminal_recursion (m : ℕ) :
    stableSyntaxTerminalVector (m + 1) =
      stableSyntaxTerminalMatrix.mulVec (stableSyntaxTerminalVector m) := by
  ext i
  fin_cases i
  · simp [stableSyntaxTerminalVector, stableSyntaxTerminalMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, X.card_endsInOne_succ]
  · change Fintype.card {x : X (m + 1) // X.EndsInZero x} = _
    rw [X.card_endsInZero_succ]
    simp [stableSyntaxTerminalVector, stableSyntaxTerminalMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, X.card_eq_endsInZero_add_endsInOne, Nat.add_comm]

end Omega
