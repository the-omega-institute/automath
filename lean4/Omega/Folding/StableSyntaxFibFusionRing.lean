import Mathlib.Data.Matrix.Action
import Omega.Folding.StableSyntaxTerminalRecursion

open Matrix

namespace Omega

/-- The stable-syntax terminal recursion is the Fibonacci fusion-matrix recursion, so iterating
from the base vector `![1, 1]` recovers every terminal count vector.
    thm:folding-stable-syntax-fib-fusion-ring -/
theorem paper_folding_stable_syntax_fib_fusion_ring (m : ℕ) :
    stableSyntaxTerminalVector (m + 1) = Matrix.mulVec (stableSyntaxTerminalMatrix ^ m) ![1, 1] := by
  induction m with
  | zero =>
      ext i
      fin_cases i <;>
        simp [stableSyntaxTerminalVector, stableSyntaxTerminalMatrix, Matrix.mulVec, dotProduct,
          Fin.sum_univ_two]
  | succ m ihm =>
      calc
        stableSyntaxTerminalVector (m + 2)
            = stableSyntaxTerminalMatrix.mulVec (stableSyntaxTerminalVector (m + 1)) := by
                simpa [Nat.add_assoc] using paper_folding_stable_syntax_terminal_recursion (m + 1)
        _ = stableSyntaxTerminalMatrix.mulVec ((stableSyntaxTerminalMatrix ^ m).mulVec ![1, 1]) := by
              rw [ihm]
        _ = ((stableSyntaxTerminalMatrix * stableSyntaxTerminalMatrix ^ m)).mulVec ![1, 1] := by
              rw [← Matrix.mulVec_mulVec]
        _ = Matrix.mulVec (stableSyntaxTerminalMatrix ^ (m + 1)) ![1, 1] := by
              rw [pow_succ']

end Omega
