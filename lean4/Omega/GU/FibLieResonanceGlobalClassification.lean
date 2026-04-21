import Mathlib.Tactic
import Omega.GU.FibPrimePisano

namespace Omega.GU

/-- Concrete paper-facing package for the global Fibonacci-Lie resonance classification:
the two `A`-type resonances, the audited orthogonal/symplectic resonances, and the Fibonacci
interval exclusions for the exceptional dimensions. -/
def FibLieResonanceGlobalClassification : Prop :=
  (2 ^ 2 - 1 = Nat.fib 4) ∧
    (3 ^ 2 - 1 = Nat.fib 6) ∧
    (3 * 2 / 2 = Nat.fib 4) ∧
    (7 * 6 / 2 = Nat.fib 8) ∧
    (11 * 10 / 2 = Nat.fib 10) ∧
    (1 * (2 * 1 + 1) = Nat.fib 4) ∧
    (3 * (2 * 3 + 1) = Nat.fib 8) ∧
    (5 * (2 * 5 + 1) = Nat.fib 10) ∧
    (Nat.fib 7 < 14 ∧ 14 < Nat.fib 8) ∧
    (Nat.fib 9 < 52 ∧ 52 < Nat.fib 10) ∧
    (Nat.fib 10 < 78 ∧ 78 < Nat.fib 11) ∧
    (Nat.fib 11 < 133 ∧ 133 < Nat.fib 12) ∧
    (Nat.fib 13 < 248 ∧ 248 < Nat.fib 14)

/-- Paper label: `thm:fib-lie-resonance-global-classification`. -/
theorem paper_fib_lie_resonance_global_classification : FibLieResonanceGlobalClassification := by
  rcases paper_fib_lie_resonance_orthogonal_symplectic with
    ⟨hso7, hso11, hsp6, hsp10, _, _, _⟩
  refine ⟨?_, ?_, ?_, hso7, hso11, ?_, hsp6, hsp10, ?_, ?_, ?_, ?_, ?_⟩
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide

end Omega.GU
