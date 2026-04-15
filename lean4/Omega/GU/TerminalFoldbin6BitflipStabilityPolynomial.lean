import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
import Omega.GU.TerminalFoldbin6ThreeOffsetRigidity

namespace Omega.GU

open scoped BigOperators

/-- Stable ordered pairs in the window-6 Bernoulli bit-flip shell `K = k`. -/
def terminalFoldbin6StableShellPairs : Nat → Nat
  | 0 => 64
  | 1 => 0
  | 2 => 32
  | 3 => 32
  | 4 => 56
  | 5 => 24
  | 6 => 4
  | _ => 0

/-- The shellwise stability ratios `A_k = P(S | K = k)`. -/
def terminalFoldbin6StabilityCoeff (k : Nat) : ℚ :=
  (terminalFoldbin6StableShellPairs k : ℚ) / ((64 * Nat.choose 6 k : Nat) : ℚ)

/-- The Bernoulli-shell expansion of the exact window-6 bit-flip stability law. -/
def terminalFoldbin6BernoulliShellExpansion (p : ℚ) : ℚ :=
  (1 - p) ^ 6 + (1 / 2 : ℚ) * p ^ 2 * (1 - p) ^ 4 + (1 / 2 : ℚ) * p ^ 3 * (1 - p) ^ 3 +
    (7 / 8 : ℚ) * p ^ 4 * (1 - p) ^ 2 + (3 / 8 : ℚ) * p ^ 5 * (1 - p) + (1 / 16 : ℚ) * p ^ 6

/-- The expanded exact stability polynomial. -/
def terminalFoldbin6BitflipStability (p : ℚ) : ℚ :=
  1 - 6 * p + (31 / 2 : ℚ) * p ^ 2 - (43 / 2 : ℚ) * p ^ 3 + (139 / 8 : ℚ) * p ^ 4 -
    (63 / 8 : ℚ) * p ^ 5 + (25 / 16 : ℚ) * p ^ 6

/-- The complementary instability polynomial. -/
def terminalFoldbin6BitflipInstability (p : ℚ) : ℚ :=
  1 - terminalFoldbin6BitflipStability p

/-- Paper-facing exact Bernoulli bit-flip stability polynomial for `Foldbin₆`:
    shell counts, conditional stability coefficients, the vanishing one-bit term from edge
    separation, and the closed-form stability/instability polynomials.
    thm:terminal-foldbin6-bitflip-stability-polynomial -/
theorem paper_terminal_foldbin6_bitflip_stability_polynomial :
    cBinFiberHist 6 1 = 0 ∧
    terminalFoldbin6StableShellPairs 0 = 64 ∧
    terminalFoldbin6StableShellPairs 1 = 0 ∧
    terminalFoldbin6StableShellPairs 2 = 32 ∧
    terminalFoldbin6StableShellPairs 3 = 32 ∧
    terminalFoldbin6StableShellPairs 4 = 56 ∧
    terminalFoldbin6StableShellPairs 5 = 24 ∧
    terminalFoldbin6StableShellPairs 6 = 4 ∧
    terminalFoldbin6StabilityCoeff 0 = 1 ∧
    terminalFoldbin6StabilityCoeff 1 = 0 ∧
    terminalFoldbin6StabilityCoeff 2 = 1 / 30 ∧
    terminalFoldbin6StabilityCoeff 3 = 1 / 40 ∧
    terminalFoldbin6StabilityCoeff 4 = 7 / 120 ∧
    terminalFoldbin6StabilityCoeff 5 = 1 / 16 ∧
    terminalFoldbin6StabilityCoeff 6 = 1 / 16 ∧
    (∀ p : ℚ,
      terminalFoldbin6BernoulliShellExpansion p = terminalFoldbin6BitflipStability p ∧
      terminalFoldbin6BitflipInstability p =
        6 * p - (31 / 2 : ℚ) * p ^ 2 + (43 / 2 : ℚ) * p ^ 3 - (139 / 8 : ℚ) * p ^ 4 +
          (63 / 8 : ℚ) * p ^ 5 - (25 / 16 : ℚ) * p ^ 6) := by
  rcases paper_terminal_foldbin6_three_offset_rigidity with ⟨_, _, _, hOne, _⟩
  repeat' constructor
  · exact hOne
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · intro p
    constructor
    · simp [terminalFoldbin6BernoulliShellExpansion, terminalFoldbin6BitflipStability]
      ring_nf
    · simp [terminalFoldbin6BitflipInstability, terminalFoldbin6BitflipStability]
      ring_nf

end Omega.GU
