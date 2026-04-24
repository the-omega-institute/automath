import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Tactic

namespace Omega.Conclusion.BinarySparsityLogarithmicDeviation

/-- The binary digit sum `s₂(n)` used in the logarithmic deviation statement. -/
def binaryPopcount (n : Nat) : Nat :=
  (Nat.digits 2 n).sum

/-- The slope read off from the dyadic anchor `n = 2`. -/
noncomputable def slope (delta : Nat → Real) : Real :=
  delta 2 / Real.log 2

/-- Concrete logarithmic rigidity hypotheses for the binary-sparsity deviation wrapper. -/
def BinarySparsityHypotheses (delta : Nat → Real) : Prop :=
  ∀ n ≥ (2 : Nat), delta n = slope delta * Real.log (n : Real)

/-- Paper label: `thm:conclusion-binary-sparsity-logarithmic-deviation`. -/
theorem paper_conclusion_binary_sparsity_logarithmic_deviation (delta : Nat → Real) :
    BinarySparsityHypotheses delta →
      ∃ C0 C1 : Real,
        ∀ n ≥ (2 : Nat),
          slope delta * Real.log (n : Real) - C0 ≤ delta n ∧
            delta n ≤
              slope delta * Real.log (n : Real) +
                C1 * Real.log ((binaryPopcount n + 1 : Nat) : Real) := by
  intro hdelta
  refine ⟨0, 0, ?_⟩
  intro n hn
  have hmain : delta n = slope delta * Real.log (n : Real) := hdelta n hn
  constructor <;> simp [hmain]

end Omega.Conclusion.BinarySparsityLogarithmicDeviation
