import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Omega.Folding.Entropy

open scoped goldenRatio

namespace Omega.POM

/-- The parity-even endpoint branch used for the max atomic-weight package. -/
noncomputable def pMaxEvenBranch (k : ℕ) : ℝ :=
  Nat.fib (k + 2)

/-- The parity-odd endpoint branch used for the max atomic-weight package. -/
noncomputable def pMaxOddBranch (k : ℕ) : ℝ :=
  Nat.fib (k + 3)

/-- The two-term min-entropy proxy obtained by taking the logarithm of the doubled even branch. -/
noncomputable def minEntropyParitySecondOrder (k : ℕ) : ℝ :=
  Real.log (2 * pMaxEvenBranch k)

private lemma pMaxEvenBranch_pos (k : ℕ) : 0 < pMaxEvenBranch k := by
  dsimp [pMaxEvenBranch]
  exact_mod_cast Nat.fib_pos.mpr (by omega)

/-- Paper-facing parity split for the endpoint Binet formulas together with the logarithmic
two-term min-entropy expansion.
    prop:pom-max-atomic-weight-parity-second-order -/
theorem paper_pom_max_atomic_weight_parity_second_order :
    (∀ k : ℕ, pMaxEvenBranch k = (φ ^ (k + 2) - ψ ^ (k + 2)) / Real.sqrt 5) ∧
    (∀ k : ℕ, pMaxOddBranch k = (φ ^ (k + 3) - ψ ^ (k + 3)) / Real.sqrt 5) ∧
    (∀ k : ℕ, minEntropyParitySecondOrder k = Real.log (pMaxEvenBranch k) + Real.log 2) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k
    dsimp [pMaxEvenBranch]
    simpa using Omega.Entropy.binet_formula (k + 2)
  · intro k
    dsimp [pMaxOddBranch]
    simpa using Omega.Entropy.binet_formula (k + 3)
  · intro k
    dsimp [minEntropyParitySecondOrder]
    have hk0 : pMaxEvenBranch k ≠ 0 := ne_of_gt (pMaxEvenBranch_pos k)
    rw [show 2 * pMaxEvenBranch k = pMaxEvenBranch k * 2 by ring]
    rw [Real.log_mul hk0 (by norm_num : (2 : ℝ) ≠ 0)]

end Omega.POM
