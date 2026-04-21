import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Folding

noncomputable section

/-- Concrete data for the unified Lee--Yang digit-rigidity argument: five seeds, a cardinality
formula for each branch layer, and the resulting entropy/dimension parameters. -/
structure KilloLeyangUnifiedDigitRigidityData where
  scale : ℝ
  digitCount : ℕ
  seedCount : ℕ
  branchCount : ℕ → ℕ
  topologicalEntropy : ℝ
  hausdorffDimension : ℝ
  minkowskiDimension : ℝ
  seedCount_eq : seedCount = 5
  branchCount_from_digits : ∀ n, branchCount n = seedCount * digitCount ^ n
  branchCount_from_hypercube : ∀ n, branchCount n = 5 * 4 ^ n
  topologicalEntropy_eq : topologicalEntropy = Real.log digitCount
  hausdorffDimension_eq : hausdorffDimension = 2 / scale
  minkowskiDimension_eq : minkowskiDimension = 2 / scale

/-- Paper label: `thm:killo-leyang-unified-digit-rigidity`. -/
theorem paper_killo_leyang_unified_digit_rigidity (D : KilloLeyangUnifiedDigitRigidityData) :
    D.digitCount = 4 ∧ D.topologicalEntropy = Real.log 4 ∧
      D.hausdorffDimension = 2 / D.scale ∧ D.minkowskiDimension = 2 / D.scale := by
  have hcount : D.seedCount * D.digitCount = 5 * 4 := by
    calc
      D.seedCount * D.digitCount = D.branchCount 1 := by
        simpa using (D.branchCount_from_digits 1).symm
      _ = 5 * 4 := by
        simpa using D.branchCount_from_hypercube 1
  have hdigit : D.digitCount = 4 := by
    rw [D.seedCount_eq] at hcount
    omega
  refine ⟨hdigit, ?_, D.hausdorffDimension_eq, D.minkowskiDimension_eq⟩
  rw [D.topologicalEntropy_eq, hdigit]
  norm_num

end

end Omega.Folding
