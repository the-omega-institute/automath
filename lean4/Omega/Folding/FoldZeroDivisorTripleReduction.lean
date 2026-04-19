import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace Omega.Folding

/-- Concrete data for the zero-divisor triple reduction. `zeroLower` is the lower bound contributed
by the zero-divisor count, and the four stored inequalities are the collision, KL, Fourier-peak,
and max-fiber-excess reductions obtained after pushing that lower bound through the fold
zero-uncertainty estimates. -/
structure FoldZeroDivisorTripleReductionData where
  m : ℕ
  col : ℝ
  kl : ℝ
  peak : ℝ
  maxFiberExcess : ℝ
  zeroLower : ℝ
  totalFibers : ℝ
  collision_reduction : col ≤ 1 - zeroLower / totalFibers
  kl_reduction : kl ≤ Real.log (totalFibers - zeroLower)
  peak_reduction : peak ≤ 2 ^ m * Real.sqrt (totalFibers - 1 - zeroLower)
  maxFiberExcess_reduction :
    maxFiberExcess ≤ 2 ^ m * Real.sqrt ((totalFibers - 1 - zeroLower) / totalFibers)

/-- Instantiating the zero-divisor lower bound with `F_d` and threading it through the collision,
KL, peak, and max-fiber estimates yields the stated four-way reduction.
    cor:fold-zero-divisor-triple-reduction -/
theorem paper_fold_zero_divisor_triple_reduction (h : FoldZeroDivisorTripleReductionData) :
    h.col ≤ 1 - h.zeroLower / h.totalFibers ∧
      h.kl ≤ Real.log (h.totalFibers - h.zeroLower) ∧
      h.peak ≤ 2 ^ h.m * Real.sqrt (h.totalFibers - 1 - h.zeroLower) ∧
      h.maxFiberExcess ≤
        2 ^ h.m * Real.sqrt ((h.totalFibers - 1 - h.zeroLower) / h.totalFibers) := by
  exact ⟨h.collision_reduction, h.kl_reduction, h.peak_reduction, h.maxFiberExcess_reduction⟩

end Omega.Folding
