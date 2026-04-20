import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.EA.CentralIdempotentsRecovery

namespace Omega.EA

/-- The coarse-grained KL loss for the four `m = 6` fiber classes used in the saturation model:
two maximal fibers of size `4`, one nonmaximal fiber of size `2`, and one singleton fiber. -/
noncomputable def foldSaturationFiberLoss (a b c d : ℝ) : ℝ :=
  a * Real.log 4 + b * Real.log 4 + c * Real.log 2 + d * Real.log 1

/-- Saturation forces the coarse support onto the maximal fibers, equivalently the weights of the
nonmaximal fibers vanish. -/
def foldSaturationOnMaxFibers (c d : ℝ) : Prop :=
  c = 0 ∧ d = 0

/-- Paper label: `thm:fold-max-data-processing-saturation-chi`. -/
theorem paper_fold_max_data_processing_saturation_chi
    {a b c d : ℝ}
    (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hsum : a + b + c + d = 1)
    (hloss : foldSaturationFiberLoss a b c d = Real.log 4) :
    foldSaturationOnMaxFibers c d ∧
      ((21 : Nat) = Nat.fib 8 ∧ (4 : Nat) > 0 ∧ (9 : Nat) > 0 ∧
        4 * 9 = 36 ∧ 36 < 64 ∧ 2 ^ 6 = 64) := by
  have hlog2_pos : 0 < Real.log (2 : ℝ) := by
    exact Real.log_pos (by norm_num)
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log (2 : ℝ) := by
    rw [show (4 : ℝ) = (2 : ℝ) * 2 by norm_num,
      Real.log_mul (show (2 : ℝ) ≠ 0 by norm_num) (show (2 : ℝ) ≠ 0 by norm_num)]
    ring
  have hloss' :
      a * (2 * Real.log 2) + b * (2 * Real.log 2) + c * Real.log 2 = 2 * Real.log 2 := by
    rw [foldSaturationFiberLoss, Real.log_one, mul_zero, add_zero, hlog4] at hloss
    simpa [hlog4] using hloss
  have htotal :
      a * (2 * Real.log 2) + b * (2 * Real.log 2) + c * (2 * Real.log 2) +
        d * (2 * Real.log 2) = 2 * Real.log 2 := by
    have hsum_mul := congrArg (fun x : ℝ => x * (2 * Real.log 2)) hsum
    ring_nf at hsum_mul ⊢
    simpa [mul_assoc, mul_left_comm, mul_comm] using hsum_mul
  have hvanish :
      c * Real.log (2 : ℝ) + d * (2 * Real.log (2 : ℝ)) = 0 := by
    linarith
  have hcTerm_nonneg : 0 ≤ c * Real.log (2 : ℝ) := mul_nonneg hc hlog2_pos.le
  have htwoLog2_pos : 0 < 2 * Real.log (2 : ℝ) := by positivity
  have hdTerm_nonneg : 0 ≤ d * (2 * Real.log (2 : ℝ)) := mul_nonneg hd htwoLog2_pos.le
  have hcTerm_zero : c * Real.log (2 : ℝ) = 0 := by
    linarith
  have hdTerm_zero : d * (2 * Real.log (2 : ℝ)) = 0 := by
    linarith
  have hc0 : c = 0 := by
    exact (mul_eq_zero.mp hcTerm_zero).resolve_right hlog2_pos.ne'
  have hd0 : d = 0 := by
    exact (mul_eq_zero.mp hdTerm_zero).resolve_right htwoLog2_pos.ne'
  exact ⟨⟨hc0, hd0⟩, paper_fold_groupoid_maxblock_chi_homogeneity⟩

end Omega.EA
