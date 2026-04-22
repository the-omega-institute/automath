import Mathlib.Tactic
import Omega.CircleDimension.LissajousBranchDivisorBoundarySignature
import Omega.CircleDimension.LissajousPhaseCirclePrimeLedgerKernel

namespace Omega.CircleDimension

theorem paper_cdim_lissajous_boundary_kernel_recovery (a b : ℕ) (δ : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hδ : ¬ lissajousDoubleCornerPhaseCondition a b δ) :
    a = lissajousBranchDivisor a b * lissajousVisibleXPlusCount a b δ ∧
      b = lissajousBranchDivisor a b * lissajousVisibleYPlusCount a b δ ∧
      lissajousPrimeLedgerKernel a b = lissajousBranchDivisor a b := by
  rcases paper_cdim_lissajous_branch_divisor_boundary_signature a b δ ha hb with
    ⟨_, _, _, _, _, hvisible⟩
  rcases hvisible hδ with ⟨hx, _, hy, _⟩
  rcases paper_cdim_lissajous_phase_circle_prime_ledger_kernel a b (Nat.succ_le_of_lt ha)
      (Nat.succ_le_of_lt hb) δ with
    ⟨_, hda, hdb, _, _, _⟩
  refine ⟨?_, ?_, rfl⟩
  · calc
      a = Nat.gcd a b * (a / Nat.gcd a b) := by
        exact (Nat.mul_div_cancel' hda).symm
      _ = lissajousBranchDivisor a b * lissajousVisibleXPlusCount a b δ := by
        rw [hx]
        rfl
  · calc
      b = Nat.gcd a b * (b / Nat.gcd a b) := by
        exact (Nat.mul_div_cancel' hdb).symm
      _ = lissajousBranchDivisor a b * lissajousVisibleYPlusCount a b δ := by
        rw [hy]
        rfl

end Omega.CircleDimension
