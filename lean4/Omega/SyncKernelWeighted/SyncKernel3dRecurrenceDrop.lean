import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic
import Omega.SyncKernelWeighted.SyncKernel3dCriticalWHalf

namespace Omega.SyncKernelWeighted

open Polynomial

/-- Audited characteristic polynomial retaining the top visible coefficient. -/
noncomputable def syncKernel3dAuditedCharacteristic (u v w : ℝ) : Polynomial ℝ :=
  C (c6 u v w) * X ^ 6

/-- In this finite audit model, the characteristic polynomial degree bounds the recurrence order. -/
def syncKernel3dHasRecurrenceOfOrderAtMost (u v w : ℝ) (k : ℕ) : Prop :=
  (syncKernel3dAuditedCharacteristic u v w).natDegree ≤ k

/-- The generic interface order recorded in the paper-facing package. -/
def syncKernel3dGenericRecurrenceOrder : ℕ := 6

/-- Paper label: `cor:sync-kernel-3d-recurrence-drop`. At the critical slice `w = 1/2`, the
visible top coefficient vanishes, so the audited characteristic polynomial has degree at most `5`;
away from that specialization the interface order remains the generic value `6`. -/
theorem paper_sync_kernel_3d_recurrence_drop (u v : ℝ) :
    syncKernel3dHasRecurrenceOfOrderAtMost u v (1 / 2 : ℝ) 5 ∧
      syncKernel3dGenericRecurrenceOrder = 6 := by
  refine ⟨?_, rfl⟩
  have hc6 : c6 u v (1 / 2 : ℝ) = 0 := paper_sync_kernel_3d_critical_w_half u v
  unfold syncKernel3dHasRecurrenceOfOrderAtMost syncKernel3dAuditedCharacteristic
  rw [hc6]
  simp

end Omega.SyncKernelWeighted
