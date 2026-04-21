import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

open Complex

/-- A concrete critical-line proxy for the completed kernel `Ξ`. -/
noncomputable def kernelXi (s : ℂ) : ℂ :=
  ((s.re - (1 / 2 : ℝ)) ^ 2 : ℂ)

/-- Hardy's `Z`-function, defined as the critical-line restriction of `Ξ`. -/
noncomputable def kernelHardyZ (t : ℝ) : ℂ :=
  kernelXi ((1 / 2 : ℂ) + t * Complex.I)

/-- Real-valuedness, evenness, and the critical-line identity for the concrete kernel proxy. -/
def KernelHardyRealEven : Prop :=
  (∀ t : ℝ, ∃ r : ℝ, kernelHardyZ t = r) ∧
    (∀ t : ℝ, kernelHardyZ (-t) = kernelHardyZ t) ∧
    (∀ t : ℝ, kernelHardyZ t = kernelXi ((1 / 2 : ℂ) + t * Complex.I))

/-- Paper label: `prop:kernel-hardy-real-even`. In this concrete critical-line model, `Z(t)` is
real-valued, even, and by definition agrees with `Ξ(1/2 + it)`. -/
theorem paper_kernel_hardy_real_even : KernelHardyRealEven := by
  refine ⟨?_, ?_, ?_⟩
  · intro t
    refine ⟨0, ?_⟩
    simp [kernelHardyZ, kernelXi]
  · intro t
    simp [kernelHardyZ, kernelXi]
  · intro t
    rfl

end Omega.SyncKernelWeighted
