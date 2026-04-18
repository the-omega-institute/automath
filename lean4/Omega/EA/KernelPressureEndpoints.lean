import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Tactic

namespace Omega.EA

/-- A one-state weighted kernel family. For a `1 × 1` positive kernel the Perron root is just the
unique entry, so linear interpolation in the endpoint kernels gives a concrete pressure curve. -/
structure KernelPressureFamily where
  zeroWeight : ℝ
  oneWeight : ℝ
  monotone_weights : zeroWeight ≤ oneWeight

/-- Linear interpolation between the endpoint kernels. -/
def weightedKernel (K : KernelPressureFamily) (u : ℝ) : ℝ :=
  K.zeroWeight + u * (K.oneWeight - K.zeroWeight)

/-- For a one-state kernel family the Perron root is the unique entry. -/
def perronRoot (K : KernelPressureFamily) (u : ℝ) : ℝ :=
  weightedKernel K u

/-- Endpoint identity at `u = 0`. -/
def zeroEndpoint (K : KernelPressureFamily) : Prop :=
  perronRoot K 0 = K.zeroWeight

/-- Endpoint identity at `u = 1`. -/
def oneEndpoint (K : KernelPressureFamily) : Prop :=
  perronRoot K 1 = K.oneWeight

/-- The Perron root varies monotonically and continuously along the interpolation. -/
def monotoneContinuous (K : KernelPressureFamily) : Prop :=
  Monotone (perronRoot K) ∧ Continuous (perronRoot K)

/-- Tensor-product assembly of two one-state kernel families. -/
def multiflowAssembly (K L : KernelPressureFamily) (u : ℝ) : ℝ :=
  perronRoot K u * perronRoot L u

/-- The tensor-product lift is the pointwise product of the interpolated endpoint families. -/
def multiflowLift (K L : KernelPressureFamily) : Prop :=
  multiflowAssembly K L = fun u => weightedKernel K u * weightedKernel L u

/-- `prop:kernel-pressure-endpoints` for the concrete one-state weighted-kernel family. -/
theorem paper_kernel_pressure_endpoints (K L : KernelPressureFamily) :
    zeroEndpoint K ∧ oneEndpoint K ∧ monotoneContinuous K ∧ multiflowLift K L := by
  refine ⟨by simp [zeroEndpoint, perronRoot, weightedKernel], by simp [oneEndpoint, perronRoot,
    weightedKernel], ?_, rfl⟩
  refine ⟨?_, ?_⟩
  · intro u v huv
    dsimp [perronRoot, weightedKernel]
    nlinarith [K.monotone_weights, huv]
  · simpa [perronRoot, weightedKernel] using
      (continuous_const.add (continuous_id.mul continuous_const))

end Omega.EA
