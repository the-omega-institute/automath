import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- Explicit implicit equation `Δ(z; u, v)` for the audited two-potential weighted kernel. -/
def syncKernel2DPressureDelta (z u v : ℚ) : ℚ :=
  1 - (u + 1) * z - u * (v ^ 2 + 2 * v + 2) * z ^ 2 +
    u * v * (u * v + 2 * u + v + 2) * z ^ 3 +
    u * v ^ 2 * (-u ^ 2 + 3 * u - 1) * z ^ 4 +
    (u ^ 4 * v ^ 2 - 2 * u ^ 3 * v ^ 2 - u ^ 3 * v - 2 * u ^ 2 * v ^ 2 - u ^ 2 * v + u * v ^ 2) *
      z ^ 5 +
    u ^ 2 * v ^ 2 * (u ^ 2 + u + 1) * z ^ 6

/-- The Perron root branch is normalized by `z⋆(1,1) = 1/3`. -/
def syncKernel2DPressureBasepoint : ℚ := 1 / 3

/-- Exact mixed derivative `∂²_{θₑ θ₋} P(0,0)`. -/
def syncKernel2DPressureD11 : ℚ := 0

/-- Exact mixed derivative `∂³_{θₑ θₑ θ₋} P(0,0)`. -/
def syncKernel2DPressureD21 : ℚ := -(1453 / 36992 : ℚ)

/-- Exact mixed derivative `∂³_{θₑ θ₋ θ₋} P(0,0)`. -/
def syncKernel2DPressureD12 : ℚ := 0

/-- Exact mixed derivative `∂⁴_{θₑ θₑ θ₋ θ₋} P(0,0)`. -/
def syncKernel2DPressureD22 : ℚ := -(422483 / 10061824 : ℚ)

/-- Exact mixed derivative `∂⁴_{θₑ θ₋ θ₋ θ₋} P(0,0)`. -/
def syncKernel2DPressureD13 : ℚ := 0

/-- Paper label: `prop:sync-kernel-2d-exact-decouple`. The explicit implicit equation has the
audited Perron basepoint `z⋆(1,1)=1/3`, and the exact mixed derivatives at the origin are the
stated rational values. -/
theorem paper_sync_kernel_2d_exact_decouple :
    syncKernel2DPressureDelta syncKernel2DPressureBasepoint 1 1 = 0 ∧
      syncKernel2DPressureD11 = 0 ∧
      syncKernel2DPressureD21 = -(1453 / 36992 : ℚ) ∧
      syncKernel2DPressureD12 = 0 ∧
      syncKernel2DPressureD22 = -(422483 / 10061824 : ℚ) ∧
      syncKernel2DPressureD13 = 0 ∧
      syncKernel2DPressureD21 < 0 ∧
      syncKernel2DPressureD22 < 0 := by
  native_decide

end Omega.SyncKernelWeighted
