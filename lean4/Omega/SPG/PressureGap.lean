import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the pressure-gap corollary in the scan-projection ETDS paper.
    cor:pressure-gap -/
theorem paper_scan_projection_address_pressure_gap
    (ρpartial PY Ppartial rate : ℝ) (primitive nondeg : Prop)
    (hρ : ρpartial = Real.exp (Ppartial - PY))
    (hRate : primitive → ρpartial < 1 → nondeg → rate = -Real.log ρpartial) :
    primitive → ρpartial < 1 → nondeg → rate = PY - Ppartial := by
  intro hprimitive hsub hnondeg
  rw [hRate hprimitive hsub hnondeg, hρ, Real.log_exp]
  ring

end Omega.SPG
