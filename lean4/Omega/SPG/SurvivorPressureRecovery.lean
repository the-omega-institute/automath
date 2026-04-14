import Omega.SPG.PressureGap

namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for survivor pressure recovery in the
    scan-projection ETDS paper.
    cor:survivor-pressure-recovery -/
theorem paper_scan_projection_address_survivor_pressure_recovery
    (ρpartial PY Ppartial rate limLogε : ℝ) (primitive nondeg : Prop)
    (hρ : ρpartial = Real.exp (Ppartial - PY))
    (hRate : primitive → ρpartial < 1 → nondeg → rate = -Real.log ρpartial)
    (hLim : limLogε = -rate) :
    primitive → ρpartial < 1 → nondeg → Ppartial = PY + limLogε := by
  intro hprimitive hsub hnondeg
  rw [hLim, paper_scan_projection_address_pressure_gap ρpartial PY Ppartial rate primitive
    nondeg hρ hRate hprimitive hsub hnondeg]
  ring

end Omega.SPG
