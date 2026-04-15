import Mathlib.Tactic

namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the entropy ledger of finite refinements.
    thm:entropy-ledger -/
theorem paper_scan_projection_address_entropy_ledger
    (HU HY expectedLogFiber divergence Hcond Hregister : ℝ)
    (hLedger : HU = HY + expectedLogFiber - divergence)
    (hCond : Hcond = HU - HY)
    (hRegister : Hregister = Hcond)
    (hNonneg : 0 ≤ divergence) :
    HU = HY + expectedLogFiber - divergence ∧
      Hcond = expectedLogFiber - divergence ∧
      Hcond ≤ expectedLogFiber ∧
      Hregister = Hcond := by
  have hCondFormula : Hcond = expectedLogFiber - divergence := by
    calc
      Hcond = HU - HY := hCond
      _ = (HY + expectedLogFiber - divergence) - HY := by rw [hLedger]
      _ = expectedLogFiber - divergence := by ring
  refine ⟨hLedger, hCondFormula, ?_, hRegister⟩
  linarith

end Omega.SPG
