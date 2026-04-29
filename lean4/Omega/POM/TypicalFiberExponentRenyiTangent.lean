import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `prop:pom-typical-fiber-exponent-renyi-tangent`. -/
theorem paper_pom_typical_fiber_exponent_renyi_tangent (h0 hMac yStar renyiSlopeAtOne : ℝ)
    (hLedger : yStar = h0 - hMac) (hTangent : yStar = renyiSlopeAtOne) :
    yStar = h0 - hMac ∧ yStar = renyiSlopeAtOne := by
  exact ⟨hLedger, hTangent⟩

end Omega.POM
