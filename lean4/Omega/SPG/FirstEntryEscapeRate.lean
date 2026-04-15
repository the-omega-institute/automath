import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for first-entry residue events and escape
    rates in the scan-projection ETDS paper.
    thm:first-entry-escape-rate -/
theorem paper_scan_projection_address_first_entry_escape_rate
    (ρH PY PYH escapeRate ambiguityRate : ℝ)
    (mixing holeNonempty holeProper : Prop)
    (hρ : ρH = Real.exp (PYH - PY))
    (hEscape :
      mixing → ρH < 1 → holeNonempty → holeProper → escapeRate = -Real.log ρH)
    (hAmbiguity : ambiguityRate = escapeRate) :
    mixing → ρH < 1 → holeNonempty → holeProper →
      escapeRate = PY - PYH ∧ ambiguityRate = PY - PYH := by
  intro hMix hSub hNonempty hProper
  have hRate : escapeRate = PY - PYH := by
    rw [hEscape hMix hSub hNonempty hProper, hρ, Real.log_exp]
    ring
  exact ⟨hRate, hAmbiguity.trans hRate⟩

end Omega.SPG
