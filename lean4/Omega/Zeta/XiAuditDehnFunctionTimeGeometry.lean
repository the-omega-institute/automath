import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-audit-dehn-function-time-geometry`. -/
theorem paper_xi_audit_dehn_function_time_geometry
    (dehnEquivalentToIsoperimetric linearAuditBound hyperbolicTimeGraph : Prop)
    (hlin : dehnEquivalentToIsoperimetric → linearAuditBound)
    (hhyp : linearAuditBound → hyperbolicTimeGraph) :
    dehnEquivalentToIsoperimetric → linearAuditBound ∧ hyperbolicTimeGraph := by
  intro hdehn
  exact ⟨hlin hdehn, hhyp (hlin hdehn)⟩

end Omega.Zeta
