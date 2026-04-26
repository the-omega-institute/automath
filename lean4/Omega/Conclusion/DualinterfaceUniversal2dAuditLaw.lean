import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete audit data for the dual-interface `2D` law.  The two interfaces carry explicit
integer audit depths and real slack variables, together with certificates that the depth is the
universal two-dimensional value and that the slack is nonpositive. -/
structure conclusion_dualinterface_universal_2d_audit_law_data where
  collisionAuditDepth : ℕ
  scanAuditDepth : ℕ
  collisionSlack : ℝ
  scanSlack : ℝ
  collisionAuditDepth_eq_two : collisionAuditDepth = 2
  scanAuditDepth_eq_two : scanAuditDepth = 2
  collisionSlack_nonpos : collisionSlack ≤ 0
  scanSlack_nonpos : scanSlack ≤ 0

/-- The collision interface is locked at the universal two-dimensional audit depth. -/
def conclusion_dualinterface_universal_2d_audit_law_data.collision_locked
    (D : conclusion_dualinterface_universal_2d_audit_law_data) : Prop :=
  D.collisionAuditDepth = 2

/-- The scan interface is locked at the universal two-dimensional audit depth. -/
def conclusion_dualinterface_universal_2d_audit_law_data.scan_locked
    (D : conclusion_dualinterface_universal_2d_audit_law_data) : Prop :=
  D.scanAuditDepth = 2

/-- The collision bound has no positive slack. -/
def conclusion_dualinterface_universal_2d_audit_law_data.collision_sharp
    (D : conclusion_dualinterface_universal_2d_audit_law_data) : Prop :=
  D.collisionSlack ≤ 0

/-- The scan bound has no positive slack. -/
def conclusion_dualinterface_universal_2d_audit_law_data.scan_sharp
    (D : conclusion_dualinterface_universal_2d_audit_law_data) : Prop :=
  D.scanSlack ≤ 0

/-- Paper label: `thm:conclusion-dualinterface-universal-2d-audit-law`.  The two audited
two-dimensional interface facts give the locked and sharp forms for both collision and scan
interfaces. -/
theorem paper_conclusion_dualinterface_universal_2d_audit_law
    (D : conclusion_dualinterface_universal_2d_audit_law_data) :
    D.collision_locked ∧ D.scan_locked ∧ D.collision_sharp ∧ D.scan_sharp := by
  exact ⟨D.collisionAuditDepth_eq_two, D.scanAuditDepth_eq_two,
    D.collisionSlack_nonpos, D.scanSlack_nonpos⟩

end Omega.Conclusion
