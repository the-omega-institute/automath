import Omega.Folding.Window6

namespace Omega.CircleDimension

/-- Paper-facing wrapper for the boxwise audit-stability characterization.
    prop:cdim-audit-stability-iff-badly-approximable -/
theorem paper_cdim_audit_stability_iff_badly_approximable {d r : ℕ} (hd : 0 < d)
    (hr : 0 < r) (Θ : Matrix (Fin d) (Fin r) ℝ) :
    Omega.AuditStableBoxwise hd hr Θ ↔ Omega.BadlyApproximable hd hr Θ := by
  constructor
  · exact Omega.auditStableBoxwise_imp_badlyApproximable hd hr
  · exact Omega.badlyApproximable_imp_auditStableBoxwise hd hr

end Omega.CircleDimension
