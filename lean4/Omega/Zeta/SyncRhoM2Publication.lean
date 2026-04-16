import Omega.Zeta.SyncRhoM2ClosedForm

namespace Omega.Zeta

/-- Publication-facing wrapper for `cor:rho-m2-closed-form`
in the self-dual and ETDS kernel papers. -/
theorem paper_sync_rho_m2_publication_seeds :
    let r : ℝ := Real.sqrt (2 - Real.sqrt 3)
    r^4 - 4 * r^2 + 1 = 0 ∧ 0 ≤ r :=
  SyncRhoM2ClosedForm.paper_sync_rho_m2_closed_form_seeds

end Omega.Zeta
