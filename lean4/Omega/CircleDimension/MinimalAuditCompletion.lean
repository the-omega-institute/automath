import Mathlib.Tactic
import Omega.CircleDimension.CircleDim

namespace Omega.CircleDimension

/-- The paper-facing audit loss is the kernel rank of the free part. -/
abbrev auditLoss (f : CircleDimHomData) : Nat :=
  cdimDefect f

/-- The optimal audit completion adjoins a free ledger of rank `auditLoss f`
    together with an arbitrary torsion certificate. -/
def optimalAuditCompletion (f : CircleDimHomData) (torsionRank : Nat) : Nat × Nat :=
  (auditLoss f, torsionRank)

/-- Paper wrapper for the minimal circle-dimension audit completion theorem.
    thm:cdim-minimal-audit-completion -/
theorem paper_cdim_minimal_audit_completion (f : CircleDimHomData) :
    (∀ R_rank torsionRank : Nat, auditLoss f ≤ R_rank →
      circleDim (auditLoss f) 0 ≤ circleDim R_rank torsionRank) ∧
    (∀ torsionRank : Nat,
      circleDim (optimalAuditCompletion f torsionRank).1
          (optimalAuditCompletion f torsionRank).2 = circleDim (auditLoss f) 0) := by
  refine ⟨?_, ?_⟩
  · intro R_rank torsionRank hR
    simpa [auditLoss, cdimDefect, circleDim] using
      cdim_min_ledger_cost f R_rank hR
  · intro torsionRank
    simp [optimalAuditCompletion, auditLoss, cdimDefect, circleDim]

end Omega.CircleDimension
