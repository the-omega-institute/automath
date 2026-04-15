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

/-- Paper wrapper for the circle-dimension loss chain rule and the induced additivity
    of the minimal audit-completion cost.
    cor:cdim-loss-chain-rule -/
def paper_cdim_loss_chain_rule : Prop :=
  (∀ (f g : CircleDimHomData) (hfg : f.targetRank = g.sourceRank)
     (restrictedKerRank : Nat) (hRestrict : restrictedKerRank ≤ g.kernelRank)
     (hRestrictBound : restrictedKerRank ≤ f.imageRank)
     (hImageSplit : f.imageRank ≤ restrictedKerRank + g.imageRank),
    auditLoss (f.comp g hfg restrictedKerRank hRestrict hRestrictBound hImageSplit) =
      auditLoss f + restrictedKerRank) ∧
  (∀ (f g : CircleDimHomData) (hfg : f.targetRank = g.sourceRank)
     (restrictedKerRank : Nat) (hRestrict : restrictedKerRank ≤ g.kernelRank)
     (hRestrictBound : restrictedKerRank ≤ f.imageRank)
     (hImageSplit : f.imageRank ≤ restrictedKerRank + g.imageRank)
     (torsionRank : Nat),
    circleDim
        (optimalAuditCompletion
          (f.comp g hfg restrictedKerRank hRestrict hRestrictBound hImageSplit) torsionRank).1
        (optimalAuditCompletion
          (f.comp g hfg restrictedKerRank hRestrict hRestrictBound hImageSplit) torsionRank).2 =
      circleDim (optimalAuditCompletion f torsionRank).1
        (optimalAuditCompletion f torsionRank).2 + circleDim restrictedKerRank 0)

theorem paper_cdim_loss_chain_rule_proof : paper_cdim_loss_chain_rule := by
  refine ⟨?_, ?_⟩
  · intro f g hfg restrictedKerRank hRestrict hRestrictBound hImageSplit
    simpa [paper_cdim_loss_chain_rule, auditLoss] using
      cdimDefect_comp f g hfg restrictedKerRank hRestrict hRestrictBound hImageSplit
  · intro f g hfg restrictedKerRank hRestrict hRestrictBound hImageSplit torsionRank
    rw [(paper_cdim_minimal_audit_completion
        (f.comp g hfg restrictedKerRank hRestrict hRestrictBound hImageSplit)).2 torsionRank]
    rw [(paper_cdim_minimal_audit_completion f).2 torsionRank]
    have hLoss :
        auditLoss (f.comp g hfg restrictedKerRank hRestrict hRestrictBound hImageSplit) =
          auditLoss f + restrictedKerRank := by
      simpa [auditLoss] using
        cdimDefect_comp f g hfg restrictedKerRank hRestrict hRestrictBound hImageSplit
    rw [hLoss]
    simp [auditLoss, circleDim]

end Omega.CircleDimension
