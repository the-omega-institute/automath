import Omega.Conclusion.ScreenAuditGapSupermodularity
import Mathlib.Tactic

namespace Omega.SPG

open Finset

/-- SPG-facing wrapper for the abstract rank/corank supermodularity package.
    thm:spg-screen-rank-matroid-supermodularity -/
theorem paper_spg_screen_rank_matroid_supermodularity
    {V : Type*} [DecidableEq V] (rho : Nat) (r : Finset V → Nat)
    (hrho : ∀ s, r s ≤ rho)
    (hmono : ∀ {s t : Finset V}, s ⊆ t → r s ≤ r t)
    (hsub : ∀ s t, r (s ∩ t) + r (s ∪ t) ≤ r s + r t) :
    (∀ s t, r (s ∩ t) + r (s ∪ t) ≤ r s + r t) ∧
      (∀ {s t : Finset V}, s ⊆ t → r s ≤ r t) ∧
      (∀ s t,
        Omega.Conclusion.ScreenAuditGapSupermodularity.AuditGap rho r s +
            Omega.Conclusion.ScreenAuditGapSupermodularity.AuditGap rho r t ≤
          Omega.Conclusion.ScreenAuditGapSupermodularity.AuditGap rho r (s ∩ t) +
            Omega.Conclusion.ScreenAuditGapSupermodularity.AuditGap rho r (s ∪ t)) ∧
      (∀ {s t : Finset V}, s ⊆ t →
        Omega.Conclusion.ScreenAuditGapSupermodularity.AuditGap rho r t ≤
          Omega.Conclusion.ScreenAuditGapSupermodularity.AuditGap rho r s) := by
  refine ⟨hsub, hmono, ?_, ?_⟩
  · exact Omega.Conclusion.ScreenAuditGapSupermodularity.auditGap_supermodular rho r hrho hsub
  · intro s t hst
    dsimp [Omega.Conclusion.ScreenAuditGapSupermodularity.AuditGap]
    have hs := hrho s
    have ht := hrho t
    have hst' := hmono hst
    omega

end Omega.SPG
