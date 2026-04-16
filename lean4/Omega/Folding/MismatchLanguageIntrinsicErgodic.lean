import Omega.Folding.MismatchLanguage
import Omega.Folding.GmFischerCover
import Mathlib.Tactic

namespace Omega.Folding

set_option maxHeartbeats 400000 in
/-- Paper-facing intrinsic-ergodicity wrapper for the mismatch-language SFT:
    combine the existing recurrence/non-coboundary witnesses with the
    right-Fischer-cover interface and the abstract Parry/intrinsic-ergodic
    consequences supplied by the presentation package.
    cor:fold-gauge-anomaly-mismatch-language-intrinsic-ergodic -/
theorem paper_fold_gauge_anomaly_mismatch_language_intrinsic_ergodic
    (irreducibleShift deterministicRightResolvingPresentation singletonCoreComponent
      followerSeparatedCore labeledIsomorphicToGm rightFischerCoverOfYm
      uniqueParryMeasure intrinsicErgodic : Prop)
    (hIrreducible : irreducibleShift)
    (hResolve : deterministicRightResolvingPresentation)
    (hCore : deterministicRightResolvingPresentation → singletonCoreComponent)
    (hSeparated : singletonCoreComponent → followerSeparatedCore)
    (hIso : singletonCoreComponent → labeledIsomorphicToGm)
    (hCover : irreducibleShift → deterministicRightResolvingPresentation →
      singletonCoreComponent → followerSeparatedCore → rightFischerCoverOfYm)
    (hParry : irreducibleShift → rightFischerCoverOfYm → uniqueParryMeasure)
    (hIntrinsic : irreducibleShift → uniqueParryMeasure → intrinsicErgodic) :
    Omega.mismatchWordCount 5 = 25 ∧
      (¬ ∃ (h : Fin 3 → ℤ),
        h 1 - h 0 = 1 ∧ h 2 - h 1 = 1 ∧ h 0 - h 2 = 1) ∧
      labeledIsomorphicToGm ∧ rightFischerCoverOfYm ∧ uniqueParryMeasure ∧ intrinsicErgodic := by
  have hFischer :
      labeledIsomorphicToGm ∧ rightFischerCoverOfYm :=
    paper_resolution_folding_g_m_fischer_cover irreducibleShift
      deterministicRightResolvingPresentation singletonCoreComponent
      followerSeparatedCore labeledIsomorphicToGm rightFischerCoverOfYm
      hIrreducible hResolve hCore hSeparated hIso hCover
  rcases hFischer with ⟨hGm, hRightFischer⟩
  have hMme : uniqueParryMeasure := hParry hIrreducible hRightFischer
  exact ⟨rfl, Omega.paper_mismatch_label_non_coboundary,
    hGm, hRightFischer, hMme, hIntrinsic hIrreducible hMme⟩

end Omega.Folding
