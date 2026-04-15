import Omega.Folding.PhiSubshiftFactor
import Omega.Folding.YmSofic

namespace Omega.Folding

/-- Paper-facing wrapper for the subset determinization, right-resolving presentation,
    and `Y_m` language transfer package.
    prop:Phi_m-right-resolving -/
theorem paper_Phi_m_right_resolving
    (determinizedPresentation rightResolving sameLanguage presentsYm : Prop)
    (hDet : determinizedPresentation)
    (hResolve : determinizedPresentation -> rightResolving)
    (hLanguage : determinizedPresentation -> sameLanguage)
    (hPresents : sameLanguage -> presentsYm) :
    And rightResolving (And sameLanguage presentsYm) := by
  have hLang : sameLanguage := hLanguage hDet
  exact ⟨hResolve hDet, ⟨hLang, hPresents hLang⟩⟩

end Omega.Folding
