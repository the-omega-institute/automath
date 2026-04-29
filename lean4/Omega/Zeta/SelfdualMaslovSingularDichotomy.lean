import Omega.Zeta.BlaschkePointSpectrumCorrespondence

namespace Omega.Zeta

open blaschke_point_spectrum_correspondence_data

/-- Paper label: `prop:selfdual-maslov-singular-dichotomy`. -/
theorem paper_selfdual_maslov_singular_dichotomy
    (D : blaschke_point_spectrum_correspondence_data)
    (singularInner boundaryResidual phaseClosureAudit : Prop)
    (hBoundary : singularInner → boundaryResidual)
    (hAudit : phaseClosureAudit → ¬ singularInner) :
    D.pointSpectrumMatchesZeros ∧ D.pointSpectrumDimension = D.blaschkeDegree ∧
      (singularInner → boundaryResidual) ∧ (phaseClosureAudit → ¬ singularInner) := by
  rcases paper_blaschke_point_spectrum_correspondence D with ⟨hmatch, hdegree⟩
  exact ⟨hmatch, hdegree, hBoundary, hAudit⟩

end Omega.Zeta
