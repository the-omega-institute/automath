import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-boundary-patterson-sullivan-kms`. -/
theorem paper_xi_time_boundary_patterson_sullivan_kms
    (linearIsoperimetric growthExponentExists conformalDensity kmsCorrespondence : Prop)
    (hlin : linearIsoperimetric)
    (hgrowth : growthExponentExists)
    (hps : linearIsoperimetric → growthExponentExists → conformalDensity)
    (hkms : conformalDensity → kmsCorrespondence) :
    conformalDensity ∧ kmsCorrespondence := by
  have hdensity : conformalDensity := hps hlin hgrowth
  exact ⟨hdensity, hkms hdensity⟩

end Omega.Zeta
