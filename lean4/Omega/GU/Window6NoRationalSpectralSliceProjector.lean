import Omega.GU.TerminalWindowRationalCommutantIdempotentRigidity

namespace Omega.GU

/-- Paper-facing corollary: a rational spectral slice projector is already forbidden by the
terminal commutant/idempotent rigidity package, and any separating rational polynomial would
produce such a projector. Hence neither object can exist.
    cor:window6-no-rational-spectral-slice-projector -/
theorem paper_window6_no_rational_spectral_slice_projector
    (rationalSpectralProjectorExists rationalSeparatingPolynomialExists : Prop)
    (hRigidity : rationalSpectralProjectorExists -> False)
    (hPolyToProj : rationalSeparatingPolynomialExists -> rationalSpectralProjectorExists) :
    ¬ rationalSpectralProjectorExists ∧ ¬ rationalSeparatingPolynomialExists := by
  refine ⟨hRigidity, ?_⟩
  intro hPoly
  exact hRigidity (hPolyToProj hPoly)

end Omega.GU
