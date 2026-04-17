import Omega.CircleDimension.SignedStokesCohomologicalCharacterization

namespace Omega.CircleDimension

open Omega.CircleDimension.StokesHomologyExactSplitting

/-- Formal transgression wrapper extracted from the split Stokes exact sequence and the
cohomological rank identification.
    prop:cdim-stokes-radial-fibration-transgression -/
theorem paper_cdim_stokes_radial_fibration_transgression (u v : ℕ) :
    Function.Injective (stokesBoundaryInclusion u v) ∧
      Function.Surjective (stokesProjection u v) ∧
      Set.range (stokesBoundaryInclusion u v) = {p | stokesProjection u v p = 0} ∧
      stokesRelativeH2Rank u v = v := by
  rcases paper_cdim_signed_stokes_cohomological_characterization u v with
    ⟨hInj, hSurj, hRange, _hSplit, _hH1, hRel, _hSigma, _hWdim, _hClosed⟩
  exact ⟨hInj, hSurj, hRange, hRel⟩

end Omega.CircleDimension
