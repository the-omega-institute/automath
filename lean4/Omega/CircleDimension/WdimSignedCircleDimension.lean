import Omega.CircleDimension.OrthogonalAmalgamatedWdim
import Omega.CircleDimension.SignedCircleDimension

namespace Omega.CircleDimension

/-- General-monoid Stokes character contraction identifies the weighted dimension with the signed
circle dimension in the torsion-free quotient case.
    thm:cdim-stokes-character-contraction-general-monoid -/
theorem paper_cdim_stokes_character_contraction_general_monoid (u v : ℕ) :
    Omega.CircleDimension.wdim (u : ℚ) (v : ℚ) = Omega.CircleDimension.cdimSigned u v 0 0 := by
  rw [wdim_u_linear]
  simpa [cdimSignedOrthant] using (paper_cdim_signed_orthant_closed.1 u v 0).symm

end Omega.CircleDimension
