import Omega.Zeta.PsiTruncationBounds

namespace Omega.Zeta

/-- Publication-facing wrapper for
`cor:finite-part-gap-positive`
in `2026_dynamical_zeta_finite_part_spectral_fingerprint_etds`. -/
theorem paper_etds_finite_part_gap_positive
    (x : ℝ) (hx₀ : 0 < x) (hx₁ : x < 1) :
    0 < PsiTruncationBounds.psi x :=
  PsiTruncationBounds.paper_finite_part_gap_positive x hx₀ hx₁

end Omega.Zeta
