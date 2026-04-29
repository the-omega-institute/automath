import Omega.Folding.FoldInfoNCETriangularInversionCollisionSpectrum

namespace Omega.Zeta

/-- Paper label: `thm:xi-fold-bayes-infonce-newton-binomial-inversion`.
This chapter-level wrapper packages the already verified forward-difference / triangular inversion
statement for the Bayes--InfoNCE loss tower. -/
theorem paper_xi_fold_bayes_infonce_newton_binomial_inversion (m Q : ℕ) :
    Omega.Folding.foldInfoNCETriangularInversionCollisionSpectrumStatement m Q := by
  simpa using Omega.Folding.paper_fold_infonce_triangular_inversion_collision_spectrum m Q

end Omega.Zeta
