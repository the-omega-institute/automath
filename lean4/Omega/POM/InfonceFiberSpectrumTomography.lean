import Omega.Folding.FoldInfoNCELossTowerNewtonPronyCompleteness

namespace Omega.POM

/-- Paper label: `thm:pom-infonce-fiber-spectrum-tomography`. The chapter-level fiber-spectrum
reconstruction statement is exactly the existing Newton/Prony completeness package for the
InfoNCE loss tower. -/
theorem paper_pom_infonce_fiber_spectrum_tomography
    (D : Omega.Folding.FoldInfoNCELossTowerNewtonPronyData) : D.newtonPronyCompleteness := by
  exact Omega.Folding.paper_fold_infonce_loss_tower_newton_prony_completeness D

end Omega.POM
