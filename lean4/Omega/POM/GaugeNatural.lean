import Omega.Folding.Defect

namespace Omega.POM

/-- Paper label: `prop:pom-gauge-natural`. -/
theorem paper_pom_gauge_natural (m : ℕ) (w : Omega.Word (m + 1)) :
    Omega.Fold (Omega.X.restrict (Omega.Fold w)).1 = Omega.X.restrict (Omega.Fold w) := by
  simpa using (Omega.Fold_stable (Omega.X.restrict (Omega.Fold w)))

end Omega.POM
