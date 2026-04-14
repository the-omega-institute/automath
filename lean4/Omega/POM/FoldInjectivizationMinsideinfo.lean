import Omega.Folding.MomentBounds

namespace Omega.POM.FoldInjectivizationMinsideinfo

/-- Seeds for the fold injectivization minimum side-information budget.
    cor:pom-fold-injectivization-minsideinfo-equals-unknot-norm-square -/
theorem paper_pom_fold_injectivization_minsideinfo_seeds :
    Omega.X.maxFiberMultiplicity 6 = 5 ∧ Nat.clog 2 (Omega.X.maxFiberMultiplicity 6) = 3 := by
  rcases Omega.fold6_binary_auxbits with ⟨hmax, hclog⟩
  refine ⟨hmax, ?_⟩
  simpa [hmax] using hclog

/-- Package for the fold injectivization minimum side-information budget.
    cor:pom-fold-injectivization-minsideinfo-equals-unknot-norm-square -/
theorem paper_pom_fold_injectivization_minsideinfo_package :
    Omega.X.maxFiberMultiplicity 6 = 5 ∧ Nat.clog 2 (Omega.X.maxFiberMultiplicity 6) = 3 :=
  paper_pom_fold_injectivization_minsideinfo_seeds

end Omega.POM.FoldInjectivizationMinsideinfo
