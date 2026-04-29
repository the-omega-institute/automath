import Omega.EA.Wedderburn

namespace Omega.POM

/-- Paper-facing fiber-index CGF package assembled from the existing low-moment specializations,
the general moment identity, and the total fiber-count identity.
    prop:pom-fiber-index-cgf -/
theorem paper_pom_fiber_index_cgf :
    (∀ m, ∑ x : X m, X.fiberMultiplicity x ^ 2 = momentSum 2 m) ∧
    (∀ m, ∑ x : X m, X.fiberMultiplicity x ^ 3 = momentSum 3 m) ∧
    (∀ m, ∑ x : X m, X.fiberMultiplicity x ^ 4 = momentSum 4 m) ∧
    (∀ q m, ∑ x : X m, X.fiberMultiplicity x ^ q = momentSum q m) ∧
    (∀ m, ∑ x : X m, X.fiberMultiplicity x = 2 ^ m) := by
  exact Omega.EA.paper_pom_fiber_index_cgf_package

end Omega.POM
