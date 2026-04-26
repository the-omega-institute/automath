import Omega.EA.AddressNaturality

namespace Omega.EA.StableAddFiniteResolutionCompatibility

/-- Paper-facing seed for compatibility between finite-resolution addressing and stable addition. -/
theorem paper_ea_stable_add_finite_resolution_compatibility_seeds
    (m : ℕ) (a b : ℤ) :
    Omega.EA.AddressNaturality.addr m (a + b) =
      Omega.EA.AddressNaturality.addr m a + Omega.EA.AddressNaturality.addr m b := by
  exact Omega.EA.AddressNaturality.addr_add m a b

/-- Wrapper theorem matching the paper-facing package name. -/
theorem paper_ea_stable_add_finite_resolution_compatibility_package
    (m : ℕ) (a b : ℤ) :
    Omega.EA.AddressNaturality.addr m (a + b) =
      Omega.EA.AddressNaturality.addr m a + Omega.EA.AddressNaturality.addr m b :=
  paper_ea_stable_add_finite_resolution_compatibility_seeds m a b

/-- Paper proposition `prop:stable-add-finite-resolution-compatibility`, collapsed to the
finite-resolution address additivity already proved in `Omega.EA.AddressNaturality`. -/
theorem paper_stable_add_finite_resolution_compatibility (m : ℕ) (a b : ℤ) :
    Omega.EA.AddressNaturality.addr m (a + b) =
      Omega.EA.AddressNaturality.addr m a + Omega.EA.AddressNaturality.addr m b := by
  exact Omega.EA.AddressNaturality.addr_add m a b

end Omega.EA.StableAddFiniteResolutionCompatibility
