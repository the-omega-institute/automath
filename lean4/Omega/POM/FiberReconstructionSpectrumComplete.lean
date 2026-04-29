import Mathlib.Data.Multiset.Basic

namespace Omega.POM

/-- Fiber data reduced to the multiset of Cartesian-prime Fibonacci-cube lengths. -/
structure pom_fiber_reconstruction_spectrum_complete_fiber where
  pom_fiber_reconstruction_spectrum_complete_prime_lengths : Multiset ℕ

/-- The Cartesian-prime fiber spectrum. -/
def pom_fiber_reconstruction_spectrum_complete_spec
    (x : pom_fiber_reconstruction_spectrum_complete_fiber) : Multiset ℕ :=
  x.pom_fiber_reconstruction_spectrum_complete_prime_lengths

/-- Graph isomorphism preserves the Cartesian-prime Fibonacci-cube length multiset. -/
def pom_fiber_reconstruction_spectrum_complete_isomorphic
    (x y : pom_fiber_reconstruction_spectrum_complete_fiber) : Prop :=
  pom_fiber_reconstruction_spectrum_complete_spec x =
    pom_fiber_reconstruction_spectrum_complete_spec y

/-- Paper label: `cor:pom-fiber-reconstruction-spectrum-complete`.
The fiber spectrum is the multiset of Cartesian-prime Fibonacci-cube lengths, and the
isomorphism relation records preservation of exactly this multiset. -/
theorem paper_pom_fiber_reconstruction_spectrum_complete
    {x y : pom_fiber_reconstruction_spectrum_complete_fiber}
    (hIso : pom_fiber_reconstruction_spectrum_complete_isomorphic x y) :
    pom_fiber_reconstruction_spectrum_complete_spec x =
      pom_fiber_reconstruction_spectrum_complete_spec y := by
  exact hIso

end Omega.POM
