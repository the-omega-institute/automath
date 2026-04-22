import Omega.Folding.KilloPrimeFreedomNonFinitizability

namespace Omega.Folding

/-- Paper label: `cor:killo-no-finite-additive-register-linearization`. The finite-register
linearization obstruction is exactly the second clause of the prime-freedom non-finitizability
package. -/
theorem paper_killo_no_finite_additive_register_linearization (k : ℕ) :
    killoFiniteRegisterLinearizationObstructed k := by
  exact (paper_killo_prime_freedom_non_finitizability.2) k

end Omega.Folding
