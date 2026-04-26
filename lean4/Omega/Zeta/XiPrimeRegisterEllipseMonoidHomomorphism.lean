import Omega.Conclusion.PrimeRegisterEllipseCompleteEquivalence

namespace Omega.Zeta

/-- Paper label: `thm:xi-prime-register-ellipse-monoid-homomorphism`. -/
theorem paper_xi_prime_register_ellipse_monoid_homomorphism :
    Omega.Conclusion.primeRegisterMonoidHomLaw ∧
      Omega.Conclusion.primeRegisterEllipseMapInjective ∧
      Omega.Conclusion.primeRegisterEllipseImageClassification := by
  exact Omega.Conclusion.paper_conclusion_prime_register_ellipse_complete_equivalence

end Omega.Zeta
