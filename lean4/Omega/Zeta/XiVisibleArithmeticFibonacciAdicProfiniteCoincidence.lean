import Omega.Zeta.XiVisibleArithmeticFibonacciCofinalQuotients

namespace Omega.Zeta

/-- Paper label: `thm:xi-visible-arithmetic-fibonacci-adic-profinite-coincidence`. -/
def paper_xi_visible_arithmetic_fibonacci_adic_profinite_coincidence
    (hcofinal : Omega.Zeta.FibonacciFoldModuliCofinal) :
    Omega.Zeta.FibProfiniteCompletion ≃+* Omega.Zeta.Zhat :=
  cofinalSubsystemCompletionEquiv hcofinal

end Omega.Zeta
