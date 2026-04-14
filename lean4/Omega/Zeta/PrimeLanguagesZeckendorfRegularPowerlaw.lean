import Omega.Zeta.ETDSZeckendorfRegularPowerlaw

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the Zeckendorf regular-language power-law
    theorem in the prime-languages paper.
    thm:zeckendorf-regular-powerlaw -/
theorem paper_prime_languages_zeckendorf_regular_powerlaw :
    (∀ m, Fintype.card (Omega.X (m + 2)) = Fintype.card (Omega.X (m + 1)) + Fintype.card (Omega.X m)) ∧
    (Nat.fib 8 = 21 ∧ Nat.fib 10 = 55 ∧ Nat.fib 12 = 144) :=
  paper_etds_zeckendorf_regular_powerlaw

end Omega.Zeta
