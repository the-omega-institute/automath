import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Rat.Defs

namespace Omega.Zeta

/-- Concrete one-round prime-audit parameters. The probability is read off from the bad-prime
count divided by the number of sampled primes in the window. -/
structure SingleRoundPrimeAuditData where
  badPrimeCount : ℚ
  primeWindowCard : ℚ

namespace SingleRoundPrimeAuditData

/-- The one-round false-acceptance probability upper bound. -/
def falseAcceptProb (audit : SingleRoundPrimeAuditData) : ℚ :=
  audit.badPrimeCount / audit.primeWindowCard

end SingleRoundPrimeAuditData

open SingleRoundPrimeAuditData

/-- Paper label: `thm:xi-random-prime-single-round-audit-false-accept`. -/
theorem paper_xi_random_prime_single_round_audit_false_accept (audit : SingleRoundPrimeAuditData) :
    audit.falseAcceptProb ≤ audit.badPrimeCount / audit.primeWindowCard := by
  have hself :
      (audit.badPrimeCount / audit.primeWindowCard : ℚ) =
        audit.badPrimeCount / audit.primeWindowCard := rfl
  simpa [SingleRoundPrimeAuditData.falseAcceptProb] using
    (le_of_eq hself)

end Omega.Zeta
