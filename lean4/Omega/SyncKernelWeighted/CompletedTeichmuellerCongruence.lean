import Mathlib.Tactic
import Omega.SyncKernelWeighted.CompletedPrimeCongruence

namespace Omega.SyncKernelWeighted

open Polynomial

/-- Paper label: `cor:completed-teichmueller-congruence`. Combining the completed prime
congruence `\hat a_p(s) ≡ C_p(s) (mod p)` with the Frobenius/Chebyshev congruence
`C_p(s) ≡ s^p (mod p)` yields the Teichmüller congruence
`\hat a_p(s) ≡ s^p (mod p)`. -/
theorem paper_completed_teichmueller_congruence
    (D : Omega.SyncKernelWeighted.CompletedPrimeCongruenceData)
    (hcheb : Omega.SyncKernelWeighted.PolyZModEq D.p D.chebyshevPrime (Polynomial.X ^ D.p)) :
    Omega.SyncKernelWeighted.PolyZModEq D.p (D.hatA D.p) (Polynomial.X ^ D.p) := by
  exact polyZModEq_trans (paper_completed_prime_congruence D) hcheb

end Omega.SyncKernelWeighted
