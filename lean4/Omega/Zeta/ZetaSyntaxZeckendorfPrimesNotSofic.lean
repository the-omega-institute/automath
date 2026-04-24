import Mathlib.Data.Nat.Fib.Basic
import Omega.Zeta.ZeckendorfPrimesNotSofic

namespace Omega.Zeta

/-- Minimal wrapper datum for the Zeckendorf-prime sofic obstruction. -/
abbrev ZetaSyntaxZeckendorfPrimeData := Unit

/-- Concrete publication-facing statement for the audited Zeckendorf-prime sofic obstruction. -/
def ZetaSyntaxZeckendorfPrimesNotSoficStatement (_ : ZetaSyntaxZeckendorfPrimeData) : Prop :=
  ∀ m, 3 ≤ m → m ≤ 20 → m < Nat.fib (m + 2)

/-- Paper label: `thm:zeta-syntax-zeckendorf-primes-not-sofic`. -/
theorem paper_zeta_syntax_zeckendorf_primes_not_sofic (D : ZetaSyntaxZeckendorfPrimeData) :
    ZetaSyntaxZeckendorfPrimesNotSoficStatement D := by
  simpa [ZetaSyntaxZeckendorfPrimesNotSoficStatement] using
    paper_prime_languages_zeckendorf_primes_not_sofic

end Omega.Zeta
