import Omega.Zeta.ZetaSyntaxZeckendorfPrimesNotSofic

namespace Omega.Zeta

/-- Paper label: `cor:zeta-syntax-zeckendorf-primes-not-regular`. -/
theorem paper_zeta_syntax_zeckendorf_primes_not_regular (D : ZetaSyntaxZeckendorfPrimeData) :
    ZetaSyntaxZeckendorfPrimesNotSoficStatement D := by
  simpa using paper_zeta_syntax_zeckendorf_primes_not_sofic D

end Omega.Zeta
