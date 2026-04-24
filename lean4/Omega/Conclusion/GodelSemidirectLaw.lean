import Omega.Conclusion.PrimeRegister

namespace Omega.Conclusion

/-- Paper-facing semidirect-product form of the Gödel concatenation law.
    thm:conclusion-godel-semidirect-law -/
theorem paper_conclusion_godel_semidirect_law (primes : Nat → Nat) (u v : List Nat) :
    godelEncoding primes 0 (u ++ v) =
      godelEncoding primes 0 u * godelEncoding primes u.length v := by
  simpa using godelEncoding_append primes 0 u v

end Omega.Conclusion
