import Mathlib.Tactic
import Omega.Conclusion.PrimeRegister

namespace Omega.Conclusion

/-- Equality of the folded output together with equality of the Gödel-encoded trace already
determines the original `(fold, trace)` pair, hence it determines the source state as soon as
`(fold, trace)` itself is injective.
    thm:conclusion-algorithm-prime-shift-equivalence -/
theorem paper_conclusion_algorithm_prime_shift_equivalence {Omega X : Type*} (fold : Omega → X)
    (trace : Omega → List Nat) (primes : Nat → Nat) (hprime : ∀ i, Nat.Prime (primes i))
    (hstrict : StrictMono primes)
    (hlength : ∀ w1 w2, fold w1 = fold w2 → (trace w1).length = (trace w2).length)
    (hinj : Function.Injective fun w => (fold w, trace w)) :
    Function.Injective fun w => (fold w, godelEncoding primes 0 (trace w)) := by
  intro w1 w2 hfg
  have hfold : fold w1 = fold w2 := congrArg Prod.fst hfg
  have hcode : godelEncoding primes 0 (trace w1) = godelEncoding primes 0 (trace w2) :=
    congrArg Prod.snd hfg
  have hlen : (trace w1).length = (trace w2).length := hlength w1 w2 hfold
  have hcop :
      ∀ i j, i ≠ j → Nat.Coprime (primes i) (primes j) := by
    intro i j hij
    refine (Nat.coprime_primes (hprime i) (hprime j)).2 ?_
    exact fun hp => hij (hstrict.injective hp)
  have htrace : trace w1 = trace w2 :=
    godelEncoding_injective_of_eq_length primes 0 (trace w1) (trace w2) hlen hcop
      (fun i => (hprime i).one_lt) hcode
  exact hinj (Prod.ext hfold htrace)

end Omega.Conclusion
