import Omega.Conclusion.PrimeRegister

namespace Omega.Conclusion

/-- Arithmetic prefix criterion obtained by restricting the Gödel code of `v` to the first
`u.length` coordinates.
    thm:conclusion-godel-prefix-arithmetic-criterion -/
theorem paper_conclusion_godel_prefix_arithmetic_criterion (primes : Nat → Nat) (u v : List Nat)
    (hcop : ∀ i j, i ≠ j → Nat.Coprime (primes i) (primes j)) (hp : ∀ i, 1 < primes i) :
    (∃ w, v = u ++ w) ↔
      u.length ≤ v.length ∧ godelEncoding primes 0 (v.take u.length) = godelEncoding primes 0 u := by
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨by simp, ?_⟩
    simpa using
      congrArg (godelEncoding primes 0) (show (u ++ w).take u.length = u from List.take_left)
  · rintro ⟨hlen, henc⟩
    have htake_len : (v.take u.length).length = u.length := by
      simp [List.length_take, Nat.min_eq_left hlen]
    have htake : v.take u.length = u := by
      exact godelEncoding_injective_of_eq_length primes 0 (v.take u.length) u htake_len hcop hp henc
    refine ⟨v.drop u.length, ?_⟩
    calc
      v = v.take u.length ++ v.drop u.length := by
        exact (List.take_append_drop u.length v).symm
      _ = u ++ v.drop u.length := by rw [htake]

end Omega.Conclusion
