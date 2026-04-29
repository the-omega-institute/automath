import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete prime-register encoding data for
`thm:conclusion-prime-log-rh-operator-countable-prime-rank`.  The valuation map embeds the
multiplicative monoid into the direct sum of integer axes, while the prime enumeration marks
countably many independent rank-one axes. -/
structure conclusion_prime_log_rh_operator_countable_prime_rank_data where
  primeEnumeration : ℕ → ℕ
  primeEnumeration_prime : ∀ n : ℕ, Nat.Prime (primeEnumeration n)
  primeEnumeration_injective : Function.Injective primeEnumeration
  valuationVector : ℕ → ℕ →₀ ℤ
  decodeValuationVector : (ℕ →₀ ℤ) → ℕ
  valuationVector_left_inverse :
    ∀ n : ℕ, decodeValuationVector (valuationVector n) = n
  valuationVector_on_prime :
    ∀ n : ℕ, valuationVector (primeEnumeration n) = Finsupp.single n (1 : ℤ)

namespace conclusion_prime_log_rh_operator_countable_prime_rank_data

/-- The multiplicative monoid has a faithful valuation-vector encoding. -/
def multiplicativeMonoidIsCountableFree
    (D : conclusion_prime_log_rh_operator_countable_prime_rank_data) : Prop :=
  Function.Injective D.valuationVector

/-- The prime registers are realized on countably many independent integer axes. -/
def hasCountablyInfiniteRankImplementation
    (D : conclusion_prime_log_rh_operator_countable_prime_rank_data) : Prop :=
  (∀ n : ℕ, Nat.Prime (D.primeEnumeration n)) ∧
    Function.Injective D.primeEnumeration ∧
      ∀ n : ℕ, D.valuationVector (D.primeEnumeration n) = Finsupp.single n (1 : ℤ)

/-- A finite-rank faithful model would inject the enumerated prime axes into a finite set of
axes. -/
def hasFiniteRankFaithfulModel
    (_D : conclusion_prime_log_rh_operator_countable_prime_rank_data) : Prop :=
  ∃ N : ℕ, ∃ axis : ℕ → Fin N, Function.Injective axis

end conclusion_prime_log_rh_operator_countable_prime_rank_data

private lemma conclusion_prime_log_rh_operator_countable_prime_rank_no_nat_to_fin :
    ¬ ∃ N : ℕ, ∃ axis : ℕ → Fin N, Function.Injective axis := by
  rintro ⟨N, axis, haxis⟩
  let restrictedAxis : Fin (N + 1) → Fin N := fun i => axis i
  have hrestricted : Function.Injective restrictedAxis := by
    intro i j hij
    apply Fin.ext
    exact haxis hij
  have hcard : N + 1 ≤ N := by
    simpa using Fintype.card_le_of_injective restrictedAxis hrestricted
  omega

/-- Paper label: `thm:conclusion-prime-log-rh-operator-countable-prime-rank`. -/
theorem paper_conclusion_prime_log_rh_operator_countable_prime_rank
    (D : conclusion_prime_log_rh_operator_countable_prime_rank_data) :
    D.multiplicativeMonoidIsCountableFree ∧
      D.hasCountablyInfiniteRankImplementation ∧
        ¬ D.hasFiniteRankFaithfulModel := by
  refine ⟨?_, ?_, ?_⟩
  · intro m n hmn
    calc
      m = D.decodeValuationVector (D.valuationVector m) := by
        rw [D.valuationVector_left_inverse]
      _ = D.decodeValuationVector (D.valuationVector n) := by
        rw [hmn]
      _ = n := by
        rw [D.valuationVector_left_inverse]
  · exact ⟨D.primeEnumeration_prime, D.primeEnumeration_injective, D.valuationVector_on_prime⟩
  · exact conclusion_prime_log_rh_operator_countable_prime_rank_no_nat_to_fin

end Omega.Conclusion
