import Mathlib.Tactic
import Omega.Zeta.LocalizedQuotientLedger

namespace Omega.Zeta

/-- Paper label:
`cor:xi-time-part69c-localized-finite-quotient-profile-recovers-primes`. -/
theorem paper_xi_time_part69c_localized_finite_quotient_profile_recovers_primes
    (S T : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) (hT : ∀ p ∈ T, Nat.Prime p) :
    ((∀ p, Nat.Prime p → Omega.Zeta.localizedIndex S p = Omega.Zeta.localizedIndex T p) ↔
        S = T) ∧
      (∀ p, Nat.Prime p → (p ∈ S ↔ Omega.Zeta.localizedIndex S p = 1)) := by
  refine ⟨?_, ?_⟩
  · constructor
    · intro hIndex
      apply Finset.ext
      intro p
      constructor
      · intro hpS
        have hp : Nat.Prime p := hS p hpS
        have hSp : localizedIndex S p = 1 :=
          (paper_xi_localized_quotient_index_prime_recovery S hp).1.1 hpS
        have hTp : localizedIndex T p = 1 := by
          simpa [hIndex p hp] using hSp
        exact (paper_xi_localized_quotient_index_prime_recovery T hp).1.2 hTp
      · intro hpT
        have hp : Nat.Prime p := hT p hpT
        have hTp : localizedIndex T p = 1 :=
          (paper_xi_localized_quotient_index_prime_recovery T hp).1.1 hpT
        have hSp : localizedIndex S p = 1 := by
          simpa [hIndex p hp] using hTp
        exact (paper_xi_localized_quotient_index_prime_recovery S hp).1.2 hSp
    · intro hST
      subst T
      intro p hp
      rfl
  · intro p hp
    exact (paper_xi_localized_quotient_index_prime_recovery S hp).1

end Omega.Zeta
