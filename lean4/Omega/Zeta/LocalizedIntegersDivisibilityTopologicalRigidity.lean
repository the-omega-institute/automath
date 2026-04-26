import Mathlib.Tactic
import Omega.Zeta.LocalizedQuotientLedger

namespace Omega.Zeta

/-- Paper label: `thm:xi-localized-integers-divisibility-topological-rigidity`. -/
theorem paper_xi_localized_integers_divisibility_topological_rigidity (S T : Finset Nat)
    (hS : ∀ p, p ∈ S → Nat.Prime p) (hT : ∀ p, p ∈ T → Nat.Prime p) :
    (∀ p : Nat, Nat.Prime p → (localizedIndex S p = 1 ↔ p ∈ S)) ∧
      ((∀ p : Nat, Nat.Prime p → (localizedIndex S p = 1 ↔ localizedIndex T p = 1)) ↔
        S = T) := by
  refine ⟨?_, ?_⟩
  · intro p hp
    exact (paper_xi_localized_quotient_index_prime_recovery S hp).1.symm
  · constructor
    · intro hIndex
      apply Finset.ext
      intro p
      constructor
      · intro hpS
        have hp : Nat.Prime p := hS p hpS
        have hSindex : localizedIndex S p = 1 :=
          (paper_xi_localized_quotient_index_prime_recovery S hp).1.1 hpS
        have hTindex : localizedIndex T p = 1 := (hIndex p hp).1 hSindex
        exact (paper_xi_localized_quotient_index_prime_recovery T hp).1.2 hTindex
      · intro hpT
        have hp : Nat.Prime p := hT p hpT
        have hTindex : localizedIndex T p = 1 :=
          (paper_xi_localized_quotient_index_prime_recovery T hp).1.1 hpT
        have hSindex : localizedIndex S p = 1 := (hIndex p hp).2 hTindex
        exact (paper_xi_localized_quotient_index_prime_recovery S hp).1.2 hSindex
    · intro hST
      subst T
      intro p hp
      rfl

end Omega.Zeta
