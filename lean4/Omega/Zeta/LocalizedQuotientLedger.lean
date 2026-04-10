import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The `S`-perpendicular truncation of `n`: primes in `S` collapse to `1`,
primes outside `S` remain unchanged. -/
def nSperp (S : Finset Nat) (n : Nat) : Nat :=
  if n ∈ S then 1 else n

/-- Localized quotient index ledger `I_S(n) = n_{S^\perp}`. -/
def localizedIndex (S : Finset Nat) (n : Nat) : Nat := nSperp S n

/-- Paper: `cor:xi-localized-quotient-index-prime-recovery`. -/
theorem paper_xi_localized_quotient_index_prime_recovery
    (S : Finset Nat) :
    ∀ ⦃p : Nat⦄, Nat.Prime p →
      ((p ∈ S ↔ localizedIndex S p = 1) ∧
       (p ∉ S ↔ localizedIndex S p = p)) := by
  intro p hp
  by_cases hpS : p ∈ S
  · constructor
    · simp [localizedIndex, nSperp, hpS]
    · constructor
      · intro hpnot
        exact (hpnot hpS).elim
      · intro hEq
        exfalso
        have hp_ne_one : p ≠ 1 := hp.ne_one
        exact hp_ne_one (by simpa [localizedIndex, nSperp, hpS] using hEq.symm)
  · constructor
    · constructor
      · exact fun h => (hpS h).elim
      · intro hEq
        exfalso
        exact hp.ne_one (by simpa [localizedIndex, nSperp, hpS] using hEq)
    · simp [localizedIndex, nSperp, hpS]

end Omega.Zeta
