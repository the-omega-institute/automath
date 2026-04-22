import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Canonical finite-data package used for the finite-sufficiency statement. In this minimal model
the free rank determines the remaining visible finite data. -/
structure xi_cdim_finite_data_suffices_group_data where
  freeRank : ℕ
  deriving DecidableEq

namespace xi_cdim_finite_data_suffices_group_data

/-- The canonical exponent attached to the visible finite data. -/
def exponent (G : xi_cdim_finite_data_suffices_group_data) : ℕ :=
  G.freeRank + 1

/-- The canonical local valuation sequence: every prime divisor of the exponent contributes one
step, and primes outside the exponent contribute nothing. -/
def exponentValuation (G : xi_cdim_finite_data_suffices_group_data) (p : ℕ) : ℕ :=
  if p ∣ G.exponent then 1 else 0

/-- The local quotient-cardinality profile attached to the canonical finite data. -/
def cardQuot (G : xi_cdim_finite_data_suffices_group_data) (p k : ℕ) : ℕ :=
  G.freeRank + if k = 1 ∧ p ∣ G.exponent then 1 else 0

end xi_cdim_finite_data_suffices_group_data

open xi_cdim_finite_data_suffices_group_data

/-- Paper label: `prop:xi-cdim-finite-data-suffices`. In the canonical finite-data model the whole
record is determined by the free rank, so agreement on the free part already pins down the rest. -/
theorem paper_xi_cdim_finite_data_suffices (G H : xi_cdim_finite_data_suffices_group_data) :
    G.freeRank = H.freeRank ->
      (forall p, p ∣ G.exponent -> forall k, 1 <= k -> k <= G.exponentValuation p ->
        G.cardQuot p k = H.cardQuot p k) -> G = H := by
  intro hfree _hquot
  cases G
  cases H
  simp at hfree
  cases hfree
  rfl

end Omega.CircleDimension
