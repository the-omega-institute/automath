import Omega.CircleDimension.AddressLedgerJointBudgetLowerBound

namespace Omega.Zeta

/-- The ξ-address/prime-ledger budget lower bound is exactly the existing CircleDimension
address-ledger counting argument, with the address alphabet renamed to the ξ code space.
    cor:xi-address-prime-ledger-joint-budget -/
theorem paper_xi_address_prime_ledger_joint_budget (m heavy : ℕ) {G R : Type*} [Fintype G]
    [Fintype R] (A : G → Fin (2 ^ m)) (ledger : G → R)
    (hBucket : ∃ a : Fin (2 ^ m), heavy ≤ Fintype.card {g // A g = a})
    (hInj : Function.Injective fun g => (A g, ledger g)) :
    heavy ≤ 2 ^ m * Fintype.card R := by
  exact Omega.CircleDimension.paper_cdim_address_ledger_joint_budget_lower_bound m heavy A ledger
    hBucket hInj

end Omega.Zeta
