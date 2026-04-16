import Mathlib.Tactic
import Omega.CircleDimension.PrefixResidualRegisterCapacity

namespace Omega.CircleDimension

/-- Paper-facing wrapper for the address/ledger joint-budget lower bound.
    A heavy address bucket forces enough distinct ledger labels inside that bucket, so the combined
    address-plus-ledger budget is at least the heavy bucket size.
    thm:cdim-address-ledger-joint-budget-lower-bound -/
theorem paper_cdim_address_ledger_joint_budget_lower_bound
    (b heavy : ℕ) {Γ R : Type*} [Fintype Γ] [Fintype R] (A : Γ → Fin (2 ^ b)) (r : Γ → R)
    (hBucket : ∃ a : Fin (2 ^ b), heavy ≤ Fintype.card {γ // A γ = a})
    (hInj : Function.Injective fun γ => (A γ, r γ)) :
    heavy ≤ 2 ^ b * Fintype.card R := by
  rcases hBucket with ⟨a, hHeavy⟩
  have hLedger : heavy ≤ Fintype.card R :=
    paper_cdim_prefix_residual_register_capacity b heavy A r a hInj hHeavy
  have hPow : 1 ≤ 2 ^ b := by
    exact Nat.succ_le_of_lt (pow_pos (show 0 < (2 : ℕ) by decide) b)
  calc
    heavy ≤ Fintype.card R := hLedger
    _ = 1 * Fintype.card R := by simp
    _ ≤ 2 ^ b * Fintype.card R := Nat.mul_le_mul_right (Fintype.card R) hPow

end Omega.CircleDimension
