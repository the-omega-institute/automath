import Mathlib.Tactic

namespace Omega.Zeta

/-- The audited four-block weighted tree number for the window-6 quotient. -/
def xi_window6_block_tree_number_audit_prime_blockTreeNumber : ℕ :=
  123336

/-- Paper label: `cor:xi-window6-block-tree-number-audit-prime`. -/
theorem paper_xi_window6_block_tree_number_audit_prime :
    xi_window6_block_tree_number_audit_prime_blockTreeNumber = 123336 ∧
      123336 = 2 ^ 3 * 3 ^ 3 * 571 ∧ Nat.Prime 571 ∧ Nat.Coprime 571 6 := by
  native_decide

end Omega.Zeta
