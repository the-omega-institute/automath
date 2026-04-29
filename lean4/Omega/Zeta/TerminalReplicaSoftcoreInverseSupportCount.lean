import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete data for the terminal-replica softcore inverse-support count.

The parameter `q` fixes the Boolean coordinate set. Each Boolean row `u : Finset (Fin q)` carries
`2 ^ |u|` inverse-support choices, and the distinguished zero row contributes one extra choice. -/
structure xi_terminal_replica_softcore_inverse_support_count_data where
  q : ℕ

namespace xi_terminal_replica_softcore_inverse_support_count_data

/-- The row contribution attached to a Boolean support row. -/
def rowSupportCount (D : xi_terminal_replica_softcore_inverse_support_count_data)
    (u : Finset (Fin D.q)) : ℕ :=
  2 ^ u.card

/-- The special terminal zero row contributes one support choice. -/
def zeroRowSupportCount (_D : xi_terminal_replica_softcore_inverse_support_count_data) : ℕ :=
  1

/-- Total inverse-support count: sum all Boolean row contributions and add the special zero row. -/
def totalSupport (D : xi_terminal_replica_softcore_inverse_support_count_data) : ℕ :=
  (∑ u : Finset (Fin D.q), D.rowSupportCount u) + D.zeroRowSupportCount

end xi_terminal_replica_softcore_inverse_support_count_data

/-- Paper label: `cor:xi-terminal-replica-softcore-inverse-support-count`.

Summing the row contributions `2 ^ |u|` over all Boolean supports gives `(2 + 1) ^ q`; the
terminal zero row adds the final `+ 1`. -/
theorem paper_xi_terminal_replica_softcore_inverse_support_count
    (D : xi_terminal_replica_softcore_inverse_support_count_data) :
    D.totalSupport = 3 ^ D.q + 1 := by
  have hsum : (∑ u : Finset (Fin D.q), 2 ^ u.card) = 3 ^ D.q := by
    simpa [Fintype.card_fin] using
      Fintype.sum_pow_mul_eq_add_pow (Fin D.q) (2 : ℕ) 1
  simp [xi_terminal_replica_softcore_inverse_support_count_data.totalSupport,
    xi_terminal_replica_softcore_inverse_support_count_data.rowSupportCount,
    xi_terminal_replica_softcore_inverse_support_count_data.zeroRowSupportCount,
    hsum]

end Omega.Zeta
