import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- The total contribution of the ten node preimages, grouped into the two branches above the five
finite nodes. -/
def xi_terminal_zm_delta_node_preimage_sum_zero_total {E : Type*} [AddCommGroup E]
    (left right : Fin 5 → E) : E :=
  (∑ i, left i) + ∑ i, right i

/-- Paper label: `thm:xi-terminal-zm-delta-node-preimage-sum-zero`.  If the pullback divisor pairs
the two branches above each finite node as additive inverses, then the full ten-point sum is zero
in the elliptic-curve group law. -/
theorem paper_xi_terminal_zm_delta_node_preimage_sum_zero {E : Type*} [AddCommGroup E]
    (left right : Fin 5 → E) (hpair : ∀ i, right i = -left i) :
    xi_terminal_zm_delta_node_preimage_sum_zero_total left right = 0 := by
  unfold xi_terminal_zm_delta_node_preimage_sum_zero_total
  calc
    (∑ i, left i) + ∑ i, right i = ∑ i, (left i + right i) := by
      rw [← Finset.sum_add_distrib]
    _ = ∑ i : Fin 5, (0 : E) := by
      simp [hpair]
    _ = 0 := by
      simp

end Omega.Zeta
