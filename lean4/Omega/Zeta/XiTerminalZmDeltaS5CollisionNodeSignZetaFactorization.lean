import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- The number `n_{H,p}` of nodes over the `H`-quotient in the terminal `S₅` collision package. -/
def xi_terminal_zm_delta_s5_collision_node_sign_zeta_factorization_node_count
    (stabilizerOrder : ℕ) : ℕ :=
  60 / stabilizerOrder

/-- The one-node normalization factor attached to a fixed splitting sign. -/
def xi_terminal_zm_delta_s5_collision_node_sign_zeta_factorization_one_node_factor
    (splittingSign : ℤ) : ℤ :=
  1 - splittingSign

/-- The total correction factor obtained by multiplying the one-node factor over all
`n_{H,p}` nodes. -/
def xi_terminal_zm_delta_s5_collision_node_sign_zeta_factorization_total_factor
    (stabilizerOrder : ℕ) (splittingSign : ℤ) : ℤ :=
  ∏ _ : Fin (xi_terminal_zm_delta_s5_collision_node_sign_zeta_factorization_node_count
      stabilizerOrder),
    xi_terminal_zm_delta_s5_collision_node_sign_zeta_factorization_one_node_factor splittingSign

/-- Paper label: `thm:xi-terminal-zm-delta-s5-collision-node-sign-zeta-factorization`.
If the unique node on the `A₅` quotient has splitting sign `σ`, and every lifted / quotient node
over the `H`-quotient inherits the same sign, then the total zeta-factor correction is the
`n_{H,p}`-fold product of the identical one-node normalization factor. -/
theorem paper_xi_terminal_zm_delta_s5_collision_node_sign_zeta_factorization
    (stabilizerOrder : ℕ) (splittingSign : ℤ)
    (liftedNodeSign :
      Fin (xi_terminal_zm_delta_s5_collision_node_sign_zeta_factorization_node_count
        stabilizerOrder) → ℤ)
    (quotientNodeSign :
      Fin (xi_terminal_zm_delta_s5_collision_node_sign_zeta_factorization_node_count
        stabilizerOrder) → ℤ)
    (hlift : ∀ i, liftedNodeSign i = splittingSign)
    (hquot : ∀ i, quotientNodeSign i = splittingSign) :
    (∀ i, liftedNodeSign i = splittingSign) ∧
      (∀ i, quotientNodeSign i = splittingSign) ∧
      xi_terminal_zm_delta_s5_collision_node_sign_zeta_factorization_total_factor
          stabilizerOrder splittingSign =
        xi_terminal_zm_delta_s5_collision_node_sign_zeta_factorization_one_node_factor
            splittingSign ^
          xi_terminal_zm_delta_s5_collision_node_sign_zeta_factorization_node_count
            stabilizerOrder := by
  refine ⟨hlift, hquot, ?_⟩
  simp [xi_terminal_zm_delta_s5_collision_node_sign_zeta_factorization_total_factor]

end Omega.Zeta
