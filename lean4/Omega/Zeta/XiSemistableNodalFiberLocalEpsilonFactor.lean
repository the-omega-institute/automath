import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- The one-node zeta factor in the semistable irreducible nodal fiber model. -/
def xi_semistable_nodal_fiber_local_epsilon_factor_one_node_zeta_factor
    (splittingSign : ℤ) : ℤ :=
  2 - splittingSign

/-- Each node contributes one unit to the conductor exponent in the semistable no-Swan model. -/
def xi_semistable_nodal_fiber_local_epsilon_factor_one_node_conductor : ℕ :=
  1

/-- The one-node local epsilon contribution in the same model. -/
def xi_semistable_nodal_fiber_local_epsilon_factor_one_node_epsilon_factor
    (splittingSign : ℤ) : ℤ :=
  -splittingSign

/-- Paper label: `thm:xi-semistable-nodal-fiber-local-epsilon-factor`.
For a semistable irreducible nodal fiber with `r` nodes and uniform splitting sign `σ`, the local
zeta factor is the product of the `r` identical nodal zeta contributions, the conductor exponent
is the sum of `r` one-node contributions, and the local epsilon factor is the corresponding
`r`-fold product of the identical nodal epsilon contribution. -/
theorem paper_xi_semistable_nodal_fiber_local_epsilon_factor
    (r : ℕ) (nodeSign : Fin r → ℤ) (splittingSign : ℤ)
    (hsign : ∀ i, nodeSign i = splittingSign) :
    (∏ i : Fin r,
        xi_semistable_nodal_fiber_local_epsilon_factor_one_node_zeta_factor (nodeSign i)) =
      xi_semistable_nodal_fiber_local_epsilon_factor_one_node_zeta_factor splittingSign ^ r ∧
      (∑ _ : Fin r,
          xi_semistable_nodal_fiber_local_epsilon_factor_one_node_conductor) = r ∧
      (∏ i : Fin r,
          xi_semistable_nodal_fiber_local_epsilon_factor_one_node_epsilon_factor
            (nodeSign i)) =
        xi_semistable_nodal_fiber_local_epsilon_factor_one_node_epsilon_factor splittingSign ^ r :=
    by
  refine ⟨?_, ?_, ?_⟩
  · simp [hsign]
  · simp [xi_semistable_nodal_fiber_local_epsilon_factor_one_node_conductor]
  · simp [hsign]

end Omega.Zeta
