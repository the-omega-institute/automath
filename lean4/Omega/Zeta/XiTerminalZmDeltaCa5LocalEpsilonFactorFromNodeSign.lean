import Omega.Zeta.XiSemistableNodalFiberLocalEpsilonFactor

namespace Omega.Zeta

/-- Paper label: `thm:xi-terminal-zm-delta-ca5-local-epsilon-factor-from-node-sign`. -/
theorem paper_xi_terminal_zm_delta_ca5_local_epsilon_factor_from_node_sign (epsilon_p : ℤ) :
    Omega.Zeta.xi_semistable_nodal_fiber_local_epsilon_factor_one_node_conductor = 1 ∧
      Omega.Zeta.xi_semistable_nodal_fiber_local_epsilon_factor_one_node_epsilon_factor epsilon_p =
        -epsilon_p := by
  simp [xi_semistable_nodal_fiber_local_epsilon_factor_one_node_conductor,
    xi_semistable_nodal_fiber_local_epsilon_factor_one_node_epsilon_factor]

end Omega.Zeta
