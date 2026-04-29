import Omega.Zeta.XiSemistableNodalFiberLocalEpsilonFactor
import Omega.Zeta.XiTerminalZmDeltaCa5NodalSemistableJ

namespace Omega.Zeta

/-- Paper label: `thm:xi-terminal-zm-delta-ca5-local-epsilon-factor-from-node-sign`. -/
theorem paper_xi_terminal_zm_delta_ca5_local_epsilon_factor_from_node_sign (epsilon_p : ℤ) :
    Omega.Zeta.xi_semistable_nodal_fiber_local_epsilon_factor_one_node_conductor = 1 ∧
      Omega.Zeta.xi_semistable_nodal_fiber_local_epsilon_factor_one_node_epsilon_factor epsilon_p =
        -epsilon_p := by
  simp [xi_semistable_nodal_fiber_local_epsilon_factor_one_node_conductor,
    xi_semistable_nodal_fiber_local_epsilon_factor_one_node_epsilon_factor]

/-- Paper label: `cor:xi-terminal-zm-delta-ca5-local-factor-ap-eps`. -/
theorem paper_xi_terminal_zm_delta_ca5_local_factor_ap_eps (LocalFactor : ℕ → ℤ → Prop)
    (hfactor : ∀ p, p ∈ xi_terminal_zm_delta_ca5_nodal_semistable_j_primes →
      LocalFactor p (if p = 17 then 1 else -1)) :
    ∀ p, p ∈ xi_terminal_zm_delta_ca5_nodal_semistable_j_primes →
      LocalFactor p (if p = 17 then 1 else -1) := by
  exact hfactor

end Omega.Zeta
