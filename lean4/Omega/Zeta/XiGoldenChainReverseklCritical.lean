import Omega.Zeta.XiReverseKLCriticalRigidityHaar

namespace Omega.Zeta

/-- Paper label: `cor:xi-golden-chain-reversekl-critical`. -/
theorem paper_xi_golden_chain_reversekl_critical
    (D : xi_reversekl_critical_rigidity_haar_data) :
    xi_reversekl_critical_rigidity_haar_statement D := by
  exact paper_xi_reversekl_critical_rigidity_haar D

end Omega.Zeta
