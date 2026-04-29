import Omega.Zeta.XiTerminalBelyiPuiseuxScaling
import Omega.Zeta.XiTerminalBelyiDiscriminantClosedForm
import Omega.Zeta.XiTerminalBelyiFullSymmetricCover

namespace Omega.Zeta

/-- Paper label: `cor:xi-terminal-belyi-adjustable-exponent-maximal-galois`. -/
theorem paper_xi_terminal_belyi_adjustable_exponent_maximal_galois (r : Nat) (hr : 2 ≤ r) :
    xi_terminal_belyi_puiseux_scaling_statement r ∧
      xi_terminal_belyi_discriminant_closed_form_statement r ∧
      xi_terminal_belyi_full_symmetric_cover_statement r := by
  exact ⟨paper_xi_terminal_belyi_puiseux_scaling r hr,
    paper_xi_terminal_belyi_discriminant_closed_form r hr,
    paper_xi_terminal_belyi_full_symmetric_cover r hr⟩

end Omega.Zeta
