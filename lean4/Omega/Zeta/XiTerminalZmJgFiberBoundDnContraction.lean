import Omega.Zeta.XiTerminalZmJgCriticalSquareEvenSignDefect

namespace Omega.Zeta

/-- Paper label: `cor:xi-terminal-zm-jg-fiber-bound-dn-contraction`. The `D_n`-style contraction
is exactly the final sign-packet projection from the concrete critical-square defect theorem. -/
theorem paper_xi_terminal_zm_jg_fiber_bound_dn_contraction :
    ∀ eps : xi_terminal_zm_jg_critical_square_even_sign_defect_sign_vector,
      eps ∈ xi_terminal_zm_jg_critical_square_even_sign_defect_kummer_sign_subgroup →
        eps = xi_terminal_zm_jg_critical_square_even_sign_defect_zero_sign ∨
          eps = xi_terminal_zm_jg_critical_square_even_sign_defect_full_sign := by
  intro eps h_eps
  exact (paper_xi_terminal_zm_jg_critical_square_even_sign_defect.2.2.2.2.2 eps).1 h_eps

end Omega.Zeta
