import Mathlib.Data.Real.Basic

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part60ab2-logcm-shift-even-zeta`. Substituting the recovered
modal coefficient from the shift projector into the even-zeta coefficient formula gives the
projector-limit form. -/
theorem paper_xi_time_part60ab2_logcm_shift_even_zeta
    (zetaEven prefactor modalCoeff projectorLimit : ℝ)
    (hprojector : projectorLimit = modalCoeff)
    (hzeta : zetaEven = prefactor * modalCoeff) :
    zetaEven = prefactor * projectorLimit := by
  rw [hzeta, hprojector]

end Omega.Zeta
