import Mathlib.Tactic
import Omega.Zeta.XiTimePart62debbFinitePrimeSupportLocalizedAxisThreshold

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part62debb-finite-localization-axes-no-full-multiplicative-host`.
The localized-axis threshold theorem identifies the exact channel budget as `a + b`, so the first
forbidden size is `a + b + 1`. -/
theorem paper_xi_time_part62debb_finite_localization_axes_no_full_multiplicative_host
    (a b : Nat) : ¬ Omega.Zeta.xiLocalizedAxisThreshold (a + b + 1) a b := by
  have hThreshold :=
    paper_xi_time_part62debb_finite_prime_support_localized_axis_threshold (a + b + 1) a b
  rw [hThreshold.2.2.2]
  omega

end Omega.Zeta
