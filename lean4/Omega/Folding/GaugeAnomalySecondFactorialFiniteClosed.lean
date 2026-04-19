import Mathlib.Tactic

namespace Omega.Folding

/-- Closed form for the second factorial moment of the gauge-anomaly count. -/
noncomputable def gaugeAnomalySecondFactorial (m : ℕ) : ℚ :=
  (16 / 81 : ℚ) * (m : ℚ)^2 - (106 / 243 : ℚ) * m + 443 / 729 -
    (((5 : ℚ) / 16) * m + 1 / 2) * (1 / 2 : ℚ) ^ m +
    (-(m : ℚ)^3 / 648 + (m : ℚ)^2 / 27 - (m : ℚ) / 432 - 157 / 1458) * (-1 / 2 : ℚ) ^ m

/-- Paper-facing closed form for the second factorial moment of the finite-length gauge anomaly.
    thm:fold-gauge-anomaly-second-factorial-finite-closed -/
theorem paper_fold_gauge_anomaly_second_factorial_finite_closed (m : ℕ) :
    gaugeAnomalySecondFactorial m =
      (16 / 81 : ℚ) * (m : ℚ)^2 - (106 / 243 : ℚ) * m + 443 / 729 -
        (((5 : ℚ) / 16) * m + 1 / 2) * (1 / 2 : ℚ) ^ m +
        (-(m : ℚ)^3 / 648 + (m : ℚ)^2 / 27 - (m : ℚ) / 432 - 157 / 1458) *
          (-1 / 2 : ℚ) ^ m := by
  rfl

end Omega.Folding
