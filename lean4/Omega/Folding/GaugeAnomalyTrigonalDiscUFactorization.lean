import Mathlib.Tactic

namespace Omega.Folding

/-- Paper: `prop:fold-gauge-anomaly-trigonal-disc-u-factorization`. -/
theorem paper_fold_gauge_anomaly_trigonal_disc_u_factorization (mu : ℚ) :
    -mu * (32 * (mu ^ 2 - mu - 1) + 27 * mu ^ 5) * (mu ^ 2 - mu - 1) ^ 2 =
      -mu * (3 * mu + 2) * (mu ^ 2 - mu - 1) ^ 2 *
        (9 * mu ^ 4 - 6 * mu ^ 3 + 4 * mu ^ 2 + 8 * mu - 16) := by
  have hfactor :
      32 * (mu ^ 2 - mu - 1) + 27 * mu ^ 5 =
        (3 * mu + 2) * (9 * mu ^ 4 - 6 * mu ^ 3 + 4 * mu ^ 2 + 8 * mu - 16) := by
    ring
  rw [hfactor]
  ring

end Omega.Folding
