import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic

open Filter Asymptotics

namespace Omega.Zeta

noncomputable section

/-- Spectral-tax product defect after multiplying the drift--mix uncertainty by `log |G_m|`. -/
def xi_time_part9h_spectral_tax_drift_product_defect
    (logGroup tau drift worstDirection : ℕ → ℝ) (m : ℕ) : ℝ :=
  logGroup m * (tau m * drift m) - logGroup m * worstDirection m

/-- Paper label: `cor:xi-time-part9h-spectral-tax-drift-product`. -/
theorem paper_xi_time_part9h_spectral_tax_drift_product
    (gap tau drift worstDirection error q logGroup : ℕ → ℝ)
    (hnearOnePole :
      ∀ m, drift m = worstDirection m * gap m + error m)
    (hinverseGap : ∀ m, tau m * gap m = 1)
    (hquadraticError : (fun m => tau m * error m) =O[atTop] q) :
    xi_time_part9h_spectral_tax_drift_product_defect logGroup tau drift worstDirection =O[atTop]
      fun m => logGroup m * q m := by
  have hproduct :
      (fun m => logGroup m * (tau m * error m)) =O[atTop]
        fun m => logGroup m * q m :=
    (isBigO_refl logGroup atTop).mul hquadraticError
  refine hproduct.congr' ?_ EventuallyEq.rfl
  filter_upwards with m
  unfold xi_time_part9h_spectral_tax_drift_product_defect
  rw [hnearOnePole m]
  calc
    logGroup m * (tau m * error m) =
        logGroup m * (tau m * (worstDirection m * gap m + error m)) -
          logGroup m * worstDirection m := by
          rw [show tau m * (worstDirection m * gap m + error m) =
              worstDirection m + tau m * error m by
            calc
              tau m * (worstDirection m * gap m + error m) =
                  worstDirection m * (tau m * gap m) + tau m * error m := by
                    ring
              _ = worstDirection m + tau m * error m := by
                    rw [hinverseGap m]
                    ring]
          ring
    _ = logGroup m * (tau m * (worstDirection m * gap m + error m)) -
          logGroup m * worstDirection m := rfl

end

end Omega.Zeta
