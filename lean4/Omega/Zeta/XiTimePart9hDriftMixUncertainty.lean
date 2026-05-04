import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic

open Filter Asymptotics

namespace Omega.Zeta

noncomputable section

/-- The drift defect after converting a near-1 pole gap into mixing time. -/
def xi_time_part9h_drift_mix_uncertainty_defect
    (tau drift worstDirection : ℕ → ℝ) (m : ℕ) : ℝ :=
  tau m * drift m - worstDirection m

/-- The scaled error term left after multiplying by the inverse gap. -/
def xi_time_part9h_drift_mix_uncertainty_scaledError
    (tau error : ℕ → ℝ) (m : ℕ) : ℝ :=
  tau m * error m

/-- Paper label: `thm:xi-time-part9h-drift-mix-uncertainty`. -/
theorem paper_xi_time_part9h_drift_mix_uncertainty
    (gap tau drift worstDirection error q : ℕ → ℝ)
    (hnearOnePole :
      ∀ m, drift m = worstDirection m * gap m + error m)
    (hinverseGap : ∀ m, tau m * gap m = 1)
    (hquadraticError :
      xi_time_part9h_drift_mix_uncertainty_scaledError tau error =O[atTop] q) :
    xi_time_part9h_drift_mix_uncertainty_defect tau drift worstDirection =O[atTop] q := by
  refine hquadraticError.congr' ?_ EventuallyEq.rfl
  filter_upwards with m
  unfold xi_time_part9h_drift_mix_uncertainty_defect
    xi_time_part9h_drift_mix_uncertainty_scaledError
  rw [hnearOnePole m]
  exact (calc
    tau m * (worstDirection m * gap m + error m) - worstDirection m =
        worstDirection m * (tau m * gap m) - worstDirection m + tau m * error m := by
          ring
    _ = tau m * error m := by
          rw [hinverseGap m]
          ring).symm

end

end Omega.Zeta
