import Mathlib.Tactic
import Omega.Zeta.XiTimePart50cbMirrorBranchEvenOddPowerSumSuppression

namespace Omega.Zeta

open Filter

/-- Concrete data for the mesoscopic period-two interference statement.  The discrete parameter
indexes the zero-temperature limit; the power-sum limit is forced by the two-branch identity and
the mirror-branch parity limit. -/
structure xi_time_part50cb_mesoscopic_period2_interference_data where
  xi_time_part50cb_mesoscopic_period2_interference_length : ℕ → ℕ
  xi_time_part50cb_mesoscopic_period2_interference_mainBranch : ℕ → ℝ
  xi_time_part50cb_mesoscopic_period2_interference_mirrorBranch : ℕ → ℝ
  xi_time_part50cb_mesoscopic_period2_interference_powerSum : ℕ → ℝ
  xi_time_part50cb_mesoscopic_period2_interference_mesoscopicGrowth :
    ∀ t : ℕ, 1 ≤ xi_time_part50cb_mesoscopic_period2_interference_length t
  xi_time_part50cb_mesoscopic_period2_interference_powerSum_identity :
    ∀ t : ℕ,
      xi_time_part50cb_mesoscopic_period2_interference_powerSum t /
          xi_time_part50cb_mesoscopic_period2_interference_mainBranch t ^
            xi_time_part50cb_mesoscopic_period2_interference_length t =
        1 +
          xi_time_part50cb_mesoscopic_period2_interference_mirrorBranch t ^
              xi_time_part50cb_mesoscopic_period2_interference_length t /
            xi_time_part50cb_mesoscopic_period2_interference_mainBranch t ^
              xi_time_part50cb_mesoscopic_period2_interference_length t
  xi_time_part50cb_mesoscopic_period2_interference_mirrorBranch_limit :
    Tendsto
      (fun t : ℕ =>
        xi_time_part50cb_mesoscopic_period2_interference_mirrorBranch t ^
              xi_time_part50cb_mesoscopic_period2_interference_length t /
            xi_time_part50cb_mesoscopic_period2_interference_mainBranch t ^
              xi_time_part50cb_mesoscopic_period2_interference_length t -
          (-1 : ℝ) ^ xi_time_part50cb_mesoscopic_period2_interference_length t)
      atTop (nhds 0)

namespace xi_time_part50cb_mesoscopic_period2_interference_data

/-- The normalized mirror branch converges to the parity character on the mesoscopic window. -/
def xi_time_part50cb_mesoscopic_period2_interference_mirror_branch_parity_limit
    (D : xi_time_part50cb_mesoscopic_period2_interference_data) : Prop :=
  Tendsto
    (fun t : ℕ =>
      D.xi_time_part50cb_mesoscopic_period2_interference_mirrorBranch t ^
            D.xi_time_part50cb_mesoscopic_period2_interference_length t /
          D.xi_time_part50cb_mesoscopic_period2_interference_mainBranch t ^
            D.xi_time_part50cb_mesoscopic_period2_interference_length t -
        (-1 : ℝ) ^ D.xi_time_part50cb_mesoscopic_period2_interference_length t)
    atTop (nhds 0)

/-- The normalized total power sum inherits the same period-two interference limit. -/
def xi_time_part50cb_mesoscopic_period2_interference_power_sum_limit
    (D : xi_time_part50cb_mesoscopic_period2_interference_data) : Prop :=
  Tendsto
    (fun t : ℕ =>
      D.xi_time_part50cb_mesoscopic_period2_interference_powerSum t /
            D.xi_time_part50cb_mesoscopic_period2_interference_mainBranch t ^
              D.xi_time_part50cb_mesoscopic_period2_interference_length t -
          (1 + (-1 : ℝ) ^ D.xi_time_part50cb_mesoscopic_period2_interference_length t))
    atTop (nhds 0)

end xi_time_part50cb_mesoscopic_period2_interference_data

/-- Paper label: `cor:xi-time-part50cb-mesoscopic-period2-interference`. -/
theorem paper_xi_time_part50cb_mesoscopic_period2_interference
    (D : xi_time_part50cb_mesoscopic_period2_interference_data) :
    D.xi_time_part50cb_mesoscopic_period2_interference_mirror_branch_parity_limit ∧
      D.xi_time_part50cb_mesoscopic_period2_interference_power_sum_limit := by
  refine ⟨D.xi_time_part50cb_mesoscopic_period2_interference_mirrorBranch_limit, ?_⟩
  have hfun :
      (fun t : ℕ =>
        D.xi_time_part50cb_mesoscopic_period2_interference_powerSum t /
              D.xi_time_part50cb_mesoscopic_period2_interference_mainBranch t ^
                D.xi_time_part50cb_mesoscopic_period2_interference_length t -
            (1 + (-1 : ℝ) ^ D.xi_time_part50cb_mesoscopic_period2_interference_length t)) =
        fun t : ℕ =>
          D.xi_time_part50cb_mesoscopic_period2_interference_mirrorBranch t ^
                D.xi_time_part50cb_mesoscopic_period2_interference_length t /
              D.xi_time_part50cb_mesoscopic_period2_interference_mainBranch t ^
                D.xi_time_part50cb_mesoscopic_period2_interference_length t -
            (-1 : ℝ) ^ D.xi_time_part50cb_mesoscopic_period2_interference_length t := by
    funext t
    rw [D.xi_time_part50cb_mesoscopic_period2_interference_powerSum_identity t]
    ring
  change Tendsto
    (fun t : ℕ =>
      D.xi_time_part50cb_mesoscopic_period2_interference_powerSum t /
            D.xi_time_part50cb_mesoscopic_period2_interference_mainBranch t ^
              D.xi_time_part50cb_mesoscopic_period2_interference_length t -
          (1 + (-1 : ℝ) ^ D.xi_time_part50cb_mesoscopic_period2_interference_length t))
    atTop (nhds 0)
  rw [hfun]
  exact D.xi_time_part50cb_mesoscopic_period2_interference_mirrorBranch_limit

end Omega.Zeta
