import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Zeta.XiTimePart65caFrozenMaxSectorOracleCapacityLowerBound

namespace Omega.Zeta

/-- Positive part used in the critical-slope reformulation. -/
def xi_time_part65ca_frozen_max_sector_sideinfo_critical_slope_positivePart (x : ℝ) : ℝ :=
  max x 0

/-- Exponent supplied by the maximum-sector side-information lower bound. -/
noncomputable def xi_time_part65ca_frozen_max_sector_sideinfo_critical_slope_exponent
    (g alpha beta : ℝ) : ℝ :=
  g + min alpha (beta * Real.log 2) - Real.log 2

/-- Concrete data for the maximum-sector side-information critical-slope corollary. -/
structure xi_time_part65ca_frozen_max_sector_sideinfo_critical_slope_data where
  C : ℕ → ℝ
  K : ℕ → ℝ
  M : ℕ → ℝ
  P : ℕ → ℝ
  g : ℝ
  alpha : ℝ
  beta : ℝ
  entropyGap : g + alpha ≤ Real.log 2
  sectorLower :
    ∀ ε > 0, ∃ N : ℕ, ∀ m : ℕ, m ≥ N →
      Real.exp
          ((xi_time_part65ca_frozen_max_sector_sideinfo_critical_slope_exponent
                g alpha beta - ε) * (m : ℝ)) ≤
        K m * min (M m) (P m)
  capacityLower : ∀ m, K m * min (M m) (P m) ≤ C m

/-- Concrete statement for `cor:xi-time-part65ca-frozen-max-sector-sideinfo-critical-slope`. -/
def xi_time_part65ca_frozen_max_sector_sideinfo_critical_slope_statement
    (D : xi_time_part65ca_frozen_max_sector_sideinfo_critical_slope_data) : Prop :=
  let r :=
    xi_time_part65ca_frozen_max_sector_sideinfo_critical_slope_exponent
      D.g D.alpha D.beta
  (∀ ε > 0, ∃ N : ℕ, ∀ m : ℕ, m ≥ N → Real.exp ((r - ε) * (m : ℝ)) ≤ D.C m) ∧
    r =
      -xi_time_part65ca_frozen_max_sector_sideinfo_critical_slope_positivePart
        (Real.log 2 - D.g - min D.alpha (D.beta * Real.log 2)) ∧
    (Real.log 2 - D.g ≤ D.alpha →
      (Real.log 2 - D.g) / Real.log 2 < D.beta → r = 0) ∧
    (D.beta < (Real.log 2 - D.g) / Real.log 2 → r < 0) ∧
    (Real.log 2 - D.g > D.alpha → r < 0)

/-- Paper label: `cor:xi-time-part65ca-frozen-max-sector-sideinfo-critical-slope`. -/
theorem paper_xi_time_part65ca_frozen_max_sector_sideinfo_critical_slope
    (D : xi_time_part65ca_frozen_max_sector_sideinfo_critical_slope_data) :
    xi_time_part65ca_frozen_max_sector_sideinfo_critical_slope_statement D := by
  let r :=
    xi_time_part65ca_frozen_max_sector_sideinfo_critical_slope_exponent
      D.g D.alpha D.beta
  have hcapacity :
      ∀ ε > 0, ∃ N : ℕ, ∀ m : ℕ, m ≥ N → Real.exp ((r - ε) * (m : ℝ)) ≤ D.C m := by
    exact paper_xi_time_part65ca_frozen_max_sector_oracle_capacity_lower_bound
      D.C D.K D.M D.P r D.capacityLower D.sectorLower
  have hlog_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmin_le_alpha : min D.alpha (D.beta * Real.log 2) ≤ D.alpha := min_le_left _ _
  have hnonnegGap : 0 ≤ Real.log 2 - D.g - min D.alpha (D.beta * Real.log 2) := by
    have hsum :
        D.g + min D.alpha (D.beta * Real.log 2) ≤ D.g + D.alpha :=
      calc
        D.g + min D.alpha (D.beta * Real.log 2) =
            min D.alpha (D.beta * Real.log 2) + D.g := by rw [add_comm]
        _ ≤ D.alpha + D.g := add_le_add_left hmin_le_alpha D.g
        _ = D.g + D.alpha := by rw [add_comm]
    linarith [hsum, D.entropyGap]
  have hpositivePart :
      r =
        -xi_time_part65ca_frozen_max_sector_sideinfo_critical_slope_positivePart
          (Real.log 2 - D.g - min D.alpha (D.beta * Real.log 2)) := by
    rw [xi_time_part65ca_frozen_max_sector_sideinfo_critical_slope_positivePart,
      max_eq_left hnonnegGap]
    simp [r, xi_time_part65ca_frozen_max_sector_sideinfo_critical_slope_exponent]
    ring
  have hfinite :
      Real.log 2 - D.g ≤ D.alpha →
        (Real.log 2 - D.g) / Real.log 2 < D.beta → r = 0 := by
    intro hthreshold hbeta
    have hbeta_mul : Real.log 2 - D.g < D.beta * Real.log 2 := by
      have h := mul_lt_mul_of_pos_right hbeta hlog_pos
      simpa [div_mul_cancel₀ _ hlog_pos.ne'] using h
    have hle_min : Real.log 2 - D.g ≤ min D.alpha (D.beta * Real.log 2) :=
      le_min hthreshold hbeta_mul.le
    have hge : 0 ≤ r := by
      simp [r, xi_time_part65ca_frozen_max_sector_sideinfo_critical_slope_exponent]
      linarith
    have hle : r ≤ 0 := by
      simp [r, xi_time_part65ca_frozen_max_sector_sideinfo_critical_slope_exponent]
      linarith
    linarith
  have hbelow :
      D.beta < (Real.log 2 - D.g) / Real.log 2 → r < 0 := by
    intro hbeta
    have hbeta_mul : D.beta * Real.log 2 < Real.log 2 - D.g := by
      have h := mul_lt_mul_of_pos_right hbeta hlog_pos
      simpa [div_mul_cancel₀ _ hlog_pos.ne'] using h
    have hmin_le_beta : min D.alpha (D.beta * Real.log 2) ≤ D.beta * Real.log 2 :=
      min_le_right _ _
    simp [r, xi_time_part65ca_frozen_max_sector_sideinfo_critical_slope_exponent]
    linarith
  have hinfinite :
      Real.log 2 - D.g > D.alpha → r < 0 := by
    intro hgap
    simp [r, xi_time_part65ca_frozen_max_sector_sideinfo_critical_slope_exponent]
    linarith
  exact ⟨hcapacity, hpositivePart, hfinite, hbelow, hinfinite⟩

end Omega.Zeta
