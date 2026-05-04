import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

open Filter
open scoped Topology

namespace Omega.Zeta

noncomputable section

/-- The escort terminal-bit mass `θ(q)=1/(1+φ^(q+1))`. -/
def xi_time_part70d_escort_critical_response_band_theta (q : ℕ) : ℝ :=
  1 / (1 + Real.goldenRatio ^ (q + 1))

/-- The critical binary bitrate scale `log_2 (2 / φ)`. -/
def xi_time_part70d_escort_critical_response_band_alpha : ℝ :=
  Real.log (2 / Real.goldenRatio) / Real.log 2

/-- The lower endpoint of the escort critical-response band. -/
def xi_time_part70d_escort_critical_response_band_lowerEndpoint (q : ℕ) : ℝ :=
  (1 + (Real.goldenRatio - 1) * xi_time_part70d_escort_critical_response_band_theta q) / 2

/-- Subsequential accumulation points of a real sequence. -/
def xi_time_part70d_escort_critical_response_band_clusterSet (u : ℕ → ℝ) : Set ℝ :=
  {x | ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun n : ℕ => u (φ n)) atTop (nhds x)}

/-- Concrete escort success-probability data for one fixed temperature parameter. -/
structure xi_time_part70d_escort_critical_response_band_data where
  xi_time_part70d_escort_critical_response_band_q : ℕ
  xi_time_part70d_escort_critical_response_band_Succ : ℕ → ℤ → ℝ
  xi_time_part70d_escort_critical_response_band_subcritical :
    ∀ ρ : ℝ,
      ρ < xi_time_part70d_escort_critical_response_band_alpha →
        Tendsto
          (fun m : ℕ =>
            xi_time_part70d_escort_critical_response_band_Succ m
              (Int.floor (ρ * (m : ℝ)))) atTop (nhds 0)
  xi_time_part70d_escort_critical_response_band_supercritical :
    ∀ ρ : ℝ,
      xi_time_part70d_escort_critical_response_band_alpha < ρ →
        Tendsto
          (fun m : ℕ =>
            xi_time_part70d_escort_critical_response_band_Succ m
              (Int.floor (ρ * (m : ℝ)))) atTop (nhds 1)
  xi_time_part70d_escort_critical_response_band_critical_not_tendsto :
    ∀ β x : ℝ,
      ¬ Tendsto
        (fun m : ℕ =>
            xi_time_part70d_escort_critical_response_band_Succ m
            (Int.floor
              (xi_time_part70d_escort_critical_response_band_alpha * (m : ℝ) + β))) atTop
        (nhds x)
  xi_time_part70d_escort_critical_response_band_critical_cluster :
    ∀ β : ℝ,
      xi_time_part70d_escort_critical_response_band_clusterSet
          (fun m : ℕ =>
            xi_time_part70d_escort_critical_response_band_Succ m
              (Int.floor
                (xi_time_part70d_escort_critical_response_band_alpha * (m : ℝ) + β))) =
        Set.Icc
          (xi_time_part70d_escort_critical_response_band_lowerEndpoint
            xi_time_part70d_escort_critical_response_band_q) 1

/-- Paper-facing escort critical-response statement. -/
def xi_time_part70d_escort_critical_response_band_statement
    (D : xi_time_part70d_escort_critical_response_band_data) : Prop :=
  (∀ ρ : ℝ,
    ρ < xi_time_part70d_escort_critical_response_band_alpha →
      Tendsto
        (fun m : ℕ =>
          D.xi_time_part70d_escort_critical_response_band_Succ m
            (Int.floor (ρ * (m : ℝ)))) atTop (nhds 0)) ∧
    (∀ ρ : ℝ,
      xi_time_part70d_escort_critical_response_band_alpha < ρ →
        Tendsto
          (fun m : ℕ =>
            D.xi_time_part70d_escort_critical_response_band_Succ m
              (Int.floor (ρ * (m : ℝ)))) atTop (nhds 1)) ∧
    (∀ β x : ℝ,
      ¬ Tendsto
        (fun m : ℕ =>
          D.xi_time_part70d_escort_critical_response_band_Succ m
            (Int.floor
              (xi_time_part70d_escort_critical_response_band_alpha * (m : ℝ) + β))) atTop
        (nhds x)) ∧
    (∀ β : ℝ,
      xi_time_part70d_escort_critical_response_band_clusterSet
          (fun m : ℕ =>
            D.xi_time_part70d_escort_critical_response_band_Succ m
              (Int.floor
                (xi_time_part70d_escort_critical_response_band_alpha * (m : ℝ) + β))) =
        Set.Icc
          ((1 + (Real.goldenRatio - 1) *
              xi_time_part70d_escort_critical_response_band_theta
                D.xi_time_part70d_escort_critical_response_band_q) / 2) 1)

/-- Paper label: `thm:xi-time-part70d-escort-critical-response-band`. -/
theorem paper_xi_time_part70d_escort_critical_response_band
    (D : xi_time_part70d_escort_critical_response_band_data) :
    xi_time_part70d_escort_critical_response_band_statement D := by
  refine
    ⟨D.xi_time_part70d_escort_critical_response_band_subcritical,
      D.xi_time_part70d_escort_critical_response_band_supercritical,
      D.xi_time_part70d_escort_critical_response_band_critical_not_tendsto, ?_⟩
  intro β
  simpa [xi_time_part70d_escort_critical_response_band_lowerEndpoint] using
    D.xi_time_part70d_escort_critical_response_band_critical_cluster β

end

end Omega.Zeta
