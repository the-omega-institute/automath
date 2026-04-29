import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

open Filter
open scoped Topology

namespace Omega.Zeta

noncomputable section

/-- The critical binary bitrate scale `log_2 (2 / φ)`. -/
def xi_time_part70d_critical_bitrate_phase_cluster_alpha : ℝ :=
  Real.log (2 / Real.goldenRatio) / Real.log 2

/-- The lower endpoint of the critical-window accumulation interval. -/
def xi_time_part70d_critical_bitrate_phase_cluster_lowerEndpoint : ℝ :=
  Real.goldenRatio ^ 2 / (2 * Real.sqrt 5)

/-- Subsequential accumulation points of a real sequence. -/
def xi_time_part70d_critical_bitrate_phase_cluster_clusterSet (u : ℕ → ℝ) : Set ℝ :=
  {x | ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun n : ℕ => u (φ n)) atTop (nhds x)}

/-- Concrete success-probability data for the terminal-sheet critical bitrate phase cluster. -/
structure xi_time_part70d_critical_bitrate_phase_cluster_Data where
  xi_time_part70d_critical_bitrate_phase_cluster_Succ : ℕ → ℤ → ℝ
  xi_time_part70d_critical_bitrate_phase_cluster_subcritical :
    ∀ ρ : ℝ,
      ρ < xi_time_part70d_critical_bitrate_phase_cluster_alpha →
        Tendsto
          (fun m : ℕ =>
            xi_time_part70d_critical_bitrate_phase_cluster_Succ m
              (Int.floor (ρ * (m : ℝ)))) atTop (nhds 0)
  xi_time_part70d_critical_bitrate_phase_cluster_supercritical :
    ∀ ρ : ℝ,
      xi_time_part70d_critical_bitrate_phase_cluster_alpha < ρ →
        Tendsto
          (fun m : ℕ =>
            xi_time_part70d_critical_bitrate_phase_cluster_Succ m
              (Int.floor (ρ * (m : ℝ)))) atTop (nhds 1)
  xi_time_part70d_critical_bitrate_phase_cluster_critical_not_tendsto :
    ∀ β x : ℝ,
      ¬ Tendsto
        (fun m : ℕ =>
          xi_time_part70d_critical_bitrate_phase_cluster_Succ m
            (Int.floor
              (xi_time_part70d_critical_bitrate_phase_cluster_alpha * (m : ℝ) + β))) atTop
        (nhds x)
  xi_time_part70d_critical_bitrate_phase_cluster_critical_cluster :
    ∀ β : ℝ,
      xi_time_part70d_critical_bitrate_phase_cluster_clusterSet
          (fun m : ℕ =>
            xi_time_part70d_critical_bitrate_phase_cluster_Succ m
              (Int.floor
                (xi_time_part70d_critical_bitrate_phase_cluster_alpha * (m : ℝ) + β))) =
        Set.Icc xi_time_part70d_critical_bitrate_phase_cluster_lowerEndpoint 1

/-- Paper-facing statement of the subcritical, supercritical, and critical-window laws. -/
def xi_time_part70d_critical_bitrate_phase_cluster_Statement
    (D : xi_time_part70d_critical_bitrate_phase_cluster_Data) : Prop :=
  (∀ ρ : ℝ,
    ρ < xi_time_part70d_critical_bitrate_phase_cluster_alpha →
      Tendsto
        (fun m : ℕ =>
          D.xi_time_part70d_critical_bitrate_phase_cluster_Succ m
            (Int.floor (ρ * (m : ℝ)))) atTop (nhds 0)) ∧
    (∀ ρ : ℝ,
      xi_time_part70d_critical_bitrate_phase_cluster_alpha < ρ →
        Tendsto
          (fun m : ℕ =>
            D.xi_time_part70d_critical_bitrate_phase_cluster_Succ m
              (Int.floor (ρ * (m : ℝ)))) atTop (nhds 1)) ∧
    (∀ β x : ℝ,
      ¬ Tendsto
        (fun m : ℕ =>
          D.xi_time_part70d_critical_bitrate_phase_cluster_Succ m
            (Int.floor
              (xi_time_part70d_critical_bitrate_phase_cluster_alpha * (m : ℝ) + β))) atTop
        (nhds x)) ∧
    (∀ β : ℝ,
      xi_time_part70d_critical_bitrate_phase_cluster_clusterSet
          (fun m : ℕ =>
            D.xi_time_part70d_critical_bitrate_phase_cluster_Succ m
              (Int.floor
                (xi_time_part70d_critical_bitrate_phase_cluster_alpha * (m : ℝ) + β))) =
        Set.Icc xi_time_part70d_critical_bitrate_phase_cluster_lowerEndpoint 1)

/-- Paper label: `thm:xi-time-part70d-critical-bitrate-phase-cluster`. -/
theorem paper_xi_time_part70d_critical_bitrate_phase_cluster
    (D : xi_time_part70d_critical_bitrate_phase_cluster_Data) :
    xi_time_part70d_critical_bitrate_phase_cluster_Statement D := by
  exact
    ⟨D.xi_time_part70d_critical_bitrate_phase_cluster_subcritical,
      D.xi_time_part70d_critical_bitrate_phase_cluster_supercritical,
      D.xi_time_part70d_critical_bitrate_phase_cluster_critical_not_tendsto,
      D.xi_time_part70d_critical_bitrate_phase_cluster_critical_cluster⟩

end

end Omega.Zeta
