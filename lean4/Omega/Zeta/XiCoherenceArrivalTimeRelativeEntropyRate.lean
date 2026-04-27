import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

open Filter
open scoped Topology

namespace Omega.Zeta

noncomputable section

/-- The exponential posterior error envelope supplied by a relative-entropy-rate gap. -/
def xi_coherence_arrival_time_relative_entropy_rate_posterior_error
    (Dstar t : ℝ) : ℝ :=
  Real.exp (-(Dstar * t))

/-- Posterior mass of the true concept in the exact exponential envelope model. -/
def xi_coherence_arrival_time_relative_entropy_rate_posterior_mass
    (Dstar t : ℝ) : ℝ :=
  1 - xi_coherence_arrival_time_relative_entropy_rate_posterior_error Dstar t

/-- Real-valued threshold arrival time for posterior error level `ε`. -/
def xi_coherence_arrival_time_relative_entropy_rate_threshold_arrival
    (Dstar ε : ℝ) : ℝ :=
  Real.log (1 / ε) / Dstar

/-- The same arrival time with the true-concept prior penalty retained in the numerator. -/
def xi_coherence_arrival_time_relative_entropy_rate_prior_penalty_arrival
    (Dstar wTrue ε : ℝ) : ℝ :=
  (Real.log (1 / ε) + Real.log (1 / wTrue)) / Dstar

/-- The concrete conclusion records the posterior exponential law, the threshold-time law, and
the prior-penalty refinement along the standard thresholds `ε_k = exp (-(k+1))`. -/
def xi_coherence_arrival_time_relative_entropy_rate_conclusion
    (Dstar wTrue : ℝ) : Prop :=
  Tendsto
      (fun n : ℕ =>
        -Real.log
            (xi_coherence_arrival_time_relative_entropy_rate_posterior_error Dstar
              (((n + 1 : ℕ) : ℝ))) /
          (((n + 1 : ℕ) : ℝ)))
      atTop (nhds Dstar) ∧
    Tendsto
      (fun k : ℕ =>
        xi_coherence_arrival_time_relative_entropy_rate_threshold_arrival Dstar
            (Real.exp (-(((k + 1 : ℕ) : ℝ)))) /
          Real.log (1 / Real.exp (-(((k + 1 : ℕ) : ℝ)))))
      atTop (nhds (1 / Dstar)) ∧
      Tendsto
        (fun k : ℕ =>
          xi_coherence_arrival_time_relative_entropy_rate_prior_penalty_arrival Dstar wTrue
              (Real.exp (-(((k + 1 : ℕ) : ℝ)))) /
            (Real.log (1 / Real.exp (-(((k + 1 : ℕ) : ℝ)))) + Real.log (1 / wTrue)))
        atTop (nhds (1 / Dstar))

lemma xi_coherence_arrival_time_relative_entropy_rate_error_log_slope
    (Dstar : ℝ) (n : ℕ) :
    -Real.log
        (xi_coherence_arrival_time_relative_entropy_rate_posterior_error Dstar
          (((n + 1 : ℕ) : ℝ))) /
      (((n + 1 : ℕ) : ℝ)) = Dstar := by
  have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  simp [xi_coherence_arrival_time_relative_entropy_rate_posterior_error]
  field_simp [hn]

lemma xi_coherence_arrival_time_relative_entropy_rate_threshold_ratio
    {Dstar : ℝ} (hDstar : Dstar ≠ 0) (k : ℕ) :
    xi_coherence_arrival_time_relative_entropy_rate_threshold_arrival Dstar
        (Real.exp (-(((k + 1 : ℕ) : ℝ)))) /
      Real.log (1 / Real.exp (-(((k + 1 : ℕ) : ℝ)))) = 1 / Dstar := by
  have hk : (((k + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  simp [xi_coherence_arrival_time_relative_entropy_rate_threshold_arrival]
  field_simp [hDstar, hk]

lemma xi_coherence_arrival_time_relative_entropy_rate_prior_penalty_ratio
    {Dstar wTrue : ℝ} (hDstar : Dstar ≠ 0) (hwTrue_pos : 0 < wTrue)
    (hwTrue_le_one : wTrue ≤ 1) (k : ℕ) :
    xi_coherence_arrival_time_relative_entropy_rate_prior_penalty_arrival Dstar wTrue
        (Real.exp (-(((k + 1 : ℕ) : ℝ)))) /
      (Real.log (1 / Real.exp (-(((k + 1 : ℕ) : ℝ)))) + Real.log (1 / wTrue)) =
        1 / Dstar := by
  have hone_le_inv : 1 ≤ 1 / wTrue := by
    field_simp [ne_of_gt hwTrue_pos]
    exact hwTrue_le_one
  have hlog_nonneg : 0 ≤ Real.log (1 / wTrue) := Real.log_nonneg hone_le_inv
  have hnum :
      Real.log (1 / Real.exp (-(((k + 1 : ℕ) : ℝ)))) + Real.log (1 / wTrue) ≠ 0 := by
    have hk_pos : 0 < (((k + 1 : ℕ) : ℝ)) := by positivity
    have hlog_eps :
        Real.log (1 / Real.exp (-(((k + 1 : ℕ) : ℝ)))) = (((k + 1 : ℕ) : ℝ)) := by
      simp
    have hpos :
        0 <
          Real.log (1 / Real.exp (-(((k + 1 : ℕ) : ℝ)))) + Real.log (1 / wTrue) := by
      rw [hlog_eps]
      linarith
    exact ne_of_gt hpos
  rw [xi_coherence_arrival_time_relative_entropy_rate_prior_penalty_arrival]
  field_simp [hDstar, hnum]

/-- Paper label: `thm:xi-coherence-arrival-time-relative-entropy-rate`. -/
theorem paper_xi_coherence_arrival_time_relative_entropy_rate
    (Dstar wTrue : ℝ) (hDstar : 0 < Dstar) (hwTrue : 0 < wTrue)
    (hwTrue_le_one : wTrue ≤ 1) :
    xi_coherence_arrival_time_relative_entropy_rate_conclusion Dstar wTrue := by
  refine ⟨?_, ?_, ?_⟩
  · apply tendsto_const_nhds.congr'
    filter_upwards with n
    exact (xi_coherence_arrival_time_relative_entropy_rate_error_log_slope Dstar n).symm
  · apply tendsto_const_nhds.congr'
    filter_upwards with k
    exact (xi_coherence_arrival_time_relative_entropy_rate_threshold_ratio
      (ne_of_gt hDstar) k).symm
  · apply tendsto_const_nhds.congr'
    filter_upwards with k
    exact (xi_coherence_arrival_time_relative_entropy_rate_prior_penalty_ratio
      (ne_of_gt hDstar) hwTrue hwTrue_le_one k).symm

end

end Omega.Zeta
