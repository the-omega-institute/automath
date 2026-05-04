import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete data for the two-concept coherence-time law.  The `density_eventual` field is the
liminf consequence after choosing `eta < density`; `threshold_eventual` is the resulting linear
posterior threshold, and `coherence_upper` encodes minimality of the coherence time. -/
structure xi_two_concept_coherence_time_density_law_data where
  beta : ℝ
  epsilon : ℝ
  density : ℝ
  eta : ℝ
  descriptionGap : ℝ
  threshold : ℝ
  E1 : ℕ → ℝ
  posterior0 : ℕ → ℝ
  coherenceTime : ℕ
  beta_pos : 0 < beta
  density_eventual_N : ℕ
  threshold_eventual_N : ℕ
  density_eventual :
    ∀ n : ℕ, density_eventual_N ≤ n → (density - eta) * (n : ℝ) ≤ E1 n
  threshold_eventual :
    ∀ n : ℕ, threshold_eventual_N ≤ n →
      threshold ≤ beta * ((density - eta) * (n : ℝ)) + descriptionGap
  posterior_threshold :
    ∀ n : ℕ, threshold ≤ beta * E1 n + descriptionGap → 1 - epsilon ≤ posterior0 n
  coherence_upper :
    ∀ n : ℕ, 1 ≤ n → 1 - epsilon ≤ posterior0 n → coherenceTime ≤ n

/-- Once both eventual estimates are active, the posterior is above the target level and the
minimal coherence time is bounded by the same index. -/
def xi_two_concept_coherence_time_density_law_statement
    (D : xi_two_concept_coherence_time_density_law_data) : Prop :=
  ∀ n : ℕ, Nat.max (Nat.max D.density_eventual_N D.threshold_eventual_N) 1 ≤ n →
    1 - D.epsilon ≤ D.posterior0 n ∧ D.coherenceTime ≤ n

/-- Paper label: `cor:xi-two-concept-coherence-time-density-law`. -/
theorem paper_xi_two_concept_coherence_time_density_law
    (D : xi_two_concept_coherence_time_density_law_data) :
    xi_two_concept_coherence_time_density_law_statement D := by
  intro n hn
  have hdensity_N : D.density_eventual_N ≤ n := by
    exact le_trans (le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hn
  have hthreshold_N : D.threshold_eventual_N ≤ n := by
    exact le_trans (le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hn
  have hn_pos : 1 ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hlinear := D.density_eventual n hdensity_N
  have hthreshold := D.threshold_eventual n hthreshold_N
  have hscaled :
      D.beta * ((D.density - D.eta) * (n : ℝ)) ≤ D.beta * D.E1 n :=
    mul_le_mul_of_nonneg_left hlinear (le_of_lt D.beta_pos)
  have hposterior_input : D.threshold ≤ D.beta * D.E1 n + D.descriptionGap := by
    linarith
  have hposterior := D.posterior_threshold n hposterior_input
  exact ⟨hposterior, D.coherence_upper n hn_pos hposterior⟩

end Omega.Zeta
