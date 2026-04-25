import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace Omega.Zeta

/-- The minimum exponential scale controlling the number of addressable objects. -/
noncomputable def xi_time_resolution_dual_budget_phase_transition_minimumScale
    (epsilon collisionEntropy : ℝ) (timeBudget resolutionBudget : ℕ) : ℝ :=
  min (epsilon * (timeBudget : ℝ)) ((collisionEntropy * (resolutionBudget : ℝ)) / 2)

/-- Formal statement of the dual budget phase transition bounds. -/
def xi_time_resolution_dual_budget_phase_transition_statement
    (timeBudget resolutionBudget : ℕ) (epsilon collisionEntropy eta failProbability : ℝ) :
    Prop :=
  failProbability ≤ eta ∧
    1 - eta ≤ failProbability ∧
    xi_time_resolution_dual_budget_phase_transition_minimumScale epsilon collisionEntropy
        timeBudget resolutionBudget =
      min (epsilon * (timeBudget : ℝ)) ((collisionEntropy * (resolutionBudget : ℝ)) / 2)

private lemma xi_time_resolution_dual_budget_phase_transition_union_subcritical
    (objects timeBudget resolutionBudget : ℕ)
    (epsilon collisionEntropy eta syncTail collisionProbability collisionPairs
      failProbability : ℝ)
    (hcollisionPairs_nonneg : 0 ≤ collisionPairs)
    (hcollisionPairs_le_quadratic : collisionPairs ≤ (objects : ℝ) ^ 2 / 2)
    (hsync_exponential_law :
      syncTail ≤ Real.exp (-(epsilon * (timeBudget : ℝ))))
    (hcollision_exponential_law :
      collisionProbability ≤ Real.exp (-(collisionEntropy * (resolutionBudget : ℝ))))
    (hunion_bound :
      failProbability ≤ (objects : ℝ) * syncTail + collisionPairs * collisionProbability)
    (hsubcritical_exponential_budget :
      (objects : ℝ) * Real.exp (-(epsilon * (timeBudget : ℝ))) +
          ((objects : ℝ) ^ 2 / 2) *
            Real.exp (-(collisionEntropy * (resolutionBudget : ℝ))) ≤ eta) :
    failProbability ≤ eta := by
  have hobjects_nonneg : 0 ≤ (objects : ℝ) := by positivity
  have hsync_exp_nonneg :
      0 ≤ Real.exp (-(epsilon * (timeBudget : ℝ))) := by positivity
  have hcollision_exp_nonneg :
      0 ≤ Real.exp (-(collisionEntropy * (resolutionBudget : ℝ))) := by positivity
  have hsync_term :
      (objects : ℝ) * syncTail ≤
        (objects : ℝ) * Real.exp (-(epsilon * (timeBudget : ℝ))) := by
    exact mul_le_mul_of_nonneg_left hsync_exponential_law hobjects_nonneg
  have hcollision_law_term :
      collisionPairs * collisionProbability ≤
        collisionPairs * Real.exp (-(collisionEntropy * (resolutionBudget : ℝ))) := by
    exact mul_le_mul_of_nonneg_left hcollision_exponential_law hcollisionPairs_nonneg
  have hcollision_pair_term :
      collisionPairs * Real.exp (-(collisionEntropy * (resolutionBudget : ℝ))) ≤
        ((objects : ℝ) ^ 2 / 2) *
          Real.exp (-(collisionEntropy * (resolutionBudget : ℝ))) := by
    exact mul_le_mul_of_nonneg_right hcollisionPairs_le_quadratic hcollision_exp_nonneg
  calc
    failProbability ≤ (objects : ℝ) * syncTail + collisionPairs * collisionProbability :=
      hunion_bound
    _ ≤ (objects : ℝ) * Real.exp (-(epsilon * (timeBudget : ℝ))) +
        ((objects : ℝ) ^ 2 / 2) *
          Real.exp (-(collisionEntropy * (resolutionBudget : ℝ))) := by
      exact add_le_add hsync_term (hcollision_law_term.trans hcollision_pair_term)
    _ ≤ eta := hsubcritical_exponential_budget

/-- Paper label: `thm:xi-time-resolution-dual-budget-phase-transition`.  The subcritical
direction is the union bound after inserting the two exponential estimates; the supercritical
direction is the supplied second-moment threshold lower bound; the scale is the minimum of the
time and resolution exponents. -/
theorem paper_xi_time_resolution_dual_budget_phase_transition
    (objects timeBudget resolutionBudget : ℕ)
    (epsilon collisionEntropy eta syncTail collisionProbability collisionPairs
      failProbability : ℝ)
    (hcollisionPairs_nonneg : 0 ≤ collisionPairs)
    (hcollisionPairs_le_quadratic : collisionPairs ≤ (objects : ℝ) ^ 2 / 2)
    (hsync_exponential_law :
      syncTail ≤ Real.exp (-(epsilon * (timeBudget : ℝ))))
    (hcollision_exponential_law :
      collisionProbability ≤ Real.exp (-(collisionEntropy * (resolutionBudget : ℝ))))
    (hunion_bound :
      failProbability ≤ (objects : ℝ) * syncTail + collisionPairs * collisionProbability)
    (hsubcritical_exponential_budget :
      (objects : ℝ) * Real.exp (-(epsilon * (timeBudget : ℝ))) +
          ((objects : ℝ) ^ 2 / 2) *
            Real.exp (-(collisionEntropy * (resolutionBudget : ℝ))) ≤ eta)
    (hsupercritical_second_moment_threshold : 1 - eta ≤ failProbability) :
    xi_time_resolution_dual_budget_phase_transition_statement timeBudget resolutionBudget
      epsilon collisionEntropy eta failProbability := by
  refine ⟨?_, ?_, ?_⟩
  · exact
      xi_time_resolution_dual_budget_phase_transition_union_subcritical objects timeBudget
        resolutionBudget epsilon collisionEntropy eta syncTail collisionProbability collisionPairs
        failProbability hcollisionPairs_nonneg hcollisionPairs_le_quadratic
        hsync_exponential_law hcollision_exponential_law hunion_bound
        hsubcritical_exponential_budget
  · exact hsupercritical_second_moment_threshold
  · rfl

end Omega.Zeta
