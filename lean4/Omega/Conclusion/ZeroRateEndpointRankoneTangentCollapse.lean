import Omega.Conclusion.ZeroRateEndpointFirstOrderBlindHyperplane

namespace Omega.Conclusion

open scoped BigOperators
open Finset

noncomputable section

/--
Endpoint-expansion data for the zero-rate tangent collapse.

The gradient has a constant part plus a rank-one weight direction, and the perturbation lies in
the zero-sum, weight-blind tangent hyperplane.
-/
structure conclusion_zero_rate_endpoint_rankone_tangent_collapse_data (X : Type*)
    [Fintype X] where
  conclusion_zero_rate_endpoint_rankone_tangent_collapse_weight :
    X → ℝ
  conclusion_zero_rate_endpoint_rankone_tangent_collapse_perturbation :
    X → ℝ
  conclusion_zero_rate_endpoint_rankone_tangent_collapse_gradient :
    X → ℝ
  conclusion_zero_rate_endpoint_rankone_tangent_collapse_constant :
    ℝ
  conclusion_zero_rate_endpoint_rankone_tangent_collapse_rankOneCoefficient :
    ℝ
  conclusion_zero_rate_endpoint_rankone_tangent_collapse_endpoint_expansion :
    ∀ x : X,
      conclusion_zero_rate_endpoint_rankone_tangent_collapse_gradient x =
        conclusion_zero_rate_endpoint_rankone_tangent_collapse_constant +
          conclusion_zero_rate_endpoint_rankone_tangent_collapse_rankOneCoefficient *
            conclusion_zero_rate_endpoint_rankone_tangent_collapse_weight x
  conclusion_zero_rate_endpoint_rankone_tangent_collapse_zero_sum :
    (∑ x, conclusion_zero_rate_endpoint_rankone_tangent_collapse_perturbation x) = 0
  conclusion_zero_rate_endpoint_rankone_tangent_collapse_weight_blind :
    (∑ x,
      conclusion_zero_rate_endpoint_rankone_tangent_collapse_perturbation x *
        conclusion_zero_rate_endpoint_rankone_tangent_collapse_weight x) = 0

namespace conclusion_zero_rate_endpoint_rankone_tangent_collapse_data

/-- Modulo constants, the endpoint gradient is the supplied rank-one weight direction. -/
def gradient_mod_constants {X : Type*} [Fintype X]
    (D : conclusion_zero_rate_endpoint_rankone_tangent_collapse_data X) : Prop :=
  ∃ c a : ℝ,
    ∀ x : X,
      D.conclusion_zero_rate_endpoint_rankone_tangent_collapse_gradient x =
        c + a * D.conclusion_zero_rate_endpoint_rankone_tangent_collapse_weight x

/-- Every zero-sum, weight-blind perturbation has zero first directional derivative. -/
def directional_derivative {X : Type*} [Fintype X]
    (D : conclusion_zero_rate_endpoint_rankone_tangent_collapse_data X) : Prop :=
  (∑ x,
    D.conclusion_zero_rate_endpoint_rankone_tangent_collapse_perturbation x *
      D.conclusion_zero_rate_endpoint_rankone_tangent_collapse_gradient x) = 0

end conclusion_zero_rate_endpoint_rankone_tangent_collapse_data

open conclusion_zero_rate_endpoint_rankone_tangent_collapse_data

/-- Paper label: `thm:conclusion-zero-rate-endpoint-rankone-tangent-collapse`. -/
theorem paper_conclusion_zero_rate_endpoint_rankone_tangent_collapse {X : Type*} [Fintype X]
    (D : conclusion_zero_rate_endpoint_rankone_tangent_collapse_data X) :
    D.gradient_mod_constants ∧ D.directional_derivative := by
  constructor
  · exact
      ⟨D.conclusion_zero_rate_endpoint_rankone_tangent_collapse_constant,
        D.conclusion_zero_rate_endpoint_rankone_tangent_collapse_rankOneCoefficient,
        D.conclusion_zero_rate_endpoint_rankone_tangent_collapse_endpoint_expansion⟩
  · rw [directional_derivative]
    trans
      ∑ x,
        D.conclusion_zero_rate_endpoint_rankone_tangent_collapse_perturbation x *
          (D.conclusion_zero_rate_endpoint_rankone_tangent_collapse_constant +
            D.conclusion_zero_rate_endpoint_rankone_tangent_collapse_rankOneCoefficient *
              D.conclusion_zero_rate_endpoint_rankone_tangent_collapse_weight x)
    · refine sum_congr rfl ?_
      intro x _
      rw [D.conclusion_zero_rate_endpoint_rankone_tangent_collapse_endpoint_expansion x]
    · simp only [mul_add, sum_add_distrib]
      have conclusion_zero_rate_endpoint_rankone_tangent_collapse_constant_term :
          (∑ x,
              D.conclusion_zero_rate_endpoint_rankone_tangent_collapse_perturbation x *
                D.conclusion_zero_rate_endpoint_rankone_tangent_collapse_constant) =
            (∑ x, D.conclusion_zero_rate_endpoint_rankone_tangent_collapse_perturbation x) *
              D.conclusion_zero_rate_endpoint_rankone_tangent_collapse_constant := by
        rw [sum_mul]
      have conclusion_zero_rate_endpoint_rankone_tangent_collapse_rank_one_term :
          (∑ x,
              D.conclusion_zero_rate_endpoint_rankone_tangent_collapse_perturbation x *
                (D.conclusion_zero_rate_endpoint_rankone_tangent_collapse_rankOneCoefficient *
                  D.conclusion_zero_rate_endpoint_rankone_tangent_collapse_weight x)) =
            D.conclusion_zero_rate_endpoint_rankone_tangent_collapse_rankOneCoefficient *
              (∑ x,
                D.conclusion_zero_rate_endpoint_rankone_tangent_collapse_perturbation x *
                  D.conclusion_zero_rate_endpoint_rankone_tangent_collapse_weight x) := by
        rw [mul_sum]
        refine sum_congr rfl ?_
        intro x _
        ring
      rw [conclusion_zero_rate_endpoint_rankone_tangent_collapse_constant_term,
        conclusion_zero_rate_endpoint_rankone_tangent_collapse_rank_one_term,
        D.conclusion_zero_rate_endpoint_rankone_tangent_collapse_zero_sum,
        D.conclusion_zero_rate_endpoint_rankone_tangent_collapse_weight_blind]
      ring

end

end Omega.Conclusion
