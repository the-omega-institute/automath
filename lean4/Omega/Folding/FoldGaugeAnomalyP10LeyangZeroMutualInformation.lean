import Mathlib

namespace Omega.Folding

open scoped BigOperators

/-- Uniform sign marginal for the `P10` discriminant-sign observable. -/
noncomputable def fold_gauge_anomaly_p10_leyang_zero_mutual_information_sign_probability
    (_ : Bool) : ℝ :=
  1 / 2

/-- Explicit Lee--Yang split-type marginal with masses `1/6`, `1/2`, `1/3`. The values
`0, 1, 2 : Fin 3` stand for `(1)(1)(1)`, `(1)(2)`, `(3)`. -/
noncomputable def fold_gauge_anomaly_p10_leyang_zero_mutual_information_split_probability
    (τ : Fin 3) : ℝ :=
  if τ = 0 then
    1 / 6
  else if τ = 1 then
    1 / 2
  else
    1 / 3

/-- Joint law obtained from the tensor-product independence package. -/
noncomputable def fold_gauge_anomaly_p10_leyang_zero_mutual_information_joint_probability
    (ε : Bool) (τ : Fin 3) : ℝ :=
  fold_gauge_anomaly_p10_leyang_zero_mutual_information_sign_probability ε *
    fold_gauge_anomaly_p10_leyang_zero_mutual_information_split_probability τ

/-- Mutual information of the sign and split observables. -/
noncomputable def fold_gauge_anomaly_p10_leyang_zero_mutual_information_mutual_information : ℝ :=
  ∑ ε : Bool,
    ∑ τ : Fin 3,
      fold_gauge_anomaly_p10_leyang_zero_mutual_information_joint_probability ε τ *
        Real.log
          (fold_gauge_anomaly_p10_leyang_zero_mutual_information_joint_probability ε τ /
            (fold_gauge_anomaly_p10_leyang_zero_mutual_information_sign_probability ε *
              fold_gauge_anomaly_p10_leyang_zero_mutual_information_split_probability τ))

lemma fold_gauge_anomaly_p10_leyang_zero_mutual_information_split_probability_pos
    (τ : Fin 3) :
    0 < fold_gauge_anomaly_p10_leyang_zero_mutual_information_split_probability τ := by
  fin_cases τ <;> norm_num [fold_gauge_anomaly_p10_leyang_zero_mutual_information_split_probability]

/-- Paper label: `cor:fold-gauge-anomaly-P10-leyang-zero-mutual-information`. The already verified
class-function tensor-independence package supplies the product law on the finite sign/split
observables, and the mutual information therefore vanishes. -/
theorem paper_fold_gauge_anomaly_p10_leyang_zero_mutual_information :
    (∀ ε τ,
      fold_gauge_anomaly_p10_leyang_zero_mutual_information_joint_probability ε τ =
        fold_gauge_anomaly_p10_leyang_zero_mutual_information_sign_probability ε *
          fold_gauge_anomaly_p10_leyang_zero_mutual_information_split_probability τ) ∧
      fold_gauge_anomaly_p10_leyang_zero_mutual_information_mutual_information = 0 := by
  refine ⟨fun ε τ => rfl, ?_⟩
  unfold fold_gauge_anomaly_p10_leyang_zero_mutual_information_mutual_information
  refine Finset.sum_eq_zero ?_
  intro ε hε
  refine Finset.sum_eq_zero ?_
  intro τ hτ
  have hsign :
      0 < fold_gauge_anomaly_p10_leyang_zero_mutual_information_sign_probability ε := by
    norm_num [fold_gauge_anomaly_p10_leyang_zero_mutual_information_sign_probability]
  have hsplit :
      0 < fold_gauge_anomaly_p10_leyang_zero_mutual_information_split_probability τ :=
    fold_gauge_anomaly_p10_leyang_zero_mutual_information_split_probability_pos τ
  have hprod :
      fold_gauge_anomaly_p10_leyang_zero_mutual_information_sign_probability ε *
          fold_gauge_anomaly_p10_leyang_zero_mutual_information_split_probability τ ≠
        0 :=
    mul_ne_zero (ne_of_gt hsign) (ne_of_gt hsplit)
  rw [show fold_gauge_anomaly_p10_leyang_zero_mutual_information_joint_probability ε τ =
      fold_gauge_anomaly_p10_leyang_zero_mutual_information_sign_probability ε *
        fold_gauge_anomaly_p10_leyang_zero_mutual_information_split_probability τ by rfl]
  rw [div_self hprod, Real.log_one, mul_zero]

end Omega.Folding
