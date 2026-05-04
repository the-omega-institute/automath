import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- Uniform fiber mass for the three window-6 local hidden layers. -/
def conclusion_window6_d2_slice_unique_local_interaction_layer_mass
    (d eta xi : ℕ) : ℝ :=
  match d, eta, xi with
  | 2, 0, 0 => 1 / 2
  | 2, 0, 1 => 1 / 2
  | 3, 0, 0 => 1 / 3
  | 3, 1, 0 => 1 / 3
  | 3, 0, 1 => 1 / 3
  | 4, 0, 0 => 1 / 4
  | 4, 0, 1 => 1 / 4
  | 4, 1, 0 => 1 / 4
  | 4, 1, 1 => 1 / 4
  | _, _, _ => 0

/-- The eta marginal of the local finite law. -/
def conclusion_window6_d2_slice_unique_local_interaction_layer_eta_marginal
    (d eta : ℕ) : ℝ :=
  ∑ xi : Fin 2,
    conclusion_window6_d2_slice_unique_local_interaction_layer_mass d eta xi.val

/-- The xi marginal of the local finite law. -/
def conclusion_window6_d2_slice_unique_local_interaction_layer_xi_marginal
    (d xi : ℕ) : ℝ :=
  ∑ eta : Fin 2,
    conclusion_window6_d2_slice_unique_local_interaction_layer_mass d eta.val xi

/-- Mutual information computed by the finite four-point sum, with zero-mass terms omitted. -/
def conclusion_window6_d2_slice_unique_local_interaction_layer_mutual_information
    (d : ℕ) : ℝ :=
  ∑ eta : Fin 2, ∑ xi : Fin 2,
    let p := conclusion_window6_d2_slice_unique_local_interaction_layer_mass d eta.val xi.val
    if p = 0 then 0
    else
      p * Real.log
        (p /
          (conclusion_window6_d2_slice_unique_local_interaction_layer_eta_marginal d eta.val *
            conclusion_window6_d2_slice_unique_local_interaction_layer_xi_marginal d xi.val))

/-- Mean of eta under the local finite law. -/
def conclusion_window6_d2_slice_unique_local_interaction_layer_eta_mean
    (d : ℕ) : ℝ :=
  ∑ eta : Fin 2,
    (eta.val : ℝ) * conclusion_window6_d2_slice_unique_local_interaction_layer_eta_marginal d eta.val

/-- Mean of xi under the local finite law. -/
def conclusion_window6_d2_slice_unique_local_interaction_layer_xi_mean
    (d : ℕ) : ℝ :=
  ∑ xi : Fin 2,
    (xi.val : ℝ) * conclusion_window6_d2_slice_unique_local_interaction_layer_xi_marginal d xi.val

/-- Cross covariance computed by the finite four-point sum. -/
def conclusion_window6_d2_slice_unique_local_interaction_layer_covariance
    (d : ℕ) : ℝ :=
  ∑ eta : Fin 2, ∑ xi : Fin 2,
    conclusion_window6_d2_slice_unique_local_interaction_layer_mass d eta.val xi.val *
      ((eta.val : ℝ) - conclusion_window6_d2_slice_unique_local_interaction_layer_eta_mean d) *
        ((xi.val : ℝ) - conclusion_window6_d2_slice_unique_local_interaction_layer_xi_mean d)

/-- Concrete statement of the unique local interaction layer computation. -/
def conclusion_window6_d2_slice_unique_local_interaction_layer_statement : Prop :=
  conclusion_window6_d2_slice_unique_local_interaction_layer_mutual_information 2 = 0 ∧
    conclusion_window6_d2_slice_unique_local_interaction_layer_mutual_information 4 = 0 ∧
      conclusion_window6_d2_slice_unique_local_interaction_layer_mutual_information 3 =
        (1 / 3 : ℝ) * Real.log (27 / 16) ∧
        conclusion_window6_d2_slice_unique_local_interaction_layer_covariance 2 = 0 ∧
          conclusion_window6_d2_slice_unique_local_interaction_layer_covariance 4 = 0 ∧
            conclusion_window6_d2_slice_unique_local_interaction_layer_covariance 3 =
              -1 / 9

private lemma conclusion_window6_d2_slice_unique_local_interaction_layer_log_identity :
    (1 / 3 : ℝ) * Real.log (3 / 4) + 2 / 3 * Real.log (3 / 2) =
      (1 / 3 : ℝ) * Real.log (27 / 16) := by
  have h34 : (0 : ℝ) < 3 / 4 := by norm_num
  have h32 : (0 : ℝ) < 3 / 2 := by norm_num
  have h32_ne : (3 / 2 : ℝ) ≠ 0 := ne_of_gt h32
  have hcombine :
      Real.log (3 / 4) + 2 * Real.log (3 / 2) = Real.log (27 / 16 : ℝ) := by
    have hpow : 2 * Real.log (3 / 2 : ℝ) = Real.log ((3 / 2 : ℝ) ^ 2) := by
      rw [Real.log_pow]
      ring
    rw [hpow]
    rw [← Real.log_mul h34.ne' (pow_ne_zero 2 h32_ne)]
    norm_num
  calc
    (1 / 3 : ℝ) * Real.log (3 / 4) + 2 / 3 * Real.log (3 / 2)
        = (1 / 3 : ℝ) * (Real.log (3 / 4) + 2 * Real.log (3 / 2)) := by
            ring
    _ = (1 / 3 : ℝ) * Real.log (27 / 16) := by rw [hcombine]

/-- Paper label: `thm:conclusion-window6-d2-slice-unique-local-interaction-layer`. -/
theorem paper_conclusion_window6_d2_slice_unique_local_interaction_layer :
    conclusion_window6_d2_slice_unique_local_interaction_layer_statement := by
  unfold conclusion_window6_d2_slice_unique_local_interaction_layer_statement
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [conclusion_window6_d2_slice_unique_local_interaction_layer_mutual_information,
      conclusion_window6_d2_slice_unique_local_interaction_layer_mass,
      conclusion_window6_d2_slice_unique_local_interaction_layer_eta_marginal,
      conclusion_window6_d2_slice_unique_local_interaction_layer_xi_marginal]
  · norm_num [conclusion_window6_d2_slice_unique_local_interaction_layer_mutual_information,
      conclusion_window6_d2_slice_unique_local_interaction_layer_mass,
      conclusion_window6_d2_slice_unique_local_interaction_layer_eta_marginal,
      conclusion_window6_d2_slice_unique_local_interaction_layer_xi_marginal]
  · have h :
        conclusion_window6_d2_slice_unique_local_interaction_layer_mutual_information 3 =
          (1 / 3 : ℝ) * Real.log (3 / 4) + 2 / 3 * Real.log (3 / 2) := by
      norm_num [conclusion_window6_d2_slice_unique_local_interaction_layer_mutual_information,
        conclusion_window6_d2_slice_unique_local_interaction_layer_mass,
        conclusion_window6_d2_slice_unique_local_interaction_layer_eta_marginal,
        conclusion_window6_d2_slice_unique_local_interaction_layer_xi_marginal]
      ring
    rw [h, conclusion_window6_d2_slice_unique_local_interaction_layer_log_identity]
  · norm_num [conclusion_window6_d2_slice_unique_local_interaction_layer_covariance,
      conclusion_window6_d2_slice_unique_local_interaction_layer_mass,
      conclusion_window6_d2_slice_unique_local_interaction_layer_eta_marginal,
      conclusion_window6_d2_slice_unique_local_interaction_layer_xi_marginal,
      conclusion_window6_d2_slice_unique_local_interaction_layer_eta_mean,
      conclusion_window6_d2_slice_unique_local_interaction_layer_xi_mean]
  · norm_num [conclusion_window6_d2_slice_unique_local_interaction_layer_covariance,
      conclusion_window6_d2_slice_unique_local_interaction_layer_mass,
      conclusion_window6_d2_slice_unique_local_interaction_layer_eta_marginal,
      conclusion_window6_d2_slice_unique_local_interaction_layer_xi_marginal,
      conclusion_window6_d2_slice_unique_local_interaction_layer_eta_mean,
      conclusion_window6_d2_slice_unique_local_interaction_layer_xi_mean]
  · norm_num [conclusion_window6_d2_slice_unique_local_interaction_layer_covariance,
      conclusion_window6_d2_slice_unique_local_interaction_layer_mass,
      conclusion_window6_d2_slice_unique_local_interaction_layer_eta_marginal,
      conclusion_window6_d2_slice_unique_local_interaction_layer_xi_marginal,
      conclusion_window6_d2_slice_unique_local_interaction_layer_eta_mean,
      conclusion_window6_d2_slice_unique_local_interaction_layer_xi_mean]

end

end Omega.Conclusion
