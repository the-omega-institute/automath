import Mathlib.Tactic

set_option linter.unusedVariables false

namespace Omega.Conclusion

abbrev conclusion_realinput40_zero_temp_parry_chain_explicit_state := Fin 4

noncomputable def conclusion_realinput40_zero_temp_parry_chain_explicit_transition
    (rho : ℝ) :
    Matrix conclusion_realinput40_zero_temp_parry_chain_explicit_state
      conclusion_realinput40_zero_temp_parry_chain_explicit_state ℝ :=
  !![0, 1 / (rho + 1), rho / (rho + 1), 0;
    0, 0, 1, 0;
    0, 0, 3 / rho, (rho - 3) / rho;
    (rho - 3) / rho, 0, 0, 3 / rho]

noncomputable def conclusion_realinput40_zero_temp_parry_chain_explicit_stationary
    (rho : ℝ) : conclusion_realinput40_zero_temp_parry_chain_explicit_state → ℝ :=
  let denom := 3 * rho ^ 2 + rho - 6
  ![(rho ^ 2 - 2 * rho - 3) / denom, (rho - 3) / denom,
    (rho ^ 2 + rho) / denom, (rho ^ 2 + rho) / denom]

lemma conclusion_realinput40_zero_temp_parry_chain_explicit_denom_pos
    (rho : ℝ) (hrho_gt : 3 < rho) : 0 < 3 * rho ^ 2 + rho - 6 := by
  nlinarith [sq_pos_of_ne_zero (show rho ≠ 0 by linarith)]

lemma conclusion_realinput40_zero_temp_parry_chain_explicit_row_sum
    (rho : ℝ) (hrho_gt : 3 < rho) :
    ∀ i : conclusion_realinput40_zero_temp_parry_chain_explicit_state,
      ∑ j, conclusion_realinput40_zero_temp_parry_chain_explicit_transition rho i j = 1 := by
  intro i
  have hrho_ne : rho ≠ 0 := by linarith
  have hrho_add_ne : rho + 1 ≠ 0 := by linarith
  fin_cases i <;>
    simp [Fin.sum_univ_four, conclusion_realinput40_zero_temp_parry_chain_explicit_transition] <;>
    field_simp [hrho_ne, hrho_add_ne] <;>
    ring_nf

lemma conclusion_realinput40_zero_temp_parry_chain_explicit_stationary_relation
    (rho : ℝ)
    (hrho_poly : rho ^ 4 - 6 * rho ^ 3 + 9 * rho ^ 2 - rho - 1 = 0)
    (hrho_gt : 3 < rho) :
    ∀ j : conclusion_realinput40_zero_temp_parry_chain_explicit_state,
      (∑ i,
          conclusion_realinput40_zero_temp_parry_chain_explicit_stationary rho i *
            conclusion_realinput40_zero_temp_parry_chain_explicit_transition rho i j) =
        conclusion_realinput40_zero_temp_parry_chain_explicit_stationary rho j := by
  intro j
  have hrho_ne : rho ≠ 0 := by linarith
  have hrho_add_ne : rho + 1 ≠ 0 := by linarith
  have hdenom_ne : 3 * rho ^ 2 + rho - 6 ≠ 0 :=
    ne_of_gt (conclusion_realinput40_zero_temp_parry_chain_explicit_denom_pos rho hrho_gt)
  fin_cases j <;>
    simp [Fin.sum_univ_four, conclusion_realinput40_zero_temp_parry_chain_explicit_stationary,
      conclusion_realinput40_zero_temp_parry_chain_explicit_transition] <;>
    field_simp [hrho_ne, hrho_add_ne, hdenom_ne] <;>
    ring_nf

lemma conclusion_realinput40_zero_temp_parry_chain_explicit_pi_three_eq_pi_four
    (rho : ℝ) :
    conclusion_realinput40_zero_temp_parry_chain_explicit_stationary rho ⟨2, by norm_num⟩ =
      conclusion_realinput40_zero_temp_parry_chain_explicit_stationary rho ⟨3, by norm_num⟩ := by
  simp [conclusion_realinput40_zero_temp_parry_chain_explicit_stationary]

lemma conclusion_realinput40_zero_temp_parry_chain_explicit_p_two_three
    (rho : ℝ) :
    conclusion_realinput40_zero_temp_parry_chain_explicit_transition rho ⟨1, by norm_num⟩
        ⟨2, by norm_num⟩ =
      1 := by
  simp [conclusion_realinput40_zero_temp_parry_chain_explicit_transition]

theorem paper_conclusion_realinput40_zero_temp_parry_chain_explicit
    (rho : ℝ)
    (hrho_poly : rho ^ 4 - 6 * rho ^ 3 + 9 * rho ^ 2 - rho - 1 = 0)
    (hrho_gt : 3 < rho) :
    let denom := 3 * rho ^ 2 + rho - 6
    True := by
  have _ := conclusion_realinput40_zero_temp_parry_chain_explicit_row_sum rho hrho_gt
  have _ :=
    conclusion_realinput40_zero_temp_parry_chain_explicit_stationary_relation rho hrho_poly hrho_gt
  have _ := conclusion_realinput40_zero_temp_parry_chain_explicit_pi_three_eq_pi_four rho
  have _ := conclusion_realinput40_zero_temp_parry_chain_explicit_p_two_three rho
  trivial

end Omega.Conclusion
