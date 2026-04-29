import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The binary character split: one singleton branch and one two-point branch. -/
def xi_time_part62ea_chi_ly_exact_information_loss_chi (x : Fin 3) : Bool :=
  x ≠ 0

/-- Entropy of the uniform three-state source, in natural units. -/
noncomputable def xi_time_part62ea_chi_ly_exact_information_loss_sourceEntropy : ℝ :=
  Real.log 3

/-- Entropy of the binary character induced by a `1:2` split of the three states. -/
noncomputable def xi_time_part62ea_chi_ly_exact_information_loss_characterEntropy : ℝ :=
  -((1 / 3 : ℝ) * Real.log (1 / 3 : ℝ) +
      (2 / 3 : ℝ) * Real.log (2 / 3 : ℝ))

/-- Conditional entropy inside the binary character fibers: only the two-point branch contributes. -/
noncomputable def xi_time_part62ea_chi_ly_exact_information_loss_conditionalEntropy : ℝ :=
  (2 / 3 : ℝ) * Real.log 2

/-- Mutual information retained by the binary character. -/
noncomputable def xi_time_part62ea_chi_ly_exact_information_loss_mutualInformation : ℝ :=
  xi_time_part62ea_chi_ly_exact_information_loss_sourceEntropy -
    xi_time_part62ea_chi_ly_exact_information_loss_conditionalEntropy

/-- Concrete exact-information-loss statement for the `1:2` three-state split. -/
def xi_time_part62ea_chi_ly_exact_information_loss_statement : Prop :=
  Fintype.card
      {x : Fin 3 // xi_time_part62ea_chi_ly_exact_information_loss_chi x = false} =
      1 ∧
    Fintype.card
      {x : Fin 3 // xi_time_part62ea_chi_ly_exact_information_loss_chi x = true} =
      2 ∧
    xi_time_part62ea_chi_ly_exact_information_loss_characterEntropy +
        xi_time_part62ea_chi_ly_exact_information_loss_conditionalEntropy =
      xi_time_part62ea_chi_ly_exact_information_loss_sourceEntropy ∧
    xi_time_part62ea_chi_ly_exact_information_loss_mutualInformation =
      xi_time_part62ea_chi_ly_exact_information_loss_characterEntropy

private lemma xi_time_part62ea_chi_ly_exact_information_loss_log_third :
    Real.log (1 / 3 : ℝ) = -Real.log 3 := by
  rw [show (1 / 3 : ℝ) = (3 : ℝ)⁻¹ by norm_num, Real.log_inv]

private lemma xi_time_part62ea_chi_ly_exact_information_loss_log_two_thirds :
    Real.log (2 / 3 : ℝ) = Real.log 2 - Real.log 3 := by
  rw [div_eq_mul_inv, Real.log_mul]
  · rw [Real.log_inv]
    ring
  · norm_num
  · norm_num

private lemma xi_time_part62ea_chi_ly_exact_information_loss_chain_rule :
    xi_time_part62ea_chi_ly_exact_information_loss_characterEntropy +
        xi_time_part62ea_chi_ly_exact_information_loss_conditionalEntropy =
      xi_time_part62ea_chi_ly_exact_information_loss_sourceEntropy := by
  rw [xi_time_part62ea_chi_ly_exact_information_loss_characterEntropy,
    xi_time_part62ea_chi_ly_exact_information_loss_conditionalEntropy,
    xi_time_part62ea_chi_ly_exact_information_loss_sourceEntropy,
    xi_time_part62ea_chi_ly_exact_information_loss_log_third,
    xi_time_part62ea_chi_ly_exact_information_loss_log_two_thirds]
  ring

/-- Paper label: `cor:xi-time-part62ea-chi-ly-exact-information-loss`. -/
theorem paper_xi_time_part62ea_chi_ly_exact_information_loss :
    xi_time_part62ea_chi_ly_exact_information_loss_statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [xi_time_part62ea_chi_ly_exact_information_loss_chi]
  · norm_num [xi_time_part62ea_chi_ly_exact_information_loss_chi]
  · exact xi_time_part62ea_chi_ly_exact_information_loss_chain_rule
  · rw [xi_time_part62ea_chi_ly_exact_information_loss_mutualInformation,
      ← xi_time_part62ea_chi_ly_exact_information_loss_chain_rule]
    ring

end Omega.Zeta
