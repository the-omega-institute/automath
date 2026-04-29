import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-defect-entropy-closed-form-invariant`. -/
theorem paper_xi_defect_entropy_closed_form_invariant {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (δ : ι → ℝ) (hm : ∃ j, 0 < m j) (hδ : ∀ j, 0 < δ j) :
    0 < (∑ j, (m j : ℝ) * δ j / (1 + δ j)) ∧
      (∑ j, (m j : ℝ) * δ j / (1 + δ j)) < ∑ j, (m j : ℝ) := by
  classical
  have hterm_nonneg : ∀ j, 0 ≤ (m j : ℝ) * δ j / (1 + δ j) := by
    intro j
    have hmj : 0 ≤ (m j : ℝ) := by positivity
    have hden : 0 ≤ 1 + δ j := by linarith [hδ j]
    exact div_nonneg (mul_nonneg hmj (le_of_lt (hδ j))) hden
  have hterm_le : ∀ j, (m j : ℝ) * δ j / (1 + δ j) ≤ (m j : ℝ) := by
    intro j
    have hmj : 0 ≤ (m j : ℝ) := by positivity
    have hden : 0 < 1 + δ j := by linarith [hδ j]
    have hfrac :
        δ j / (1 + δ j) ≤ 1 := by
      have hlt :
          δ j / (1 + δ j) < 1 := by
        have hlt' :
            δ j / (1 + δ j) < (1 + δ j) / (1 + δ j) := by
          exact div_lt_div_of_pos_right (by linarith [hδ j]) hden
        simpa [div_self (ne_of_gt hden)] using hlt'
      exact le_of_lt hlt
    calc
      (m j : ℝ) * δ j / (1 + δ j) = (m j : ℝ) * (δ j / (1 + δ j)) := by
        ring
      _ ≤ (m j : ℝ) * 1 := mul_le_mul_of_nonneg_left hfrac hmj
      _ = (m j : ℝ) := by ring
  rcases hm with ⟨j, hmj_pos_nat⟩
  have hmj_pos : 0 < (m j : ℝ) := by exact_mod_cast hmj_pos_nat
  have hterm_pos_j : 0 < (m j : ℝ) * δ j / (1 + δ j) := by
    have hden : 0 < 1 + δ j := by linarith [hδ j]
    exact div_pos (mul_pos hmj_pos (hδ j)) hden
  have hterm_lt_j : (m j : ℝ) * δ j / (1 + δ j) < (m j : ℝ) := by
    have hden : 0 < 1 + δ j := by linarith [hδ j]
    have hfrac_lt :
        δ j / (1 + δ j) < 1 := by
      have hlt' :
          δ j / (1 + δ j) < (1 + δ j) / (1 + δ j) := by
        exact div_lt_div_of_pos_right (by linarith [hδ j]) hden
      simpa [div_self (ne_of_gt hden)] using hlt'
    calc
      (m j : ℝ) * δ j / (1 + δ j) = (m j : ℝ) * (δ j / (1 + δ j)) := by
        ring
      _ < (m j : ℝ) * 1 := mul_lt_mul_of_pos_left hfrac_lt hmj_pos
      _ = (m j : ℝ) := by ring
  constructor
  · exact lt_of_lt_of_le hterm_pos_j
      (Finset.single_le_sum (fun i _ => hterm_nonneg i) (Finset.mem_univ j))
  · exact Finset.sum_lt_sum (fun i _ => hterm_le i) ⟨j, Finset.mem_univ j, hterm_lt_j⟩

end Omega.Zeta
