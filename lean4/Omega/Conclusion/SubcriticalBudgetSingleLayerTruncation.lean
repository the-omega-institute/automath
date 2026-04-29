import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Zeta.XiTimePart9tTopGapAffineCapacitySegment

namespace Omega.Conclusion

/-- Concrete subcritical budget data for the single-layer truncation package. The inequalities
`M₂ < 2^B < M` say that the budget clears the entire second layer but still truncates the maximal
fiber. -/
structure conclusion_subcritical_budget_single_layer_truncation_data where
  conclusion_subcritical_budget_single_layer_truncation_ambientExponent : ℕ
  conclusion_subcritical_budget_single_layer_truncation_maxFiberSize : ℕ
  conclusion_subcritical_budget_single_layer_truncation_secondLayerSize : ℕ
  conclusion_subcritical_budget_single_layer_truncation_budgetBits : ℕ
  conclusion_subcritical_budget_single_layer_truncation_secondLayer_lt_budget :
    conclusion_subcritical_budget_single_layer_truncation_secondLayerSize <
      2 ^ conclusion_subcritical_budget_single_layer_truncation_budgetBits
  conclusion_subcritical_budget_single_layer_truncation_budget_lt_maxFiber :
    2 ^ conclusion_subcritical_budget_single_layer_truncation_budgetBits <
      conclusion_subcritical_budget_single_layer_truncation_maxFiberSize

/-- The one-fiber affine capacity segment at the subcritical budget `2^B`. -/
def conclusion_subcritical_budget_single_layer_truncation_capacity
    (D : conclusion_subcritical_budget_single_layer_truncation_data) : ℤ :=
  Omega.Zeta.xiTopGapCapacitySegment
    D.conclusion_subcritical_budget_single_layer_truncation_ambientExponent
    1
    D.conclusion_subcritical_budget_single_layer_truncation_maxFiberSize
    (2 ^ D.conclusion_subcritical_budget_single_layer_truncation_budgetBits)

/-- The normalized success factor on the unique truncated maximal fiber. -/
noncomputable def conclusion_subcritical_budget_single_layer_truncation_Succ
    (D : conclusion_subcritical_budget_single_layer_truncation_data) : ℝ :=
  (2 ^ D.conclusion_subcritical_budget_single_layer_truncation_budgetBits : ℝ) /
    D.conclusion_subcritical_budget_single_layer_truncation_maxFiberSize

/-- Paper-facing statement: the capacity stays on the affine top-gap segment, the defect is
exactly `1 - Succ`, and only the maximal layer is truncated. -/
def conclusion_subcritical_budget_single_layer_truncation_statement
    (D : conclusion_subcritical_budget_single_layer_truncation_data) : Prop :=
  conclusion_subcritical_budget_single_layer_truncation_capacity D =
      (2 ^
          D.conclusion_subcritical_budget_single_layer_truncation_ambientExponent : ℤ) -
        ((D.conclusion_subcritical_budget_single_layer_truncation_maxFiberSize -
            2 ^ D.conclusion_subcritical_budget_single_layer_truncation_budgetBits : ℕ) : ℤ) ∧
    conclusion_subcritical_budget_single_layer_truncation_capacity D =
      Omega.Zeta.xiTopGapCapacityIntercept
          D.conclusion_subcritical_budget_single_layer_truncation_ambientExponent
          1
          D.conclusion_subcritical_budget_single_layer_truncation_maxFiberSize +
        Omega.Zeta.xiTopGapCapacitySlope 1 *
          (2 ^ D.conclusion_subcritical_budget_single_layer_truncation_budgetBits) ∧
    1 - conclusion_subcritical_budget_single_layer_truncation_Succ D =
      ((D.conclusion_subcritical_budget_single_layer_truncation_maxFiberSize -
            2 ^ D.conclusion_subcritical_budget_single_layer_truncation_budgetBits : ℕ) : ℝ) /
        D.conclusion_subcritical_budget_single_layer_truncation_maxFiberSize ∧
    min D.conclusion_subcritical_budget_single_layer_truncation_secondLayerSize
        (2 ^ D.conclusion_subcritical_budget_single_layer_truncation_budgetBits) =
      D.conclusion_subcritical_budget_single_layer_truncation_secondLayerSize ∧
    min D.conclusion_subcritical_budget_single_layer_truncation_maxFiberSize
        (2 ^ D.conclusion_subcritical_budget_single_layer_truncation_budgetBits) =
      2 ^ D.conclusion_subcritical_budget_single_layer_truncation_budgetBits

/-- Paper label: `thm:conclusion-subcritical-budget-single-layer-truncation`. The already audited
top-gap affine capacity formula specializes to a one-layer truncation regime as soon as
`M₂ < 2^B < M`; then the lower layer is untouched, the maximal layer is cut at `2^B`, and the
defect is exactly `1 - Succ`. -/
theorem paper_conclusion_subcritical_budget_single_layer_truncation
    (D : conclusion_subcritical_budget_single_layer_truncation_data) :
    conclusion_subcritical_budget_single_layer_truncation_statement D := by
  have hcapacity :=
    Omega.Zeta.paper_xi_time_part9t_top_gap_affine_capacity_segment
      D.conclusion_subcritical_budget_single_layer_truncation_ambientExponent
      1
      D.conclusion_subcritical_budget_single_layer_truncation_maxFiberSize
      (2 ^ D.conclusion_subcritical_budget_single_layer_truncation_budgetBits)
      D.conclusion_subcritical_budget_single_layer_truncation_budget_lt_maxFiber
  have hbudget_le :
      2 ^ D.conclusion_subcritical_budget_single_layer_truncation_budgetBits ≤
        D.conclusion_subcritical_budget_single_layer_truncation_maxFiberSize :=
    Nat.le_of_lt D.conclusion_subcritical_budget_single_layer_truncation_budget_lt_maxFiber
  have hpow_pos :
      0 < 2 ^ D.conclusion_subcritical_budget_single_layer_truncation_budgetBits := by
    exact pow_pos (by decide : 0 < 2)
      D.conclusion_subcritical_budget_single_layer_truncation_budgetBits
  have hmaxFiber_pos_nat :
      0 < D.conclusion_subcritical_budget_single_layer_truncation_maxFiberSize :=
    lt_trans hpow_pos D.conclusion_subcritical_budget_single_layer_truncation_budget_lt_maxFiber
  have hmaxFiber_ne :
      (D.conclusion_subcritical_budget_single_layer_truncation_maxFiberSize : ℝ) ≠ 0 := by
    positivity
  have hdefect :
      1 - conclusion_subcritical_budget_single_layer_truncation_Succ D =
        ((D.conclusion_subcritical_budget_single_layer_truncation_maxFiberSize -
              2 ^ D.conclusion_subcritical_budget_single_layer_truncation_budgetBits : ℕ) : ℝ) /
          D.conclusion_subcritical_budget_single_layer_truncation_maxFiberSize := by
    have hcast_sub :
        (((D.conclusion_subcritical_budget_single_layer_truncation_maxFiberSize -
              2 ^ D.conclusion_subcritical_budget_single_layer_truncation_budgetBits : ℕ) : ℝ)) =
          (D.conclusion_subcritical_budget_single_layer_truncation_maxFiberSize : ℝ) -
            (2 ^ D.conclusion_subcritical_budget_single_layer_truncation_budgetBits : ℝ) := by
      norm_num [Nat.cast_sub hbudget_le]
    have hmain :
        1 - conclusion_subcritical_budget_single_layer_truncation_Succ D =
          ((D.conclusion_subcritical_budget_single_layer_truncation_maxFiberSize : ℝ) -
              (2 ^ D.conclusion_subcritical_budget_single_layer_truncation_budgetBits : ℝ)) /
            D.conclusion_subcritical_budget_single_layer_truncation_maxFiberSize := by
      dsimp [conclusion_subcritical_budget_single_layer_truncation_Succ]
      field_simp [hmaxFiber_ne]
    calc
      1 - conclusion_subcritical_budget_single_layer_truncation_Succ D =
          ((D.conclusion_subcritical_budget_single_layer_truncation_maxFiberSize : ℝ) -
              (2 ^ D.conclusion_subcritical_budget_single_layer_truncation_budgetBits : ℝ)) /
            D.conclusion_subcritical_budget_single_layer_truncation_maxFiberSize := hmain
      _ =
          ((D.conclusion_subcritical_budget_single_layer_truncation_maxFiberSize -
                2 ^ D.conclusion_subcritical_budget_single_layer_truncation_budgetBits : ℕ) : ℝ) /
            D.conclusion_subcritical_budget_single_layer_truncation_maxFiberSize := by
              rw [← hcast_sub]
  refine ⟨?_, ?_, hdefect, ?_, ?_⟩
  · simpa [conclusion_subcritical_budget_single_layer_truncation_capacity] using hcapacity.1
  · simpa [conclusion_subcritical_budget_single_layer_truncation_capacity] using hcapacity.2.1
  · exact Nat.min_eq_left (Nat.le_of_lt
      D.conclusion_subcritical_budget_single_layer_truncation_secondLayer_lt_budget)
  · exact Nat.min_eq_right (Nat.le_of_lt
      D.conclusion_subcritical_budget_single_layer_truncation_budget_lt_maxFiber)

end Omega.Conclusion
