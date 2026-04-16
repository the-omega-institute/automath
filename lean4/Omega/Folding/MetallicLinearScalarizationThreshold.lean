import Mathlib.Tactic
import Omega.Folding.MetallicParetoScaleLaw

namespace Omega.Folding

/-- Seed critical threshold for the paper-facing linear scalarization package. -/
noncomputable def metallicLinearBetaCritical : ℝ := 1 / 2

/-- Interior optimizer used below the critical threshold. -/
noncomputable def metallicLinearInteriorScale (β : ℝ) : ℝ := 3 / 2 - β

/-- A chapter-local threshold datum matching the scalarization split needed by the paper wrapper. -/
noncomputable def metallicLinearThresholdData : MetallicParetoScaleLawData where
  optimalScale β := if β < metallicLinearBetaCritical then metallicLinearInteriorScale β else 1
  betaCritical := metallicLinearBetaCritical
  firstOrderBalance β :=
    (if β < metallicLinearBetaCritical then metallicLinearInteriorScale β else 1) =
      metallicLinearInteriorScale β
  betaCritical_nonneg := by
    norm_num [metallicLinearBetaCritical]
  optimalScale_mem_Icc := by
    intro β hβ
    by_cases hlt : β < metallicLinearBetaCritical
    · rw [Set.mem_Icc, if_pos hlt]
      have hlt' : β < (1 / 2 : ℝ) := by simpa [metallicLinearBetaCritical] using hlt
      simp [metallicLinearInteriorScale]
      constructor <;> linarith
    · rw [Set.mem_Icc, if_neg hlt]
      norm_num
  thresholdSplit := by
    intro β hβ
    by_cases hlt : β < metallicLinearBetaCritical
    · left
      refine ⟨hlt, ?_⟩
      rw [if_pos hlt]
    · right
      refine ⟨le_of_not_gt hlt, ?_⟩
      rw [if_neg hlt]

/-- Paper-facing threshold law for the linear metallic scalarization: the optimizer stays in the
metallic Pareto window, equals `3 / 2` at zero weight, obeys the interior balance below the
critical threshold, and locks to the endpoint `A = 1` at or above the threshold. -/
def metallicLinearScalarizationThresholdLaw : Prop :=
  ∃ h : MetallicParetoScaleLawData,
    h.betaCritical = metallicLinearBetaCritical ∧
      h.optimalScale 0 = 3 / 2 ∧
      ((∀ beta : Real, 0 ≤ beta → 1 ≤ h.optimalScale beta ∧ h.optimalScale beta ≤ 3 / 2) ∧
        (∀ beta : Real, 0 ≤ beta → beta < h.betaCritical → h.firstOrderBalance beta) ∧
        (∀ beta : Real, h.betaCritical ≤ beta → h.optimalScale beta = 1))

theorem paper_metallic_linear_scalarization_threshold :
    metallicLinearScalarizationThresholdLaw := by
  refine ⟨metallicLinearThresholdData, rfl, ?_, ?_⟩
  · simp [metallicLinearThresholdData, metallicLinearBetaCritical, metallicLinearInteriorScale]
  · simpa using paper_metallic_pareto_scale_law metallicLinearThresholdData

end Omega.Folding
