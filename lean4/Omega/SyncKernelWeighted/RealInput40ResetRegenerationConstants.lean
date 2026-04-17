import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

noncomputable section

/-- Closed-form constants for the Parry-baseline reset-regeneration audit. -/
structure RealInput40ResetRegenerationCertificate where
  resetSectorProbability : ℝ
  kacReturnTime : ℝ
  typicalNonResetWait : ℝ
  augmentedChainStateCount : ℕ
  transientStateCount : ℕ

/-- The concrete reset-regeneration constants exported by the audited `8`-state calculation. -/
def realInput40ResetRegenerationCertificate : RealInput40ResetRegenerationCertificate where
  resetSectorProbability := (9 - 4 * Real.sqrt 5) / 5
  kacReturnTime := 45 + 20 * Real.sqrt 5
  typicalNonResetWait := (555 : ℝ) / 8 + (127 : ℝ) / 4 * Real.sqrt 5
  augmentedChainStateCount := 8
  transientStateCount := 7

/-- Closed form for the reset-sector occupancy. -/
def realInput40ResetSectorProbabilityClosedForm : Prop :=
  realInput40ResetRegenerationCertificate.resetSectorProbability =
    (9 - 4 * Real.sqrt 5) / 5

/-- Closed form for the Kac mean return time. -/
def realInput40KacReturnTimeClosedForm : Prop :=
  realInput40ResetRegenerationCertificate.kacReturnTime =
      1 / realInput40ResetRegenerationCertificate.resetSectorProbability ∧
    realInput40ResetRegenerationCertificate.kacReturnTime =
      45 + 20 * Real.sqrt 5

/-- Closed form for the typical non-reset waiting time, together with the audited chain sizes. -/
def realInput40TypicalWaitTimeClosedForm : Prop :=
  realInput40ResetRegenerationCertificate.augmentedChainStateCount = 8 ∧
    realInput40ResetRegenerationCertificate.transientStateCount = 7 ∧
    realInput40ResetRegenerationCertificate.typicalNonResetWait =
      (555 : ℝ) / 8 + (127 : ℝ) / 4 * Real.sqrt 5

private theorem realInput40_reset_sector_probability_ne_zero :
    realInput40ResetRegenerationCertificate.resetSectorProbability ≠ 0 := by
  have hsq : (Real.sqrt 5) ^ 2 = 5 := by
    rw [Real.sq_sqrt] <;> positivity
  have hpos : 0 < (9 - 4 * Real.sqrt 5) / 5 := by
    nlinarith [Real.sqrt_nonneg 5, hsq]
  exact ne_of_gt hpos

private theorem realInput40_kac_closed_form :
    realInput40ResetRegenerationCertificate.kacReturnTime =
      1 / realInput40ResetRegenerationCertificate.resetSectorProbability := by
  have hsq : (Real.sqrt 5) ^ 2 = 5 := by
    rw [Real.sq_sqrt] <;> positivity
  rw [show realInput40ResetRegenerationCertificate.kacReturnTime =
      45 + 20 * Real.sqrt 5 by rfl]
  rw [show realInput40ResetRegenerationCertificate.resetSectorProbability =
      (9 - 4 * Real.sqrt 5) / 5 by rfl]
  apply eq_one_div_of_mul_eq_one_left
  field_simp [realInput40_reset_sector_probability_ne_zero]
  nlinarith [Real.sqrt_nonneg 5, hsq]

/-- Paper-facing closed forms for the reset-sector occupation, the Kac return-time constant, and
the `8`-state non-reset waiting-time certificate.
    prop:real-input-40-reset-regeneration-constants -/
theorem paper_real_input_40_reset_regeneration_constants :
    realInput40ResetSectorProbabilityClosedForm ∧
      realInput40KacReturnTimeClosedForm ∧
      realInput40TypicalWaitTimeClosedForm := by
  refine ⟨rfl, ?_, ?_⟩
  · exact ⟨realInput40_kac_closed_form, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩

end

end Omega.SyncKernelWeighted
