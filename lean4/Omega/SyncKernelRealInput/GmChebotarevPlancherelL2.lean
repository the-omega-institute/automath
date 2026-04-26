import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

open scoped BigOperators

noncomputable section

/-- Finite character-sum data for the Chebotarev--Plancherel `L²` estimate. The character
index is `Fin characterCard`; in applications this is the nontrivial part of the finite
abelian dual after removing the trivial character. -/
structure gm_chebotarev_plancherel_l2_data where
  gm_chebotarev_plancherel_l2_characterCard : ℕ
  gm_chebotarev_plancherel_l2_length : ℕ
  gm_chebotarev_plancherel_l2_C : ℝ
  gm_chebotarev_plancherel_l2_theta : ℝ
  gm_chebotarev_plancherel_l2_deviation : ℝ
  gm_chebotarev_plancherel_l2_twistedSum :
    Fin gm_chebotarev_plancherel_l2_characterCard → ℂ
  gm_chebotarev_plancherel_l2_plancherel_orthogonality :
    gm_chebotarev_plancherel_l2_deviation =
      ∑ χ : Fin gm_chebotarev_plancherel_l2_characterCard,
        ‖gm_chebotarev_plancherel_l2_twistedSum χ‖ ^ 2
  gm_chebotarev_plancherel_l2_twisted_spectral_radius :
    ∀ χ : Fin gm_chebotarev_plancherel_l2_characterCard,
      ‖gm_chebotarev_plancherel_l2_twistedSum χ‖ ^ 2 ≤
        gm_chebotarev_plancherel_l2_C ^ 2 *
          gm_chebotarev_plancherel_l2_theta ^
            (2 * gm_chebotarev_plancherel_l2_length)

/-- The Plancherel-side sum of squared twisted character sums. -/
def gm_chebotarev_plancherel_l2_twistedEnergy
    (D : gm_chebotarev_plancherel_l2_data) : ℝ :=
  ∑ χ : Fin D.gm_chebotarev_plancherel_l2_characterCard,
    ‖D.gm_chebotarev_plancherel_l2_twistedSum χ‖ ^ 2

/-- The uniform spectral-gap right-hand side after summing over nontrivial characters. -/
def gm_chebotarev_plancherel_l2_gapBound
    (D : gm_chebotarev_plancherel_l2_data) : ℝ :=
  D.gm_chebotarev_plancherel_l2_characterCard *
    (D.gm_chebotarev_plancherel_l2_C ^ 2 *
      D.gm_chebotarev_plancherel_l2_theta ^
        (2 * D.gm_chebotarev_plancherel_l2_length))

/-- Character orthogonality written as the finite Plancherel identity. -/
def gm_chebotarev_plancherel_l2_data.plancherel_identity
    (D : gm_chebotarev_plancherel_l2_data) : Prop :=
  D.gm_chebotarev_plancherel_l2_deviation =
    gm_chebotarev_plancherel_l2_twistedEnergy D

/-- Summed spectral-gap estimate for the `L²` deviation statistic. -/
def gm_chebotarev_plancherel_l2_data.spectral_gap_bound
    (D : gm_chebotarev_plancherel_l2_data) : Prop :=
  D.gm_chebotarev_plancherel_l2_deviation ≤ gm_chebotarev_plancherel_l2_gapBound D

/-- Paper label: `prop:gm-chebotarev-plancherel-l2`. -/
theorem paper_gm_chebotarev_plancherel_l2
    (D : gm_chebotarev_plancherel_l2_data) :
    D.plancherel_identity ∧ D.spectral_gap_bound := by
  constructor
  · simpa [gm_chebotarev_plancherel_l2_data.plancherel_identity,
      gm_chebotarev_plancherel_l2_twistedEnergy] using
      D.gm_chebotarev_plancherel_l2_plancherel_orthogonality
  · change
      D.gm_chebotarev_plancherel_l2_deviation ≤ gm_chebotarev_plancherel_l2_gapBound D
    rw [D.gm_chebotarev_plancherel_l2_plancherel_orthogonality]
    dsimp [gm_chebotarev_plancherel_l2_twistedEnergy, gm_chebotarev_plancherel_l2_gapBound]
    calc
      (∑ χ : Fin D.gm_chebotarev_plancherel_l2_characterCard,
          ‖D.gm_chebotarev_plancherel_l2_twistedSum χ‖ ^ 2) ≤
          ∑ _χ : Fin D.gm_chebotarev_plancherel_l2_characterCard,
            D.gm_chebotarev_plancherel_l2_C ^ 2 *
              D.gm_chebotarev_plancherel_l2_theta ^
                (2 * D.gm_chebotarev_plancherel_l2_length) := by
            exact Finset.sum_le_sum fun χ _ =>
              D.gm_chebotarev_plancherel_l2_twisted_spectral_radius χ
      _ =
          D.gm_chebotarev_plancherel_l2_characterCard *
            (D.gm_chebotarev_plancherel_l2_C ^ 2 *
              D.gm_chebotarev_plancherel_l2_theta ^
                (2 * D.gm_chebotarev_plancherel_l2_length)) := by
            simp

end

end Omega.SyncKernelRealInput
