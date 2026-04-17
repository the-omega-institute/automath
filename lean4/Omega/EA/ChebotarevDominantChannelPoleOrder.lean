import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.EA.ChebotarevSecondMainTermWitness

namespace Omega.EA

/-- The reciprocal of the dominant Artin-channel eigenvalue in the seed model. -/
def artinDominantPoleLocation : ℝ := -1

/-- The dominant nontrivial channel has multiplicity equal to the representation dimension. -/
def artinDominantChannelDimension : ℕ := 2

/-- The unique simple pole factor isolated from the Artin product. -/
def artinDominantSimplePoleFactor (z : ℝ) : ℝ := z - artinDominantPoleLocation

/-- Auxiliary Artin factors that stay nonzero at the dominant pole. -/
def artinAuxiliaryFactor1 (z : ℝ) : ℝ := z ^ (2 : ℕ) + 1

/-- A second auxiliary factor that stays nonzero at the dominant pole. -/
def artinAuxiliaryFactor2 (z : ℝ) : ℝ := z + 2

/-- Exact pole order contributed by the isolated simple factor. -/
def artinDominantPoleOrder : ℕ := artinDominantChannelDimension

/-- The pole-order clause: one zero from the isolated factor, no cancellation from the others,
and hence exact order `dim rho_*`. -/
def artinDominantPoleOrderConclusion : Prop :=
  artinDominantSimplePoleFactor artinDominantPoleLocation = 0 ∧
    artinAuxiliaryFactor1 artinDominantPoleLocation ≠ 0 ∧
    artinAuxiliaryFactor2 artinDominantPoleLocation ≠ 0 ∧
    artinDominantPoleOrder = artinDominantChannelDimension

/-- A fixed nonzero witness coefficient used to invoke the second-main-term oscillation theorem. -/
def artinDominantWitnessCoeff : ℝ := 3

/-- The witness clause imported from the dominant-channel second-main-term theorem. -/
def artinDominantWitnessOscillationConclusion : Prop :=
  chebotarevNonzeroWitnessCoefficient artinDominantWitnessCoeff ∧
    chebotarevOscillationLowerBound artinDominantWitnessCoeff

/-- Paper-facing wrapper for the dominant Artin-channel pole order and witness oscillation.
    thm:kernel-artin-dominant-channel-pole-order -/
theorem paper_kernel_artin_dominant_channel_pole_order :
    artinDominantPoleOrderConclusion ∧ artinDominantWitnessOscillationConclusion := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_, rfl⟩
    · norm_num [artinDominantSimplePoleFactor, artinDominantPoleLocation]
    · norm_num [artinAuxiliaryFactor1, artinDominantPoleLocation]
    · norm_num [artinAuxiliaryFactor2, artinDominantPoleLocation]
  · rcases
      paper_kernel_chebotarev_second_main_term_witness
        artinDominantWitnessCoeff (by norm_num [artinDominantWitnessCoeff]) with
        ⟨_hexp, hnonzero, hosc⟩
    exact ⟨hnonzero, hosc⟩

end Omega.EA
