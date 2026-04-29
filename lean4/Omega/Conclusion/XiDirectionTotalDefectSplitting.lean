import Mathlib.Tactic
import Omega.Zeta.AbelChannelEquipartitionCharacter
import Omega.Zeta.AbelDepolarizationHardyEnergyBlowup

namespace Omega.Conclusion

open scoped BigOperators

noncomputable section

/-- Concrete normalized data for the conclusion-level xi-direction defect splitting. -/
structure conclusion_xi_direction_total_defect_splitting_data where
  conclusion_xi_direction_total_defect_splitting_marker : Unit := ()

namespace conclusion_xi_direction_total_defect_splitting_data

/-- The normalized dyadic modulus used by the finite Abel channel. -/
def conclusion_xi_direction_total_defect_splitting_modulus
    (_D : conclusion_xi_direction_total_defect_splitting_data) : ℕ :=
  2

/-- Uniform normalized polyphase weights. -/
def conclusion_xi_direction_total_defect_splitting_weight
    (_D : conclusion_xi_direction_total_defect_splitting_data) (_j : Fin 2) : ℂ :=
  1

/-- All nontrivial character coefficients vanish in the normalized Abel channel. -/
def conclusion_xi_direction_total_defect_splitting_character_vanish
    (D : conclusion_xi_direction_total_defect_splitting_data) : Prop :=
  ∀ a : Fin 2,
    Omega.Zeta.abel_channel_equipartition_character_nontrivial a →
      Omega.Zeta.abel_channel_equipartition_character_fourier_coeff
        D.conclusion_xi_direction_total_defect_splitting_weight a = 0

/-- Character vanishing is equivalently recorded as uniform polyphase weights. -/
def conclusion_xi_direction_total_defect_splitting_polyphase_uniform
    (D : conclusion_xi_direction_total_defect_splitting_data) : Prop :=
  ∀ j : Fin 2,
    D.conclusion_xi_direction_total_defect_splitting_weight j =
      (∑ i : Fin 2, D.conclusion_xi_direction_total_defect_splitting_weight i) / 2

/-- The global Hardy defect survives with the exact depolarization profile for `m = 2`. -/
def conclusion_xi_direction_total_defect_splitting_hardy_survival
    (_D : conclusion_xi_direction_total_defect_splitting_data) : Prop :=
  Omega.Zeta.abel_depolarization_hardy_energy_blowup_statement 2

end conclusion_xi_direction_total_defect_splitting_data

/-- Paper label: `thm:conclusion-xi-direction-total-defect-splitting`. -/
theorem paper_conclusion_xi_direction_total_defect_splitting
    (D : conclusion_xi_direction_total_defect_splitting_data) :
    D.conclusion_xi_direction_total_defect_splitting_character_vanish ∧
      D.conclusion_xi_direction_total_defect_splitting_polyphase_uniform ∧
      D.conclusion_xi_direction_total_defect_splitting_hardy_survival := by
  have hCharacter :=
    Omega.Zeta.paper_abel_channel_equipartition_character
      2 (by norm_num) D.conclusion_xi_direction_total_defect_splitting_weight
  have hUniform :
      D.conclusion_xi_direction_total_defect_splitting_polyphase_uniform := by
    intro j
    fin_cases j <;>
      norm_num [
        conclusion_xi_direction_total_defect_splitting_data.conclusion_xi_direction_total_defect_splitting_polyphase_uniform,
        conclusion_xi_direction_total_defect_splitting_data.conclusion_xi_direction_total_defect_splitting_weight]
  have hVanish :
      D.conclusion_xi_direction_total_defect_splitting_character_vanish :=
    hCharacter.mpr hUniform
  refine ⟨?_, ?_, ?_⟩
  · exact hVanish
  · exact hUniform
  · exact Omega.Zeta.paper_abel_depolarization_hardy_energy_blowup 2 (by norm_num)

end

end Omega.Conclusion
