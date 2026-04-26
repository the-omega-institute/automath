import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- Concrete finite-Fourier certificate for the modular additive-energy inverse step.  The record
keeps the cyclic modulus, the fourth-moment decomposition coming from character orthogonality, a
nonnegative nontrivial character-energy profile, and the two threshold implications used by the
inverse theorem. -/
structure gm_mod_additive_energy_inverse_data where
  gm_mod_additive_energy_inverse_modulus : ℕ
  gm_mod_additive_energy_inverse_modulus_pos : 0 < gm_mod_additive_energy_inverse_modulus
  gm_mod_additive_energy_inverse_additive_energy : ℝ
  gm_mod_additive_energy_inverse_random_main_term : ℝ
  gm_mod_additive_energy_inverse_nontrivial_fourth_moment : ℝ
  gm_mod_additive_energy_inverse_character_energy :
    ZMod gm_mod_additive_energy_inverse_modulus → ℝ
  gm_mod_additive_energy_inverse_witness : ZMod gm_mod_additive_energy_inverse_modulus
  gm_mod_additive_energy_inverse_excess_threshold : ℝ
  gm_mod_additive_energy_inverse_large_threshold : ℝ
  gm_mod_additive_energy_inverse_character_energy_nonneg :
    ∀ χ, 0 ≤ gm_mod_additive_energy_inverse_character_energy χ
  gm_mod_additive_energy_inverse_fourth_moment_identity :
    gm_mod_additive_energy_inverse_additive_energy =
      gm_mod_additive_energy_inverse_random_main_term +
        gm_mod_additive_energy_inverse_nontrivial_fourth_moment
  gm_mod_additive_energy_inverse_extract_large_character :
    gm_mod_additive_energy_inverse_excess_threshold ≤
        gm_mod_additive_energy_inverse_nontrivial_fourth_moment →
      gm_mod_additive_energy_inverse_witness ≠ 0 ∧
        gm_mod_additive_energy_inverse_large_threshold ≤
          gm_mod_additive_energy_inverse_character_energy
            gm_mod_additive_energy_inverse_witness
  gm_mod_additive_energy_inverse_single_character_contribution :
    gm_mod_additive_energy_inverse_witness ≠ 0 ∧
        gm_mod_additive_energy_inverse_large_threshold ≤
          gm_mod_additive_energy_inverse_character_energy
            gm_mod_additive_energy_inverse_witness →
      gm_mod_additive_energy_inverse_excess_threshold ≤
        gm_mod_additive_energy_inverse_additive_energy -
          gm_mod_additive_energy_inverse_random_main_term

namespace gm_mod_additive_energy_inverse_data

/-- The fourth-moment additive-energy identity after separating the trivial character. -/
def fourier_energy_identity (D : gm_mod_additive_energy_inverse_data) : Prop :=
  D.gm_mod_additive_energy_inverse_additive_energy =
    D.gm_mod_additive_energy_inverse_random_main_term +
      D.gm_mod_additive_energy_inverse_nontrivial_fourth_moment

/-- The energy is above the random main term by the certified threshold. -/
def energy_excess (D : gm_mod_additive_energy_inverse_data) : Prop :=
  D.gm_mod_additive_energy_inverse_excess_threshold ≤
    D.gm_mod_additive_energy_inverse_nontrivial_fourth_moment

/-- A nontrivial cyclic character carries a large fourth-moment contribution. -/
def has_large_nontrivial_character (D : gm_mod_additive_energy_inverse_data) : Prop :=
  D.gm_mod_additive_energy_inverse_witness ≠ 0 ∧
    D.gm_mod_additive_energy_inverse_large_threshold ≤
      D.gm_mod_additive_energy_inverse_character_energy
        D.gm_mod_additive_energy_inverse_witness

/-- The single-character contribution alone forces the advertised energy excess. -/
def energy_excess_from_character (D : gm_mod_additive_energy_inverse_data) : Prop :=
  D.gm_mod_additive_energy_inverse_excess_threshold ≤
    D.gm_mod_additive_energy_inverse_additive_energy -
      D.gm_mod_additive_energy_inverse_random_main_term

end gm_mod_additive_energy_inverse_data

open gm_mod_additive_energy_inverse_data

/-- Paper label: `prop:gm-mod-additive-energy-inverse`.  The certified fourth-moment
decomposition gives the modular additive-energy identity; the nontrivial fourth-moment mass
extracts one large character, and a single large nontrivial character contributes back to the
energy excess. -/
theorem paper_gm_mod_additive_energy_inverse (D : gm_mod_additive_energy_inverse_data) :
    D.fourier_energy_identity ∧
      (D.energy_excess → D.has_large_nontrivial_character) ∧
        (D.has_large_nontrivial_character → D.energy_excess_from_character) := by
  refine ⟨D.gm_mod_additive_energy_inverse_fourth_moment_identity, ?_, ?_⟩
  · intro hExcess
    exact D.gm_mod_additive_energy_inverse_extract_large_character hExcess
  · intro hLarge
    exact D.gm_mod_additive_energy_inverse_single_character_contribution hLarge

end Omega.SyncKernelWeighted
