import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

noncomputable section

/-- Concrete finite-character data for the modular additive-energy Plancherel identity.  The
distinguished character is the trivial one; the nontrivial error is the sum over the remaining
finite characters. -/
structure gm_modq_additive_energy_main_error_data where
  gm_modq_additive_energy_main_error_modulus : ℕ
  gm_modq_additive_energy_main_error_modulus_pos :
    0 < gm_modq_additive_energy_main_error_modulus
  gm_modq_additive_energy_main_error_character : Type*
  gm_modq_additive_energy_main_error_character_fintype :
    Fintype gm_modq_additive_energy_main_error_character
  gm_modq_additive_energy_main_error_character_decidableEq :
    DecidableEq gm_modq_additive_energy_main_error_character
  gm_modq_additive_energy_main_error_trivial_character :
    gm_modq_additive_energy_main_error_character
  gm_modq_additive_energy_main_error_cardinality : ℝ
  gm_modq_additive_energy_main_error_additive_energy : ℝ
  gm_modq_additive_energy_main_error_fourth_moment :
    gm_modq_additive_energy_main_error_character → ℝ
  gm_modq_additive_energy_main_error_error_bound : ℝ
  gm_modq_additive_energy_main_error_fourier_identity :
    gm_modq_additive_energy_main_error_additive_energy =
      (1 / (gm_modq_additive_energy_main_error_modulus : ℝ)) *
        Finset.univ.sum gm_modq_additive_energy_main_error_fourth_moment
  gm_modq_additive_energy_main_error_trivial_fourth_moment :
    gm_modq_additive_energy_main_error_fourth_moment
        gm_modq_additive_energy_main_error_trivial_character =
      gm_modq_additive_energy_main_error_cardinality ^ 4
  gm_modq_additive_energy_main_error_nontrivial_spectral_bound :
    |(1 / (gm_modq_additive_energy_main_error_modulus : ℝ)) *
        (Finset.univ.erase gm_modq_additive_energy_main_error_trivial_character).sum
          gm_modq_additive_energy_main_error_fourth_moment| ≤
      gm_modq_additive_energy_main_error_error_bound

namespace gm_modq_additive_energy_main_error_data

/-- The zero-frequency term in the fourth Plancherel expansion. -/
def gm_modq_additive_energy_main_error_main_term
    (D : gm_modq_additive_energy_main_error_data) : ℝ :=
  D.gm_modq_additive_energy_main_error_cardinality ^ 4 /
    (D.gm_modq_additive_energy_main_error_modulus : ℝ)

/-- The nontrivial-character contribution to the additive energy. -/
def gm_modq_additive_energy_main_error_nontrivial_error
    (D : gm_modq_additive_energy_main_error_data) : ℝ :=
  letI := D.gm_modq_additive_energy_main_error_character_fintype
  letI := D.gm_modq_additive_energy_main_error_character_decidableEq
  (1 / (D.gm_modq_additive_energy_main_error_modulus : ℝ)) *
    (Finset.univ.erase D.gm_modq_additive_energy_main_error_trivial_character).sum
      D.gm_modq_additive_energy_main_error_fourth_moment

/-- The published identity and spectral-gap error estimate. -/
def energy_identity_and_error (D : gm_modq_additive_energy_main_error_data) : Prop :=
  D.gm_modq_additive_energy_main_error_additive_energy =
      D.gm_modq_additive_energy_main_error_main_term +
        D.gm_modq_additive_energy_main_error_nontrivial_error ∧
    |D.gm_modq_additive_energy_main_error_nontrivial_error| ≤
      D.gm_modq_additive_energy_main_error_error_bound

end gm_modq_additive_energy_main_error_data

open gm_modq_additive_energy_main_error_data

/-- Paper label: `prop:gm-modq-additive-energy-main-error`.  Splitting the finite character sum
into the trivial character and its complement gives the main term; the supplied nontrivial
spectral estimate bounds the complementary Fourier contribution. -/
theorem paper_gm_modq_additive_energy_main_error
    (D : gm_modq_additive_energy_main_error_data) : D.energy_identity_and_error := by
  letI := D.gm_modq_additive_energy_main_error_character_fintype
  letI := D.gm_modq_additive_energy_main_error_character_decidableEq
  constructor
  · rw [gm_modq_additive_energy_main_error_data.gm_modq_additive_energy_main_error_main_term,
      gm_modq_additive_energy_main_error_data.gm_modq_additive_energy_main_error_nontrivial_error]
    rw [D.gm_modq_additive_energy_main_error_fourier_identity]
    have hsplit :
        Finset.univ.sum D.gm_modq_additive_energy_main_error_fourth_moment =
          D.gm_modq_additive_energy_main_error_fourth_moment
              D.gm_modq_additive_energy_main_error_trivial_character +
            (Finset.univ.erase D.gm_modq_additive_energy_main_error_trivial_character).sum
              D.gm_modq_additive_energy_main_error_fourth_moment := by
      simp
    rw [hsplit, D.gm_modq_additive_energy_main_error_trivial_fourth_moment]
    ring
  · change
      |(1 / (D.gm_modq_additive_energy_main_error_modulus : ℝ)) *
          (Finset.univ.erase D.gm_modq_additive_energy_main_error_trivial_character).sum
            D.gm_modq_additive_energy_main_error_fourth_moment| ≤
        D.gm_modq_additive_energy_main_error_error_bound
    exact D.gm_modq_additive_energy_main_error_nontrivial_spectral_bound

end

end Omega.SyncKernelWeighted
