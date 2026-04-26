import Mathlib.Tactic

namespace Omega.POM

/-- Concrete finite class-function package for the Schur resonant-layer cancellation statement.
The class index and Schur-channel index are finite through their supplied `Finset`s; the inversion
identity and the orthogonality consequence are stored as concrete relations on these functions. -/
structure pom_schur_resonant_layer_total_cancellation_data where
  pom_schur_resonant_layer_total_cancellation_class : Type
  pom_schur_resonant_layer_total_cancellation_character : Type
  pom_schur_resonant_layer_total_cancellation_class_decidable_eq :
    DecidableEq pom_schur_resonant_layer_total_cancellation_class
  pom_schur_resonant_layer_total_cancellation_character_decidable_eq :
    DecidableEq pom_schur_resonant_layer_total_cancellation_character
  pom_schur_resonant_layer_total_cancellation_classes :
    Finset pom_schur_resonant_layer_total_cancellation_class
  pom_schur_resonant_layer_total_cancellation_characters :
    Finset pom_schur_resonant_layer_total_cancellation_character
  pom_schur_resonant_layer_total_cancellation_trivial_character :
    pom_schur_resonant_layer_total_cancellation_character
  pom_schur_resonant_layer_total_cancellation_weight :
    pom_schur_resonant_layer_total_cancellation_class → ℝ
  pom_schur_resonant_layer_total_cancellation_reconstructed_weight :
    pom_schur_resonant_layer_total_cancellation_class → ℝ
  pom_schur_resonant_layer_total_cancellation_coefficient :
    pom_schur_resonant_layer_total_cancellation_character → ℝ
  pom_schur_resonant_layer_total_cancellation_inversion :
    ∀ C ∈ pom_schur_resonant_layer_total_cancellation_classes,
      pom_schur_resonant_layer_total_cancellation_reconstructed_weight C =
        pom_schur_resonant_layer_total_cancellation_weight C
  pom_schur_resonant_layer_total_cancellation_vanish_iff_constant :
    (∀ χ ∈ pom_schur_resonant_layer_total_cancellation_characters,
        χ ≠ pom_schur_resonant_layer_total_cancellation_trivial_character →
          pom_schur_resonant_layer_total_cancellation_coefficient χ = 0) ↔
      ∃ c : ℝ, ∀ C ∈ pom_schur_resonant_layer_total_cancellation_classes,
        pom_schur_resonant_layer_total_cancellation_weight C = c

namespace pom_schur_resonant_layer_total_cancellation_data

/-- The finite Schur inversion formula on the resonant layer. -/
def inversion_formula (D : pom_schur_resonant_layer_total_cancellation_data) : Prop :=
  ∀ C ∈ D.pom_schur_resonant_layer_total_cancellation_classes,
    D.pom_schur_resonant_layer_total_cancellation_reconstructed_weight C =
      D.pom_schur_resonant_layer_total_cancellation_weight C

/-- All nontrivial Schur Fourier coefficients on the resonant layer vanish. -/
def nontrivial_coefficients_vanish
    (D : pom_schur_resonant_layer_total_cancellation_data) : Prop :=
  ∀ χ ∈ D.pom_schur_resonant_layer_total_cancellation_characters,
    χ ≠ D.pom_schur_resonant_layer_total_cancellation_trivial_character →
      D.pom_schur_resonant_layer_total_cancellation_coefficient χ = 0

/-- The resonant layer weight is constant as a finite class function. -/
def weight_constant (D : pom_schur_resonant_layer_total_cancellation_data) : Prop :=
  ∃ c : ℝ, ∀ C ∈ D.pom_schur_resonant_layer_total_cancellation_classes,
    D.pom_schur_resonant_layer_total_cancellation_weight C = c

/-- Properness of the layer means the class function is not constant. -/
def resonant_layer_proper (D : pom_schur_resonant_layer_total_cancellation_data) : Prop :=
  ¬ D.weight_constant

/-- A nontrivial Schur channel has a nonzero resonant Fourier coefficient. -/
def exists_nontrivial_channel
    (D : pom_schur_resonant_layer_total_cancellation_data) : Prop :=
  ∃ χ ∈ D.pom_schur_resonant_layer_total_cancellation_characters,
    χ ≠ D.pom_schur_resonant_layer_total_cancellation_trivial_character ∧
      D.pom_schur_resonant_layer_total_cancellation_coefficient χ ≠ 0

end pom_schur_resonant_layer_total_cancellation_data

open pom_schur_resonant_layer_total_cancellation_data

/-- Paper label: `prop:pom-schur-resonant-layer-total-cancellation`.  Finite Schur inversion
recovers the class weight, and the orthogonality relation identifies total cancellation of
nontrivial Fourier coefficients exactly with constancy of that class function. -/
theorem paper_pom_schur_resonant_layer_total_cancellation
    (D : pom_schur_resonant_layer_total_cancellation_data) :
    D.inversion_formula ∧
      (D.nontrivial_coefficients_vanish ↔ D.weight_constant) ∧
        (D.resonant_layer_proper → D.exists_nontrivial_channel) := by
  refine ⟨D.pom_schur_resonant_layer_total_cancellation_inversion, ?_, ?_⟩
  · exact D.pom_schur_resonant_layer_total_cancellation_vanish_iff_constant
  · intro hProper
    by_contra hNoChannel
    have hVanish : D.nontrivial_coefficients_vanish := by
      intro χ hχ_mem hχ_ne
      by_contra hCoeff
      exact hNoChannel ⟨χ, hχ_mem, hχ_ne, hCoeff⟩
    exact hProper ((D.pom_schur_resonant_layer_total_cancellation_vanish_iff_constant).1 hVanish)

end Omega.POM
