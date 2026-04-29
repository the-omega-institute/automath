import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Omega.Zeta

/-- The quadratic sign character represented by the square class of a discriminant. -/
def xi_terminal_zm_leyang_phase_resonance_discriminant_center_character_centralCharacter
    (δ : ℤ) (x : ℚ) : Prop :=
  ∃ y : ℚ, x = (δ : ℚ) * y ^ 2

/-- Equality of discriminant square classes, expressed by equality of their represented
quadratic sign characters. -/
def xi_terminal_zm_leyang_phase_resonance_discriminant_center_character_squareClassEquivalent
    (δ ε : ℤ) : Prop :=
  ∀ x : ℚ,
    xi_terminal_zm_leyang_phase_resonance_discriminant_center_character_centralCharacter δ x ↔
      xi_terminal_zm_leyang_phase_resonance_discriminant_center_character_centralCharacter ε x

/-- Concrete package for the two discriminants and their common square-class center. -/
structure xi_terminal_zm_leyang_phase_resonance_discriminant_center_character_data where
  xi_terminal_zm_leyang_phase_resonance_discriminant_center_character_leyang_discriminant : ℤ
  xi_terminal_zm_leyang_phase_resonance_discriminant_center_character_phase_discriminant : ℤ
  xi_terminal_zm_leyang_phase_resonance_discriminant_center_character_center_discriminant : ℤ
  xi_terminal_zm_leyang_phase_resonance_discriminant_center_character_leyang_center :
    xi_terminal_zm_leyang_phase_resonance_discriminant_center_character_squareClassEquivalent
      xi_terminal_zm_leyang_phase_resonance_discriminant_center_character_leyang_discriminant
      xi_terminal_zm_leyang_phase_resonance_discriminant_center_character_center_discriminant
  xi_terminal_zm_leyang_phase_resonance_discriminant_center_character_phase_center :
    xi_terminal_zm_leyang_phase_resonance_discriminant_center_character_squareClassEquivalent
      xi_terminal_zm_leyang_phase_resonance_discriminant_center_character_phase_discriminant
      xi_terminal_zm_leyang_phase_resonance_discriminant_center_character_center_discriminant

namespace xi_terminal_zm_leyang_phase_resonance_discriminant_center_character_data

/-- The two discriminants define the same quadratic extension. -/
def same_quadratic_extensions
    (D : xi_terminal_zm_leyang_phase_resonance_discriminant_center_character_data) : Prop :=
  xi_terminal_zm_leyang_phase_resonance_discriminant_center_character_squareClassEquivalent
    D.xi_terminal_zm_leyang_phase_resonance_discriminant_center_character_leyang_discriminant
    D.xi_terminal_zm_leyang_phase_resonance_discriminant_center_character_phase_discriminant

/-- The associated central sign characters coincide. -/
def same_central_character
    (D : xi_terminal_zm_leyang_phase_resonance_discriminant_center_character_data) : Prop :=
  ∀ x : ℚ,
    xi_terminal_zm_leyang_phase_resonance_discriminant_center_character_centralCharacter
        D.xi_terminal_zm_leyang_phase_resonance_discriminant_center_character_leyang_discriminant
        x ↔
      xi_terminal_zm_leyang_phase_resonance_discriminant_center_character_centralCharacter
        D.xi_terminal_zm_leyang_phase_resonance_discriminant_center_character_phase_discriminant
        x

end xi_terminal_zm_leyang_phase_resonance_discriminant_center_character_data

/-- A common discriminant square-class center identifies both quadratic sign characters. -/
theorem xi_terminal_zm_leyang_phase_resonance_discriminant_center_character_center_trans
    {δ ε κ : ℤ}
    (hδ :
      xi_terminal_zm_leyang_phase_resonance_discriminant_center_character_squareClassEquivalent
        δ κ)
    (hε :
      xi_terminal_zm_leyang_phase_resonance_discriminant_center_character_squareClassEquivalent
        ε κ) :
    xi_terminal_zm_leyang_phase_resonance_discriminant_center_character_squareClassEquivalent
      δ ε := by
  intro x
  exact (hδ x).trans (hε x).symm

/-- thm:xi-terminal-zm-leyang-phase-resonance-discriminant-center-character -/
theorem paper_xi_terminal_zm_leyang_phase_resonance_discriminant_center_character
    (D : xi_terminal_zm_leyang_phase_resonance_discriminant_center_character_data) :
    D.same_quadratic_extensions ∧ D.same_central_character := by
  have hsame :
      xi_terminal_zm_leyang_phase_resonance_discriminant_center_character_squareClassEquivalent
        D.xi_terminal_zm_leyang_phase_resonance_discriminant_center_character_leyang_discriminant
        D.xi_terminal_zm_leyang_phase_resonance_discriminant_center_character_phase_discriminant :=
    xi_terminal_zm_leyang_phase_resonance_discriminant_center_character_center_trans
      D.xi_terminal_zm_leyang_phase_resonance_discriminant_center_character_leyang_center
      D.xi_terminal_zm_leyang_phase_resonance_discriminant_center_character_phase_center
  exact ⟨hsame, hsame⟩

end Omega.Zeta
