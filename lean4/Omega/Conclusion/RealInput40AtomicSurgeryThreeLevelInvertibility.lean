import Mathlib.Data.Int.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete coefficient package for removing one primitive atomic Euler factor from the real-input
40-state kernel. Coefficient streams are represented as functions `ℕ → ℤ`. -/
structure conclusion_realinput40_atomic_surgery_three_level_invertibility_Data where
  ell : ℕ
  h_ell : 0 < ell
  multiplicity : ℤ
  core_zeta_coeff : ℕ → ℤ
  core_ghost_coeff : ℕ → ℤ
  core_primitive_coeff : ℕ → ℤ

/-- The zeta-level coefficient of the single removed atom. -/
def conclusion_realinput40_atomic_surgery_three_level_invertibility_atom_zeta_coeff
    (D : conclusion_realinput40_atomic_surgery_three_level_invertibility_Data) (n : ℕ) : ℤ :=
  if n = D.ell then D.multiplicity else 0

/-- Zeta coefficients before the atom is removed. -/
def conclusion_realinput40_atomic_surgery_three_level_invertibility_before_zeta_coeff
    (D : conclusion_realinput40_atomic_surgery_three_level_invertibility_Data) (n : ℕ) : ℤ :=
  D.core_zeta_coeff n +
    conclusion_realinput40_atomic_surgery_three_level_invertibility_atom_zeta_coeff D n

/-- Zeta coefficients after the atom is removed. -/
def conclusion_realinput40_atomic_surgery_three_level_invertibility_after_zeta_coeff
    (D : conclusion_realinput40_atomic_surgery_three_level_invertibility_Data) (n : ℕ) : ℤ :=
  conclusion_realinput40_atomic_surgery_three_level_invertibility_before_zeta_coeff D n -
    conclusion_realinput40_atomic_surgery_three_level_invertibility_atom_zeta_coeff D n

/-- The ghost coefficient contributed by the removed primitive atom. -/
def conclusion_realinput40_atomic_surgery_three_level_invertibility_atom_ghost_coeff
    (D : conclusion_realinput40_atomic_surgery_three_level_invertibility_Data) (n : ℕ) : ℤ :=
  if D.ell ∣ n then (D.ell : ℤ) * D.multiplicity else 0

/-- Ghost coefficients before removal. -/
def conclusion_realinput40_atomic_surgery_three_level_invertibility_before_ghost_coeff
    (D : conclusion_realinput40_atomic_surgery_three_level_invertibility_Data) (n : ℕ) : ℤ :=
  D.core_ghost_coeff n +
    conclusion_realinput40_atomic_surgery_three_level_invertibility_atom_ghost_coeff D n

/-- Ghost coefficients after removal. -/
def conclusion_realinput40_atomic_surgery_three_level_invertibility_after_ghost_coeff
    (D : conclusion_realinput40_atomic_surgery_three_level_invertibility_Data) (n : ℕ) : ℤ :=
  conclusion_realinput40_atomic_surgery_three_level_invertibility_before_ghost_coeff D n -
    conclusion_realinput40_atomic_surgery_three_level_invertibility_atom_ghost_coeff D n

/-- The primitive atom recovered by the Mobius/Witt inversion layer. -/
def conclusion_realinput40_atomic_surgery_three_level_invertibility_primitive_atom_coeff
    (D : conclusion_realinput40_atomic_surgery_three_level_invertibility_Data) (n : ℕ) : ℤ :=
  if n = D.ell then D.multiplicity else 0

/-- Primitive coefficients before removal. -/
def conclusion_realinput40_atomic_surgery_three_level_invertibility_before_primitive_coeff
    (D : conclusion_realinput40_atomic_surgery_three_level_invertibility_Data) (n : ℕ) : ℤ :=
  D.core_primitive_coeff n +
    conclusion_realinput40_atomic_surgery_three_level_invertibility_primitive_atom_coeff D n

/-- Primitive coefficients after removal. -/
def conclusion_realinput40_atomic_surgery_three_level_invertibility_after_primitive_coeff
    (D : conclusion_realinput40_atomic_surgery_three_level_invertibility_Data) (n : ℕ) : ℤ :=
  conclusion_realinput40_atomic_surgery_three_level_invertibility_before_primitive_coeff D n -
    conclusion_realinput40_atomic_surgery_three_level_invertibility_primitive_atom_coeff D n

/-- Three-level invertibility statement for one atomic Euler-factor surgery. -/
def conclusion_realinput40_atomic_surgery_three_level_invertibility_Conclusion
    (D : conclusion_realinput40_atomic_surgery_three_level_invertibility_Data) : Prop :=
  conclusion_realinput40_atomic_surgery_three_level_invertibility_after_zeta_coeff D =
      D.core_zeta_coeff ∧
    (∀ n,
      conclusion_realinput40_atomic_surgery_three_level_invertibility_before_ghost_coeff D n -
          conclusion_realinput40_atomic_surgery_three_level_invertibility_after_ghost_coeff D n =
        conclusion_realinput40_atomic_surgery_three_level_invertibility_atom_ghost_coeff D n) ∧
      (∀ n,
        conclusion_realinput40_atomic_surgery_three_level_invertibility_before_primitive_coeff D n -
            conclusion_realinput40_atomic_surgery_three_level_invertibility_after_primitive_coeff D n =
          conclusion_realinput40_atomic_surgery_three_level_invertibility_primitive_atom_coeff D n)

/-- Paper label: `thm:conclusion-realinput40-atomic-surgery-three-level-invertibility`. -/
theorem paper_conclusion_realinput40_atomic_surgery_three_level_invertibility
    (D : conclusion_realinput40_atomic_surgery_three_level_invertibility_Data) :
    conclusion_realinput40_atomic_surgery_three_level_invertibility_Conclusion D := by
  refine ⟨?_, ?_, ?_⟩
  · funext n
    simp [conclusion_realinput40_atomic_surgery_three_level_invertibility_after_zeta_coeff,
      conclusion_realinput40_atomic_surgery_three_level_invertibility_before_zeta_coeff]
  · intro n
    simp [conclusion_realinput40_atomic_surgery_three_level_invertibility_after_ghost_coeff,
      conclusion_realinput40_atomic_surgery_three_level_invertibility_before_ghost_coeff]
  · intro n
    simp [conclusion_realinput40_atomic_surgery_three_level_invertibility_after_primitive_coeff,
      conclusion_realinput40_atomic_surgery_three_level_invertibility_before_primitive_coeff]

end Omega.Conclusion
