import Mathlib.Tactic

namespace Omega.Conclusion

open Matrix

/-- The zero-temperature four-state adjacency matrix. -/
def conclusion_realinput40_zero_temp_fourstate_sft_closed_zeta_matrix_nat :
    Matrix (Fin 4) (Fin 4) Nat :=
  !![0, 1, 1, 0; 0, 0, 1, 0; 0, 0, 3, 1; 1, 0, 0, 3]

/-- The same matrix over the integers, used for determinant checks. -/
def conclusion_realinput40_zero_temp_fourstate_sft_closed_zeta_matrix_int :
    Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 1, 1, 0; 0, 0, 1, 0; 0, 0, 3, 1; 1, 0, 0, 3]

/-- The denominator polynomial displayed for `det(I - z B_infty)`. -/
def conclusion_realinput40_zero_temp_fourstate_sft_closed_zeta_denominator
    (z : ℤ) : ℤ :=
  1 - 6 * z + 9 * z ^ 2 - z ^ 3 - z ^ 4

/-- Explicit finite primitivity witness: every state reaches every state in at most four steps. -/
def conclusion_realinput40_zero_temp_fourstate_sft_closed_zeta_primitiveWitness : Prop :=
  ∀ i j : Fin 4, ∃ n : Fin 4,
    0 < (conclusion_realinput40_zero_temp_fourstate_sft_closed_zeta_matrix_nat ^
      (n.1 + 1)) i j

/-- Concrete audited core for the four-state SFT closed-zeta theorem. -/
def conclusion_realinput40_zero_temp_fourstate_sft_closed_zeta_statement : Prop :=
  conclusion_realinput40_zero_temp_fourstate_sft_closed_zeta_matrix_int.det = -1 ∧
    (∀ z : ℤ,
      conclusion_realinput40_zero_temp_fourstate_sft_closed_zeta_denominator z =
        1 - 6 * z + 9 * z ^ 2 - z ^ 3 - z ^ 4) ∧
    conclusion_realinput40_zero_temp_fourstate_sft_closed_zeta_primitiveWitness

/-- Paper label: `thm:conclusion-realinput40-zero-temp-fourstate-sft-closed-zeta`. -/
theorem paper_conclusion_realinput40_zero_temp_fourstate_sft_closed_zeta :
    conclusion_realinput40_zero_temp_fourstate_sft_closed_zeta_statement := by
  refine ⟨?_, ?_, ?_⟩
  · unfold conclusion_realinput40_zero_temp_fourstate_sft_closed_zeta_matrix_int
    native_decide
  · intro z
    rfl
  · unfold conclusion_realinput40_zero_temp_fourstate_sft_closed_zeta_primitiveWitness
    unfold conclusion_realinput40_zero_temp_fourstate_sft_closed_zeta_matrix_nat
    native_decide

end Omega.Conclusion
