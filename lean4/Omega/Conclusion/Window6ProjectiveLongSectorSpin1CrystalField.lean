import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- Diagonal `3 × 3` operators represented on the projective long-sector basis. -/
def thm_conclusion_window6_projective_long_sector_spin1_crystal_field_diag
    (a b c : ℝ) : Fin 3 → ℝ
  | 0 => a
  | 1 => b
  | _ => c

/-- The ordered projective long-sector operator `diag(2^q, 3^q, 4^q)`. -/
def thm_conclusion_window6_projective_long_sector_spin1_crystal_field_operator
    (q : ℝ) : Fin 3 → ℝ :=
  thm_conclusion_window6_projective_long_sector_spin1_crystal_field_diag
    ((2 : ℝ) ^ q) ((3 : ℝ) ^ q) ((4 : ℝ) ^ q)

/-- The identity operator on the ordered qutrit basis. -/
def thm_conclusion_window6_projective_long_sector_spin1_crystal_field_I :
    Fin 3 → ℝ :=
  thm_conclusion_window6_projective_long_sector_spin1_crystal_field_diag 1 1 1

/-- The spin-`1` Cartan generator `J_z = diag(-1,0,1)`. -/
def thm_conclusion_window6_projective_long_sector_spin1_crystal_field_Jz :
    Fin 3 → ℝ :=
  thm_conclusion_window6_projective_long_sector_spin1_crystal_field_diag (-1) 0 1

/-- The quadratic Cartan term `J_z^2 = diag(1,0,1)`. -/
def thm_conclusion_window6_projective_long_sector_spin1_crystal_field_JzSq :
    Fin 3 → ℝ :=
  thm_conclusion_window6_projective_long_sector_spin1_crystal_field_diag 1 0 1

/-- The scalar coefficient in the `I + J_z + J_z^2` decomposition. -/
def thm_conclusion_window6_projective_long_sector_spin1_crystal_field_A (q : ℝ) : ℝ :=
  (3 : ℝ) ^ q

/-- The linear Cartan coefficient. -/
def thm_conclusion_window6_projective_long_sector_spin1_crystal_field_B (q : ℝ) : ℝ :=
  (((4 : ℝ) ^ q) - (2 : ℝ) ^ q) / 2

/-- The quadratic Cartan coefficient. -/
def thm_conclusion_window6_projective_long_sector_spin1_crystal_field_C (q : ℝ) : ℝ :=
  (((2 : ℝ) ^ q) + (4 : ℝ) ^ q - 2 * (3 : ℝ) ^ q) / 2

/-- The crystal-field decomposition in the `I, J_z, J_z^2` basis. -/
def thm_conclusion_window6_projective_long_sector_spin1_crystal_field_decomposition
    (q : ℝ) : Fin 3 → ℝ :=
  thm_conclusion_window6_projective_long_sector_spin1_crystal_field_A q •
      thm_conclusion_window6_projective_long_sector_spin1_crystal_field_I +
    thm_conclusion_window6_projective_long_sector_spin1_crystal_field_B q •
      thm_conclusion_window6_projective_long_sector_spin1_crystal_field_Jz +
    thm_conclusion_window6_projective_long_sector_spin1_crystal_field_C q •
      thm_conclusion_window6_projective_long_sector_spin1_crystal_field_JzSq

/-- The Zeeman specialization `3 I_3 + J_z` occurring at `q = 1`. -/
def thm_conclusion_window6_projective_long_sector_spin1_crystal_field_zeeman :
    Fin 3 → ℝ :=
  (3 : ℝ) • thm_conclusion_window6_projective_long_sector_spin1_crystal_field_I +
    (1 : ℝ) • thm_conclusion_window6_projective_long_sector_spin1_crystal_field_Jz

/-- Concrete proposition packaging the diagonal decomposition and the `q = 1` Zeeman reduction. -/
def thm_conclusion_window6_projective_long_sector_spin1_crystal_field_statement
    (q : ℝ) : Prop :=
  thm_conclusion_window6_projective_long_sector_spin1_crystal_field_decomposition q =
      thm_conclusion_window6_projective_long_sector_spin1_crystal_field_operator q ∧
    thm_conclusion_window6_projective_long_sector_spin1_crystal_field_A 1 = 3 ∧
    thm_conclusion_window6_projective_long_sector_spin1_crystal_field_B 1 = 1 ∧
    thm_conclusion_window6_projective_long_sector_spin1_crystal_field_C 1 = 0 ∧
    thm_conclusion_window6_projective_long_sector_spin1_crystal_field_operator 1 =
      thm_conclusion_window6_projective_long_sector_spin1_crystal_field_zeeman

lemma thm_conclusion_window6_projective_long_sector_spin1_crystal_field_decomposition_eq
    (q : ℝ) :
    thm_conclusion_window6_projective_long_sector_spin1_crystal_field_decomposition q =
      thm_conclusion_window6_projective_long_sector_spin1_crystal_field_operator q := by
  funext i
  fin_cases i <;>
    simp [thm_conclusion_window6_projective_long_sector_spin1_crystal_field_decomposition,
      thm_conclusion_window6_projective_long_sector_spin1_crystal_field_operator,
      thm_conclusion_window6_projective_long_sector_spin1_crystal_field_diag,
      thm_conclusion_window6_projective_long_sector_spin1_crystal_field_I,
      thm_conclusion_window6_projective_long_sector_spin1_crystal_field_Jz,
      thm_conclusion_window6_projective_long_sector_spin1_crystal_field_JzSq,
      thm_conclusion_window6_projective_long_sector_spin1_crystal_field_A,
      thm_conclusion_window6_projective_long_sector_spin1_crystal_field_B,
      thm_conclusion_window6_projective_long_sector_spin1_crystal_field_C] <;>
    ring

lemma thm_conclusion_window6_projective_long_sector_spin1_crystal_field_zeeman_eq :
    thm_conclusion_window6_projective_long_sector_spin1_crystal_field_operator 1 =
      thm_conclusion_window6_projective_long_sector_spin1_crystal_field_zeeman := by
  funext i
  fin_cases i <;>
    norm_num [thm_conclusion_window6_projective_long_sector_spin1_crystal_field_operator,
      thm_conclusion_window6_projective_long_sector_spin1_crystal_field_diag,
      thm_conclusion_window6_projective_long_sector_spin1_crystal_field_zeeman,
      thm_conclusion_window6_projective_long_sector_spin1_crystal_field_I,
      thm_conclusion_window6_projective_long_sector_spin1_crystal_field_Jz, Real.rpow_one]

theorem thm_conclusion_window6_projective_long_sector_spin1_crystal_field_verified
    (q : ℝ) :
    thm_conclusion_window6_projective_long_sector_spin1_crystal_field_statement q := by
  refine ⟨thm_conclusion_window6_projective_long_sector_spin1_crystal_field_decomposition_eq q,
    ?_, ?_, ?_, thm_conclusion_window6_projective_long_sector_spin1_crystal_field_zeeman_eq⟩
  · simp [thm_conclusion_window6_projective_long_sector_spin1_crystal_field_A, Real.rpow_one]
  · norm_num [thm_conclusion_window6_projective_long_sector_spin1_crystal_field_B, Real.rpow_one]
  · norm_num [thm_conclusion_window6_projective_long_sector_spin1_crystal_field_C, Real.rpow_one]

/-- Paper label: `thm:conclusion-window6-projective-long-sector-spin1-crystal-field`. -/
def paper_conclusion_window6_projective_long_sector_spin1_crystal_field (q : Real) : Prop := by
  exact thm_conclusion_window6_projective_long_sector_spin1_crystal_field_statement q

end

end Omega.Conclusion
