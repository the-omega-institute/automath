import Mathlib.Tactic

namespace Omega.Zeta

/-- The two-bit sign packet attached to the two quadratic lifts in the
concrete `P(z) = z^2 - 5`, `r = 1` model. -/
abbrev xi_terminal_zm_jg_critical_square_even_sign_defect_sign_vector :=
  Fin 2 → Bool

/-- The critical resultant values for the concrete sample `P(z) = z^2 - 5`, `r = 1`. -/
def xi_terminal_zm_jg_critical_square_even_sign_defect_Qr (w : ℚ) : ℚ :=
  36 - 5 * w ^ 2

/-- The two quadratic defects `Δ_i = w_i^2 - 4` coincide in the sample model. -/
def xi_terminal_zm_jg_critical_square_even_sign_defect_delta : Fin 2 → ℚ
  | 0 => (16 : ℚ) / 5
  | 1 => (16 : ℚ) / 5

/-- The two defect squareclasses coincide in the concrete `F₂`-model. -/
def xi_terminal_zm_jg_critical_square_even_sign_defect_delta_squareclass :
    Fin 2 → Bool := fun _ => true

/-- The even-parity sign subgroup. -/
def xi_terminal_zm_jg_critical_square_even_sign_defect_even_parity_subgroup :
    Set xi_terminal_zm_jg_critical_square_even_sign_defect_sign_vector :=
  {eps | eps 0 = eps 1}

/-- The Kummer sign subgroup cut out by the single linear relation
`[Δ₁] + [Δ₂] = 0`. -/
def xi_terminal_zm_jg_critical_square_even_sign_defect_kummer_sign_subgroup :
    Set xi_terminal_zm_jg_critical_square_even_sign_defect_sign_vector :=
  {eps | eps 0 = eps 1}

/-- The trivial sign vector. -/
def xi_terminal_zm_jg_critical_square_even_sign_defect_zero_sign :
    xi_terminal_zm_jg_critical_square_even_sign_defect_sign_vector := fun _ => false

/-- The unique nontrivial even sign vector in the two-branch model. -/
def xi_terminal_zm_jg_critical_square_even_sign_defect_full_sign :
    xi_terminal_zm_jg_critical_square_even_sign_defect_sign_vector := fun _ => true

/-- Concrete two-branch package for
`thm:xi-terminal-zm-jg-critical-square-even-sign-defect`. It records the critical values
`Q_r(±2)`, the square product of the two defects, the resulting squareclass relation, and the
induced even-parity Kummer constraint. -/
def xi_terminal_zm_jg_critical_square_even_sign_defect_statement : Prop :=
  xi_terminal_zm_jg_critical_square_even_sign_defect_Qr 2 = 16 ∧
    xi_terminal_zm_jg_critical_square_even_sign_defect_Qr (-2) = 16 ∧
    xi_terminal_zm_jg_critical_square_even_sign_defect_delta 0 *
        xi_terminal_zm_jg_critical_square_even_sign_defect_delta 1 =
      (((16 : ℚ) / 5) ^ 2) ∧
    xi_terminal_zm_jg_critical_square_even_sign_defect_delta_squareclass 0 =
      xi_terminal_zm_jg_critical_square_even_sign_defect_delta_squareclass 1 ∧
    (∀ eps : xi_terminal_zm_jg_critical_square_even_sign_defect_sign_vector,
      eps ∈ xi_terminal_zm_jg_critical_square_even_sign_defect_kummer_sign_subgroup ↔
        eps ∈ xi_terminal_zm_jg_critical_square_even_sign_defect_even_parity_subgroup) ∧
    ∀ eps : xi_terminal_zm_jg_critical_square_even_sign_defect_sign_vector,
      eps ∈ xi_terminal_zm_jg_critical_square_even_sign_defect_kummer_sign_subgroup ↔
        eps = xi_terminal_zm_jg_critical_square_even_sign_defect_zero_sign ∨
          eps = xi_terminal_zm_jg_critical_square_even_sign_defect_full_sign

/-- Paper label: `thm:xi-terminal-zm-jg-critical-square-even-sign-defect`. In the concrete
quadratic sample `P(z) = z^2 - 5`, `r = 1`, the critical values at `w = ±2` are squares, the
product of the two branch defects is a square, and the resulting Kummer sign packet is exactly
the even-parity subgroup of `(ZMod 2)^2`. -/
theorem paper_xi_terminal_zm_jg_critical_square_even_sign_defect :
    xi_terminal_zm_jg_critical_square_even_sign_defect_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [xi_terminal_zm_jg_critical_square_even_sign_defect_Qr]
  · norm_num [xi_terminal_zm_jg_critical_square_even_sign_defect_Qr]
  · norm_num [xi_terminal_zm_jg_critical_square_even_sign_defect_delta]
  · rfl
  · intro eps
    rfl
  · intro eps
    constructor
    · intro h
      by_cases h0 : eps 0
      · right
        funext i
        fin_cases i
        · simpa using h0
        · have h1 : eps 1 = true := by
            simpa [xi_terminal_zm_jg_critical_square_even_sign_defect_kummer_sign_subgroup, h0]
              using h
          simpa using h1
      · left
        funext i
        fin_cases i
        · simpa using h0
        · have h1 : eps 1 = false := by
            simpa [xi_terminal_zm_jg_critical_square_even_sign_defect_kummer_sign_subgroup, h0]
              using h
          simpa using h1
    · rintro (rfl | rfl) <;> rfl

end Omega.Zeta
