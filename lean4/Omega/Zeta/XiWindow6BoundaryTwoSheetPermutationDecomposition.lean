import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic

namespace Omega.Zeta

/-- The three boundary base points in the window-6 two-sheet boundary model. -/
abbrev xi_window6_boundary_two_sheet_permutation_decomposition_base :=
  Fin 3

/-- The six boundary sheet points, organized as three two-point fibers. -/
abbrev xi_window6_boundary_two_sheet_permutation_decomposition_sheet :=
  xi_window6_boundary_two_sheet_permutation_decomposition_base × Bool

/-- The two-point fiber over a boundary base point. -/
def xi_window6_boundary_two_sheet_permutation_decomposition_fiber
    (i : xi_window6_boundary_two_sheet_permutation_decomposition_base) :
    Finset xi_window6_boundary_two_sheet_permutation_decomposition_sheet :=
  Finset.univ.filter fun p => p.1 = i

/-- The global fiber-swap involution. -/
def xi_window6_boundary_two_sheet_permutation_decomposition_swap
    (p : xi_window6_boundary_two_sheet_permutation_decomposition_sheet) :
    xi_window6_boundary_two_sheet_permutation_decomposition_sheet :=
  (p.1, !p.2)

/-- The natural lifted `S₃` action, permuting the three fibers and preserving sheet parity. -/
def xi_window6_boundary_two_sheet_permutation_decomposition_baseAction
    (σ : Equiv.Perm xi_window6_boundary_two_sheet_permutation_decomposition_base)
    (p : xi_window6_boundary_two_sheet_permutation_decomposition_sheet) :
    xi_window6_boundary_two_sheet_permutation_decomposition_sheet :=
  (σ p.1, p.2)

/-- The three-point permutation character of the base action. -/
def xi_window6_boundary_two_sheet_permutation_decomposition_fixedChar
    (σ : Equiv.Perm xi_window6_boundary_two_sheet_permutation_decomposition_base) : ℤ :=
  Fintype.card {i : xi_window6_boundary_two_sheet_permutation_decomposition_base // σ i = i}

/-- The trivial character on `S₃`. -/
def xi_window6_boundary_two_sheet_permutation_decomposition_trivialChar
    (_σ : Equiv.Perm xi_window6_boundary_two_sheet_permutation_decomposition_base) : ℤ :=
  1

/-- The standard character obtained by removing the invariant line from the permutation module. -/
def xi_window6_boundary_two_sheet_permutation_decomposition_standardChar
    (σ : Equiv.Perm xi_window6_boundary_two_sheet_permutation_decomposition_base) : ℤ :=
  xi_window6_boundary_two_sheet_permutation_decomposition_fixedChar σ - 1

/-- The sign character of `S₃`. -/
def xi_window6_boundary_two_sheet_permutation_decomposition_signChar
    (σ : Equiv.Perm xi_window6_boundary_two_sheet_permutation_decomposition_base) : ℤ :=
  σ.sign

/-- Integer character inner product numerator divided by `|S₃| = 6`. -/
def xi_window6_boundary_two_sheet_permutation_decomposition_characterMultiplicity
    (χ ψ : Equiv.Perm xi_window6_boundary_two_sheet_permutation_decomposition_base → ℤ) : ℤ :=
  (Finset.univ.sum fun σ => χ σ * ψ σ) / 6

/-- Concrete paper-facing statement for the two-sheet boundary permutation representation:
three two-point fibers, a fixed-point-free sheet-swap involution, the lifted `S₃` action, and
the two copies of the three-point permutation character split as `1 + Std` with no sign summand. -/
def xi_window6_boundary_two_sheet_permutation_decomposition_statement : Prop :=
  Fintype.card xi_window6_boundary_two_sheet_permutation_decomposition_sheet = 6 ∧
    (∀ i,
      (xi_window6_boundary_two_sheet_permutation_decomposition_fiber i).card = 2) ∧
    Function.Involutive xi_window6_boundary_two_sheet_permutation_decomposition_swap ∧
    (∀ p, xi_window6_boundary_two_sheet_permutation_decomposition_swap p ≠ p) ∧
    (∀ σ τ p,
      xi_window6_boundary_two_sheet_permutation_decomposition_baseAction (σ * τ) p =
        xi_window6_boundary_two_sheet_permutation_decomposition_baseAction σ
          (xi_window6_boundary_two_sheet_permutation_decomposition_baseAction τ p)) ∧
    (∀ σ,
      xi_window6_boundary_two_sheet_permutation_decomposition_fixedChar σ =
        xi_window6_boundary_two_sheet_permutation_decomposition_trivialChar σ +
          xi_window6_boundary_two_sheet_permutation_decomposition_standardChar σ) ∧
    xi_window6_boundary_two_sheet_permutation_decomposition_characterMultiplicity
      xi_window6_boundary_two_sheet_permutation_decomposition_fixedChar
      xi_window6_boundary_two_sheet_permutation_decomposition_signChar = 0 ∧
    xi_window6_boundary_two_sheet_permutation_decomposition_characterMultiplicity
      xi_window6_boundary_two_sheet_permutation_decomposition_standardChar
      xi_window6_boundary_two_sheet_permutation_decomposition_signChar = 0

private lemma xi_window6_boundary_two_sheet_permutation_decomposition_fiber_card
    (i : xi_window6_boundary_two_sheet_permutation_decomposition_base) :
    (xi_window6_boundary_two_sheet_permutation_decomposition_fiber i).card = 2 := by
  fin_cases i <;> decide

private lemma xi_window6_boundary_two_sheet_permutation_decomposition_swap_involutive :
    Function.Involutive xi_window6_boundary_two_sheet_permutation_decomposition_swap := by
  rintro ⟨i, b⟩
  cases b <;> rfl

private lemma xi_window6_boundary_two_sheet_permutation_decomposition_swap_no_fixed
    (p : xi_window6_boundary_two_sheet_permutation_decomposition_sheet) :
    xi_window6_boundary_two_sheet_permutation_decomposition_swap p ≠ p := by
  rcases p with ⟨i, b⟩
  cases b <;> simp [xi_window6_boundary_two_sheet_permutation_decomposition_swap]

private lemma xi_window6_boundary_two_sheet_permutation_decomposition_baseAction_mul
    (σ τ : Equiv.Perm xi_window6_boundary_two_sheet_permutation_decomposition_base)
    (p : xi_window6_boundary_two_sheet_permutation_decomposition_sheet) :
    xi_window6_boundary_two_sheet_permutation_decomposition_baseAction (σ * τ) p =
      xi_window6_boundary_two_sheet_permutation_decomposition_baseAction σ
        (xi_window6_boundary_two_sheet_permutation_decomposition_baseAction τ p) := by
  rfl

private lemma xi_window6_boundary_two_sheet_permutation_decomposition_fixedChar_split
    (σ : Equiv.Perm xi_window6_boundary_two_sheet_permutation_decomposition_base) :
    xi_window6_boundary_two_sheet_permutation_decomposition_fixedChar σ =
      xi_window6_boundary_two_sheet_permutation_decomposition_trivialChar σ +
        xi_window6_boundary_two_sheet_permutation_decomposition_standardChar σ := by
  unfold xi_window6_boundary_two_sheet_permutation_decomposition_trivialChar
  unfold xi_window6_boundary_two_sheet_permutation_decomposition_standardChar
  omega

private lemma xi_window6_boundary_two_sheet_permutation_decomposition_no_sign_fixed :
    xi_window6_boundary_two_sheet_permutation_decomposition_characterMultiplicity
      xi_window6_boundary_two_sheet_permutation_decomposition_fixedChar
      xi_window6_boundary_two_sheet_permutation_decomposition_signChar = 0 := by
  decide

private lemma xi_window6_boundary_two_sheet_permutation_decomposition_no_sign_standard :
    xi_window6_boundary_two_sheet_permutation_decomposition_characterMultiplicity
      xi_window6_boundary_two_sheet_permutation_decomposition_standardChar
      xi_window6_boundary_two_sheet_permutation_decomposition_signChar = 0 := by
  decide

/-- Paper label: `thm:xi-window6-boundary-two-sheet-permutation-decomposition`. -/
theorem paper_xi_window6_boundary_two_sheet_permutation_decomposition :
    xi_window6_boundary_two_sheet_permutation_decomposition_statement := by
  refine ⟨by decide, xi_window6_boundary_two_sheet_permutation_decomposition_fiber_card,
    xi_window6_boundary_two_sheet_permutation_decomposition_swap_involutive,
    xi_window6_boundary_two_sheet_permutation_decomposition_swap_no_fixed,
    xi_window6_boundary_two_sheet_permutation_decomposition_baseAction_mul,
    xi_window6_boundary_two_sheet_permutation_decomposition_fixedChar_split,
    xi_window6_boundary_two_sheet_permutation_decomposition_no_sign_fixed,
    xi_window6_boundary_two_sheet_permutation_decomposition_no_sign_standard⟩

end Omega.Zeta
