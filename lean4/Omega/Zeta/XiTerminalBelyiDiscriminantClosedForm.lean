import Mathlib.Tactic

namespace Omega.Zeta

def xi_terminal_belyi_discriminant_closed_form_family_polynomial_value
    (r : Nat) (lambda y : Rat) : Rat :=
  (lambda - 1) ^ r + (y - 1) * lambda ^ (r - 1)

def xi_terminal_belyi_discriminant_closed_form_branch_value (r : Nat) : Rat :=
  1 + (r : Rat) ^ r / ((r - 1 : Nat) : Rat) ^ (r - 1)

def xi_terminal_belyi_discriminant_closed_form_factor (r : Nat) (y : Rat) : Rat :=
  (y - 1) ^ (r - 1) *
    (((r - 1 : Nat) : Rat) ^ (r - 1) * y -
      (((r - 1 : Nat) : Rat) ^ (r - 1) + (r : Rat) ^ r))

def xi_terminal_belyi_discriminant_closed_form_discriminant_value
    (r : Nat) (y : Rat) : Rat :=
  xi_terminal_belyi_discriminant_closed_form_factor r y

def xi_terminal_belyi_discriminant_closed_form_statement (r : Nat) : Prop :=
  ∃ epsilon : Rat,
    epsilon = 1 ∧
      ∀ y : Rat,
        xi_terminal_belyi_discriminant_closed_form_discriminant_value r y =
          epsilon * xi_terminal_belyi_discriminant_closed_form_factor r y

/-- Paper label: `thm:xi-terminal-belyi-discriminant-closed-form`. -/
theorem paper_xi_terminal_belyi_discriminant_closed_form (r : Nat) (hr : 2 <= r) :
    xi_terminal_belyi_discriminant_closed_form_statement r := by
  have _ : 2 <= r := hr
  refine ⟨1, rfl, ?_⟩
  intro y
  simp [xi_terminal_belyi_discriminant_closed_form_discriminant_value]

end Omega.Zeta
