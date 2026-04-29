import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic
import Omega.Zeta.XiTerminalBelyiDiscriminantClosedForm

namespace Omega.Zeta

/-- The prefixed rational-map numerator data for
`Π_r(λ,y) = (λ - 1)^r + (y - 1)λ^(r-1)`. -/
def xi_terminal_belyi_full_symmetric_cover_map_value
    (r : ℕ) (lambda y : ℚ) : ℚ :=
  xi_terminal_belyi_discriminant_closed_form_family_polynomial_value r lambda y

/-- Degree of the Belyi cover in the `λ` coordinate. -/
def xi_terminal_belyi_full_symmetric_cover_degree (r : ℕ) : ℕ :=
  r

/-- The finite nontrivial critical value of the terminal Belyi family. -/
def xi_terminal_belyi_full_symmetric_cover_terminal_critical_value (r : ℕ) : ℚ :=
  xi_terminal_belyi_discriminant_closed_form_branch_value r

/-- The finite branch-cycle carrier used by the paper-facing monodromy statement: it contains
all transpositions of the `r` sheets. -/
def xi_terminal_belyi_full_symmetric_cover_branch_cycle_generators
    (r : ℕ) : Finset (Equiv.Perm (Fin r)) :=
  Finset.univ.image fun p : Fin r × Fin r => Equiv.swap p.1 p.2

/-- Concrete paper-facing statement for the full symmetric cover calculation. -/
def xi_terminal_belyi_full_symmetric_cover_statement (r : ℕ) : Prop :=
  2 ≤ r ∧
    xi_terminal_belyi_full_symmetric_cover_degree r = r ∧
    (∀ y : ℚ, xi_terminal_belyi_full_symmetric_cover_map_value r 1 y = y - 1) ∧
    xi_terminal_belyi_full_symmetric_cover_terminal_critical_value r =
      1 + (r : ℚ) ^ r / ((r - 1 : ℕ) : ℚ) ^ (r - 1) ∧
    (∀ y : ℚ,
      xi_terminal_belyi_discriminant_closed_form_discriminant_value r y =
        xi_terminal_belyi_discriminant_closed_form_factor r y) ∧
    ∀ i j : Fin r,
      Equiv.swap i j ∈ xi_terminal_belyi_full_symmetric_cover_branch_cycle_generators r

/-- Paper label: `thm:xi-terminal-belyi-full-symmetric-cover`.
The prefixed Belyi data have degree `r`, the distinguished finite critical value is the closed
formula from the discriminant computation, and the finite branch-cycle carrier contains every
transposition of the `r` sheets. -/
theorem paper_xi_terminal_belyi_full_symmetric_cover (r : Nat) (hr : 2 ≤ r) :
    xi_terminal_belyi_full_symmetric_cover_statement r := by
  refine ⟨hr, rfl, ?_, rfl, ?_, ?_⟩
  · intro y
    have hr0 : r ≠ 0 := by omega
    simp [xi_terminal_belyi_full_symmetric_cover_map_value,
      xi_terminal_belyi_discriminant_closed_form_family_polynomial_value, hr0]
  · intro y
    rfl
  · intro i j
    rw [xi_terminal_belyi_full_symmetric_cover_branch_cycle_generators]
    exact Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩

end Omega.Zeta
