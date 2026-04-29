import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- The five finite Lee--Yang branch families. -/
abbrev xi_terminal_zm_leyang_ramification_pullback_2n_branch_family := Fin 5

/-- The concrete `2^n`-torsion fiber used in the pullback bookkeeping. -/
abbrev xi_terminal_zm_leyang_ramification_pullback_2n_torsion_fiber (n : ℕ) :=
  Fin (2 ^ n)

/-- The finite ramification fibers above the five Lee--Yang branch families. -/
abbrev xi_terminal_zm_leyang_ramification_pullback_2n_finite_branch_fiber (n : ℕ) :=
  xi_terminal_zm_leyang_ramification_pullback_2n_branch_family ×
    xi_terminal_zm_leyang_ramification_pullback_2n_torsion_fiber n

/-- Projection to the original finite branch family. -/
def xi_terminal_zm_leyang_ramification_pullback_2n_branch_projection (n : ℕ) :
    xi_terminal_zm_leyang_ramification_pullback_2n_finite_branch_fiber n →
      xi_terminal_zm_leyang_ramification_pullback_2n_branch_family :=
  Prod.fst

/-- The branch image after the etale pullback. -/
def xi_terminal_zm_leyang_ramification_pullback_2n_branch_image (n : ℕ) :
    Finset xi_terminal_zm_leyang_ramification_pullback_2n_branch_family :=
  Finset.univ.image (xi_terminal_zm_leyang_ramification_pullback_2n_branch_projection n)

/-- The total number of finite simple branch points after pullback. -/
def xi_terminal_zm_leyang_ramification_pullback_2n_finite_branch_count (n : ℕ) : ℕ :=
  Fintype.card (xi_terminal_zm_leyang_ramification_pullback_2n_finite_branch_fiber n)

/-- The number of translated copies of a fixed finite branch point. -/
def xi_terminal_zm_leyang_ramification_pullback_2n_branch_multiplicity
    (n : ℕ) (_i : xi_terminal_zm_leyang_ramification_pullback_2n_branch_family) : ℕ :=
  Fintype.card (xi_terminal_zm_leyang_ramification_pullback_2n_torsion_fiber n)

/-- The number of copied full-ramification points over infinity. -/
def xi_terminal_zm_leyang_ramification_pullback_2n_infinity_count (n : ℕ) : ℕ :=
  Fintype.card (xi_terminal_zm_leyang_ramification_pullback_2n_torsion_fiber n)

/-- Paper label: `cor:xi-terminal-zm-leyang-ramification-pullback-2n`.

The etale pullback keeps the same five finite branch images, and each finite branch family is
copied over the `2^n`-torsion fiber. -/
def xi_terminal_zm_leyang_ramification_pullback_2n_statement : Prop :=
  ∀ n : ℕ,
    xi_terminal_zm_leyang_ramification_pullback_2n_branch_image n = Finset.univ ∧
      xi_terminal_zm_leyang_ramification_pullback_2n_finite_branch_count n = 5 * 2 ^ n ∧
      (∀ i : xi_terminal_zm_leyang_ramification_pullback_2n_branch_family,
        xi_terminal_zm_leyang_ramification_pullback_2n_branch_multiplicity n i = 2 ^ n) ∧
      xi_terminal_zm_leyang_ramification_pullback_2n_infinity_count n = 2 ^ n

theorem paper_xi_terminal_zm_leyang_ramification_pullback_2n :
    xi_terminal_zm_leyang_ramification_pullback_2n_statement := by
  intro n
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i
    simp [xi_terminal_zm_leyang_ramification_pullback_2n_branch_image,
      xi_terminal_zm_leyang_ramification_pullback_2n_branch_projection]
  · simp [xi_terminal_zm_leyang_ramification_pullback_2n_finite_branch_count]
  · intro i
    simp [xi_terminal_zm_leyang_ramification_pullback_2n_branch_multiplicity]
  · simp [xi_terminal_zm_leyang_ramification_pullback_2n_infinity_count]

end Omega.Zeta
