import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open BigOperators

/-- Rank-one decomposition of the two-parameter Boolean disjointness matrix action. -/
def xi_two_param_disjointness_full_spectrum_secular_action
    (q : Nat) (a b : ℝ) (x : Fin (q + 1) → ℝ) (i : Fin (q + 1)) : ℝ :=
  (a - b) * x i + b * ∑ j : Fin (q + 1), x j

/-- The all-ones vector on the finite Boolean shell. -/
def xi_two_param_disjointness_full_spectrum_secular_ones
    (q : Nat) : Fin (q + 1) → ℝ :=
  fun _ => 1

/-- The rank-one secular polynomial carrying the exceptional all-ones root and the
orthogonal disjointness root. -/
def xi_two_param_disjointness_full_spectrum_secular_polynomial
    (q : Nat) (a b lam : ℝ) : ℝ :=
  (lam - (a + (q : ℝ) * b)) * (lam - (a - b)) ^ q

/-- Paper-facing full-spectrum secular package for the two-parameter disjointness action. -/
def xi_two_param_disjointness_full_spectrum_secular_statement
    (q : Nat) (a b : ℝ) : Prop :=
  (∀ x : Fin (q + 1) → ℝ,
      (∑ i : Fin (q + 1), x i) = 0 →
        ∀ i : Fin (q + 1),
          xi_two_param_disjointness_full_spectrum_secular_action q a b x i =
            (a - b) * x i) ∧
    (∀ i : Fin (q + 1),
      xi_two_param_disjointness_full_spectrum_secular_action q a b
          (xi_two_param_disjointness_full_spectrum_secular_ones q) i =
        (a + (q : ℝ) * b) *
          xi_two_param_disjointness_full_spectrum_secular_ones q i) ∧
    xi_two_param_disjointness_full_spectrum_secular_polynomial q a b
        (a + (q : ℝ) * b) = 0 ∧
    (q = 0 ∨
      xi_two_param_disjointness_full_spectrum_secular_polynomial q a b (a - b) = 0)

/-- Paper label: `thm:xi-two-param-disjointness-full-spectrum-secular`. -/
theorem paper_xi_two_param_disjointness_full_spectrum_secular (q : Nat) (a b : Real) :
    xi_two_param_disjointness_full_spectrum_secular_statement q a b := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx i
    simp [xi_two_param_disjointness_full_spectrum_secular_action, hx]
  · intro i
    simp [xi_two_param_disjointness_full_spectrum_secular_action,
      xi_two_param_disjointness_full_spectrum_secular_ones, Finset.sum_const, Fintype.card_fin]
    ring
  · simp [xi_two_param_disjointness_full_spectrum_secular_polynomial]
  · by_cases hq : q = 0
    · exact Or.inl hq
    · right
      cases q with
      | zero => exact (hq rfl).elim
      | succ q =>
          simp [xi_two_param_disjointness_full_spectrum_secular_polynomial]

end Omega.Zeta
