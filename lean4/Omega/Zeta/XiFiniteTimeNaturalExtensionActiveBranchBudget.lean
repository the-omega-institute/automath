import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Cardinal data for a finite natural-extension chain with at most binary fibers.  The
`fiberCard j y` entry is the size of the fiber over the `y`-th state in layer `j + 1`. -/
structure xi_finite_time_natural_extension_active_branch_budget_data where
  N : ℕ
  baseCount : Fin N → ℕ
  fiberCard : ∀ j : Fin N, Fin (baseCount j) → ℕ
  fiber_card_le_two : ∀ j y, fiberCard j y ≤ 2

/-- A layer is active exactly when one of its fibers has two points. -/
def xi_finite_time_natural_extension_active_branch_budget_active
    (D : xi_finite_time_natural_extension_active_branch_budget_data) (j : Fin D.N) : Prop :=
  ∃ y : Fin (D.baseCount j), D.fiberCard j y = 2

/-- The active layer set. -/
noncomputable def xi_finite_time_natural_extension_active_branch_budget_activeLayerSet
    (D : xi_finite_time_natural_extension_active_branch_budget_data) : Finset (Fin D.N) :=
  by
    classical
    exact Finset.univ.filter fun j =>
      xi_finite_time_natural_extension_active_branch_budget_active D j

/-- One bit is charged exactly to nontrivial binary alphabets. -/
def xi_finite_time_natural_extension_active_branch_budget_bitCost (a : ℕ) : ℕ :=
  if 2 ≤ a then 1 else 0

/-- The canonical optimal alphabet size: two symbols on active layers and one elsewhere. -/
noncomputable def xi_finite_time_natural_extension_active_branch_budget_optimalAlphabet
    (D : xi_finite_time_natural_extension_active_branch_budget_data) (j : Fin D.N) : ℕ :=
  by
    classical
    exact if xi_finite_time_natural_extension_active_branch_budget_active D j then 2 else 1

/-- An alphabet profile covers the chain if every local fiber injects into the corresponding
alphabet cardinal. -/
def xi_finite_time_natural_extension_active_branch_budget_covers
    (D : xi_finite_time_natural_extension_active_branch_budget_data) (alphabet : Fin D.N → ℕ) :
    Prop :=
  ∀ j y, D.fiberCard j y ≤ alphabet j

/-- Concrete statement for the active-layer budget theorem: any covering alphabet has at least
two symbols on active layers; the canonical active/inactive alphabet covers all fibers; and its
binary cost is exactly the number of active layers. -/
noncomputable def xi_finite_time_natural_extension_active_branch_budget_statement
    (D : xi_finite_time_natural_extension_active_branch_budget_data) : Prop :=
  (∀ alphabet,
      xi_finite_time_natural_extension_active_branch_budget_covers D alphabet →
        ∀ j, xi_finite_time_natural_extension_active_branch_budget_active D j →
          2 ≤ alphabet j) ∧
    xi_finite_time_natural_extension_active_branch_budget_covers D
      (xi_finite_time_natural_extension_active_branch_budget_optimalAlphabet D) ∧
    (∑ j : Fin D.N,
        xi_finite_time_natural_extension_active_branch_budget_bitCost
          (xi_finite_time_natural_extension_active_branch_budget_optimalAlphabet D j)) =
      (xi_finite_time_natural_extension_active_branch_budget_activeLayerSet D).card

/-- Paper label: `thm:xi-finite-time-natural-extension-active-branch-budget`. -/
theorem paper_xi_finite_time_natural_extension_active_branch_budget
    (D : xi_finite_time_natural_extension_active_branch_budget_data) :
    xi_finite_time_natural_extension_active_branch_budget_statement D := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro alphabet hcover j hactive
    rcases hactive with ⟨y, hy⟩
    simpa [hy] using hcover j y
  · intro j y
    by_cases hactive : xi_finite_time_natural_extension_active_branch_budget_active D j
    · rw [xi_finite_time_natural_extension_active_branch_budget_optimalAlphabet]
      simp [hactive, D.fiber_card_le_two j y]
    · have hne : D.fiberCard j y ≠ 2 := by
        intro htwo
        exact hactive ⟨y, htwo⟩
      have hle_two : D.fiberCard j y ≤ 2 := D.fiber_card_le_two j y
      have hle_one : D.fiberCard j y ≤ 1 := by omega
      rw [xi_finite_time_natural_extension_active_branch_budget_optimalAlphabet]
      simpa [hactive] using hle_one
  · trans ∑ j : Fin D.N,
        if xi_finite_time_natural_extension_active_branch_budget_active D j then 1 else 0
    · refine Finset.sum_congr rfl ?_
      intro j _hj
      by_cases hactive : xi_finite_time_natural_extension_active_branch_budget_active D j
      · simp [xi_finite_time_natural_extension_active_branch_budget_bitCost,
          xi_finite_time_natural_extension_active_branch_budget_optimalAlphabet, hactive]
      · simp [xi_finite_time_natural_extension_active_branch_budget_bitCost,
          xi_finite_time_natural_extension_active_branch_budget_optimalAlphabet, hactive]
    · simp [xi_finite_time_natural_extension_active_branch_budget_activeLayerSet]

end Omega.Zeta
