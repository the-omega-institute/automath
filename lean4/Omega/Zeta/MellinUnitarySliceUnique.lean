import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Zeta.MellinUnitarySlice

namespace Omega.Zeta

/-- The positive real twist relating the slice `σ` to the critical slice `1 / 2`. -/
noncomputable def mellin_unitary_slice_unique_weight (σ x : ℝ) : ℝ :=
  Real.exp ((σ - 1 / 2) * Real.log x)

/-- Paper label: `thm:mellin-unitary-slice-unique`. -/
theorem paper_mellin_unitary_slice_unique (σ : ℝ) :
    (∀ x, 0 < x → mellin_unitary_slice_unique_weight (1 / 2) x = 1) ∧
      ((∀ x, 0 < x → mellin_unitary_slice_unique_weight σ x = 1) ↔ σ = 1 / 2) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    simp [mellin_unitary_slice_unique_weight]
  · constructor
    · intro hweight
      have hexp : Real.exp (σ - 1 / 2) = 1 := by
        simpa [mellin_unitary_slice_unique_weight, Real.log_exp] using
          hweight (Real.exp 1) (Real.exp_pos 1)
      rw [Real.exp_eq_one_iff] at hexp
      linarith
    · intro hσ
      subst hσ
      intro x hx
      simp [mellin_unitary_slice_unique_weight]
