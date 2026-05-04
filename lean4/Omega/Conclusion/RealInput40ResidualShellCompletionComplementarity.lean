import Omega.Conclusion.CompletedSliceBalancedAtomsBecomeConstants
import Omega.Conclusion.RealInput40UVAtomCore
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Omega.Conclusion

open BigOperators

noncomputable section

/-- Primitive residual shell left after subtracting the real-input-40 core. -/
def conclusion_realinput40_residual_shell_completion_complementarity_primitiveDiff
    (m : ℕ) [NeZero m] (r : Fin m) (n c : ℕ) : ℂ :=
  if n = 2 ∧ c = 0 ∧ r = (1 : Fin m) then 1 else 0

/-- The residue class of `n/2` modulo `m`, as a finite residue. -/
def conclusion_realinput40_residual_shell_completion_complementarity_halfResidue
    (m : ℕ) [NeZero m] (n : ℕ) : Fin m :=
  ⟨(n / 2) % m, Nat.mod_lt _ (Nat.pos_of_neZero m)⟩

/-- Periodic residual shell left after subtracting the real-input-40 core. -/
def conclusion_realinput40_residual_shell_completion_complementarity_periodicDiff
    (m : ℕ) [NeZero m] (r : Fin m) (n c : ℕ) : ℂ :=
  if Even n ∧ c = 0 ∧
      r = conclusion_realinput40_residual_shell_completion_complementarity_halfResidue m n then
    2
  else
    0

/-- Concrete completion data for the residual-shell/completion complementarity statement. -/
structure conclusion_realinput40_residual_shell_completion_complementarity_data where
  conclusion_realinput40_residual_shell_completion_complementarity_completionData :
    conclusion_completed_slice_balanced_atoms_become_constants_data
  conclusion_realinput40_residual_shell_completion_complementarity_balanced :
    ∀ a ∈
      conclusion_completed_slice_balanced_atoms_become_constants_data.conclusion_completed_slice_balanced_atoms_become_constants_atoms
        conclusion_realinput40_residual_shell_completion_complementarity_completionData,
      a.conclusion_completed_slice_balanced_atoms_become_constants_atom_length =
        2 * a.conclusion_completed_slice_balanced_atoms_become_constants_atom_energy

/-- Paper-facing residual tomography and completed-slice blindness statement. -/
def conclusion_realinput40_residual_shell_completion_complementarity_statement
    (D : conclusion_realinput40_residual_shell_completion_complementarity_data) : Prop :=
  (∀ (m : ℕ) [NeZero m] (r : Fin m) (n c : ℕ),
    conclusion_realinput40_residual_shell_completion_complementarity_primitiveDiff m r n c =
      if n = 2 ∧ c = 0 ∧ r = (1 : Fin m) then 1 else 0) ∧
    (∀ (m : ℕ) [NeZero m] (r : Fin m) (n c : ℕ),
      conclusion_realinput40_residual_shell_completion_complementarity_periodicDiff m r n c =
        if Even n ∧ c = 0 ∧
            r = conclusion_realinput40_residual_shell_completion_complementarity_halfResidue
              m n then
          2
        else
          0) ∧
    (∀ (m : ℕ) [NeZero m] (χ : Fin m → ℂ) (n c : ℕ),
      (∑ r : Fin m,
          χ r *
            conclusion_realinput40_residual_shell_completion_complementarity_primitiveDiff
              m r n c) =
        χ (1 : Fin m) * if n = 2 ∧ c = 0 then 1 else 0) ∧
    (∀ (m : ℕ) [NeZero m] (χ : Fin m → ℂ) (n c : ℕ),
      (∑ r : Fin m,
          χ r *
            conclusion_realinput40_residual_shell_completion_complementarity_periodicDiff
              m r n c) =
        χ (conclusion_realinput40_residual_shell_completion_complementarity_halfResidue m n) *
          if Even n ∧ c = 0 then 2 else 0) ∧
    (∀ s : ℝ,
      conclusion_completed_slice_balanced_atoms_become_constants_data.completedAtomProduct
          D.conclusion_realinput40_residual_shell_completion_complementarity_completionData s =
        conclusion_completed_slice_balanced_atoms_become_constants_data.completedAtomProduct
          D.conclusion_realinput40_residual_shell_completion_complementarity_completionData (1 / 2))

lemma conclusion_realinput40_residual_shell_completion_complementarity_primitive_sum
    (m : ℕ) [NeZero m] (χ : Fin m → ℂ) (n c : ℕ) :
    (∑ r : Fin m,
        χ r *
          conclusion_realinput40_residual_shell_completion_complementarity_primitiveDiff
            m r n c) =
      χ (1 : Fin m) * if n = 2 ∧ c = 0 then 1 else 0 := by
  by_cases h : n = 2 ∧ c = 0
  · simp [conclusion_realinput40_residual_shell_completion_complementarity_primitiveDiff, h]
  · simp [conclusion_realinput40_residual_shell_completion_complementarity_primitiveDiff, h]
    have hpoint : ∀ r : Fin m, ¬(n = 2 ∧ c = 0 ∧ r = (1 : Fin m)) := by
      intro r hr
      exact h ⟨hr.1, hr.2.1⟩
    simp [hpoint]

lemma conclusion_realinput40_residual_shell_completion_complementarity_periodic_sum
    (m : ℕ) [NeZero m] (χ : Fin m → ℂ) (n c : ℕ) :
    (∑ r : Fin m,
        χ r *
          conclusion_realinput40_residual_shell_completion_complementarity_periodicDiff
            m r n c) =
      χ (conclusion_realinput40_residual_shell_completion_complementarity_halfResidue m n) *
        if Even n ∧ c = 0 then 2 else 0 := by
  by_cases h : Even n ∧ c = 0
  · simp [conclusion_realinput40_residual_shell_completion_complementarity_periodicDiff, h]
  · simp [conclusion_realinput40_residual_shell_completion_complementarity_periodicDiff, h]
    have hpoint :
        ∀ r : Fin m,
          ¬(Even n ∧ c = 0 ∧
            r = conclusion_realinput40_residual_shell_completion_complementarity_halfResidue
              m n) := by
      intro r hr
      exact h ⟨hr.1, hr.2.1⟩
    simp [hpoint]

/-- Paper label: `thm:conclusion-realinput40-residual-shell-completion-complementarity`. -/
theorem paper_conclusion_realinput40_residual_shell_completion_complementarity
    (D : conclusion_realinput40_residual_shell_completion_complementarity_data) :
    conclusion_realinput40_residual_shell_completion_complementarity_statement D := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro m _ r n c
    rfl
  · intro m _ r n c
    rfl
  · intro m _ χ n c
    exact conclusion_realinput40_residual_shell_completion_complementarity_primitive_sum m χ n c
  · intro m _ χ n c
    exact conclusion_realinput40_residual_shell_completion_complementarity_periodic_sum m χ n c
  · exact
      (paper_conclusion_completed_slice_normalized_kernel_balanced_atoms
        D.conclusion_realinput40_residual_shell_completion_complementarity_completionData
        D.conclusion_realinput40_residual_shell_completion_complementarity_balanced).1

end

end Omega.Conclusion
