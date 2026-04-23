import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.Conclusion.RealInput40RootUnityGhostCompletePrimitiveDegenerate

namespace Omega.Conclusion

/-- The canonical primitive atom supported at the two-step pulse. -/
def conclusion_realinput40_unique_primitive_two_step_atom_canonical
    (u : Complex) : ℕ → Complex :=
  fun n => atomPrimitiveCoeff n u

/-- An alternative primitive atom is admissible when it has the same two-step support and weight. -/
def conclusion_realinput40_unique_primitive_two_step_atom_admissible
    (a : ℕ → Complex) (u : Complex) : Prop :=
  a 2 = u ∧ ∀ n, n ≠ 2 → a n = 0

/-- Branch-level interpretation of the canonical atom: it contributes exactly at length `2` and
vanishes on the lower branches. -/
def conclusion_realinput40_unique_primitive_two_step_atom_branch_interpretation
    (u : Complex) : Prop :=
  conclusion_realinput40_unique_primitive_two_step_atom_canonical u 2 = u ∧
    conclusion_realinput40_unique_primitive_two_step_atom_canonical u 0 = 0 ∧
    conclusion_realinput40_unique_primitive_two_step_atom_canonical u 1 = 0

private lemma conclusion_realinput40_unique_primitive_two_step_atom_canonical_formula
    (u : Complex) (n : ℕ) :
    conclusion_realinput40_unique_primitive_two_step_atom_canonical u n =
      (if n = 2 then u else 0) := by
  simpa [conclusion_realinput40_unique_primitive_two_step_atom_canonical] using
    (paper_conclusion_realinput40_root_unity_ghost_complete_primitive_degenerate
      u 2 n (by decide)).2.1

/-- Paper label: `thm:conclusion-realinput40-unique-primitive-two-step-atom`. The primitive
two-step atom for `(1 - u z^2)⁻¹` is uniquely determined by having weight `u` at length `2` and
vanishing elsewhere, and the canonical branch interpretation records exactly that pulse. -/
theorem paper_conclusion_realinput40_unique_primitive_two_step_atom (u : Complex) :
    (∀ a : ℕ → Complex,
      conclusion_realinput40_unique_primitive_two_step_atom_admissible a u →
        a = conclusion_realinput40_unique_primitive_two_step_atom_canonical u) ∧
      (∀ n : ℕ,
        conclusion_realinput40_unique_primitive_two_step_atom_canonical u n =
          (if n = 2 then u else 0)) ∧
      conclusion_realinput40_unique_primitive_two_step_atom_branch_interpretation u := by
  refine ⟨?_, conclusion_realinput40_unique_primitive_two_step_atom_canonical_formula u, ?_⟩
  · intro a ha
    ext n
    by_cases h2 : n = 2
    · subst h2
      simpa [conclusion_realinput40_unique_primitive_two_step_atom_canonical_formula] using ha.1
    · have hzero : a n = 0 := ha.2 n h2
      rw [hzero, conclusion_realinput40_unique_primitive_two_step_atom_canonical_formula]
      simp [h2]
  · refine ⟨?_, ?_, ?_⟩
    · simpa using
        conclusion_realinput40_unique_primitive_two_step_atom_canonical_formula u 2
    · simpa using
        conclusion_realinput40_unique_primitive_two_step_atom_canonical_formula u 0
    · simpa using
        conclusion_realinput40_unique_primitive_two_step_atom_canonical_formula u 1

end Omega.Conclusion
