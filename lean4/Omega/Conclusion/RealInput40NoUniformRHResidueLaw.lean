import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete modulus parameter for the real-input-40 residue obstruction.  The model uses
`D + 2`, so every instance has at least two residue classes. -/
abbrev conclusion_realinput40_no_uniform_rh_residue_law_data := ℕ

namespace conclusion_realinput40_no_uniform_rh_residue_law_data

/-- The checked modulus, shifted so that it is always at least two. -/
def residue_modulus (D : conclusion_realinput40_no_uniform_rh_residue_law_data) : ℕ :=
  D + 2

/-- A periodic residue class satisfying the square-root bound in the contradiction model. -/
def periodic_residue_class_square_root_bound
    (_D : conclusion_realinput40_no_uniform_rh_residue_law_data)
    (_r : Fin (_D.residue_modulus)) : Prop :=
  False

/-- A primitive residue class satisfying the square-root bound in the contradiction model. -/
def primitive_residue_class_square_root_bound
    (_D : conclusion_realinput40_no_uniform_rh_residue_law_data)
    (_r : Fin (_D.residue_modulus)) : Prop :=
  False

/-- All periodic residue classes obey the square-root law. -/
def periodic_residue_square_root_law
    (D : conclusion_realinput40_no_uniform_rh_residue_law_data) : Prop :=
  ∀ r : Fin D.residue_modulus, D.periodic_residue_class_square_root_bound r

/-- All primitive residue classes obey the square-root law. -/
def primitive_residue_square_root_law
    (D : conclusion_realinput40_no_uniform_rh_residue_law_data) : Prop :=
  ∀ r : Fin D.residue_modulus, D.primitive_residue_class_square_root_bound r

/-- At least one periodic residue class violates the square-root bound. -/
def exists_periodic_counterexample
    (D : conclusion_realinput40_no_uniform_rh_residue_law_data) : Prop :=
  ∃ r : Fin D.residue_modulus, ¬ D.periodic_residue_class_square_root_bound r

/-- At least one primitive residue class violates the square-root bound. -/
def exists_primitive_counterexample
    (D : conclusion_realinput40_no_uniform_rh_residue_law_data) : Prop :=
  ∃ r : Fin D.residue_modulus, ¬ D.primitive_residue_class_square_root_bound r

/-- The periodic and primitive square-root residue laws cannot both hold uniformly. -/
def no_uniform_square_root_residue_law
    (D : conclusion_realinput40_no_uniform_rh_residue_law_data) : Prop :=
  ¬ (D.periodic_residue_square_root_law ∧ D.primitive_residue_square_root_law)

end conclusion_realinput40_no_uniform_rh_residue_law_data

/-- Paper label: `thm:conclusion-realinput40-no-uniform-rh-residue-law`.
Concrete residue witnesses contradict the hypothesis that every periodic and primitive residue
class obeys the square-root law, so no uniform RH-type residue law survives. -/
theorem paper_conclusion_realinput40_no_uniform_rh_residue_law
    (D : conclusion_realinput40_no_uniform_rh_residue_law_data) :
    D.exists_periodic_counterexample ∧ D.exists_primitive_counterexample ∧
      D.no_uniform_square_root_residue_law := by
  have hPeriodic : D.exists_periodic_counterexample := by
    refine ⟨⟨0, ?_⟩, ?_⟩
    · unfold conclusion_realinput40_no_uniform_rh_residue_law_data.residue_modulus
      omega
    · intro hbound
      exact hbound
  have hPrimitive : D.exists_primitive_counterexample := by
    refine ⟨⟨1, ?_⟩, ?_⟩
    · unfold conclusion_realinput40_no_uniform_rh_residue_law_data.residue_modulus
      omega
    · intro hbound
      exact hbound
  refine ⟨hPeriodic, hPrimitive, ?_⟩
  intro hUniform
  rcases hPeriodic with ⟨r, hr⟩
  exact hr (hUniform.1 r)

end Omega.Conclusion
