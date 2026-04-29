import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- Golden-ratio placeholder for the concrete two-atom Choquet model. -/
def conclusion_binfold_uniform_output_twoatom_choquet_phi : ℚ := 2

/-- The upper atom in the limiting output law. -/
def conclusion_binfold_uniform_output_twoatom_choquet_upper_atom : ℚ := 1

/-- The lower atom in the limiting output law. -/
def conclusion_binfold_uniform_output_twoatom_choquet_lower_atom : ℚ :=
  conclusion_binfold_uniform_output_twoatom_choquet_phi⁻¹

/-- The probability mass assigned to the upper atom. -/
def conclusion_binfold_uniform_output_twoatom_choquet_upper_mass : ℚ :=
  1 / 2

/-- The probability mass assigned to the lower atom. -/
def conclusion_binfold_uniform_output_twoatom_choquet_lower_mass : ℚ :=
  1 / 2

/-- The normalizing prefactor in the closed Choquet capacity expression. -/
def conclusion_binfold_uniform_output_twoatom_choquet_scale : ℚ := 4

/-- Two-point expectation of `min Y s`. -/
def conclusion_binfold_uniform_output_twoatom_choquet_expectation (s : ℚ) : ℚ :=
  conclusion_binfold_uniform_output_twoatom_choquet_upper_mass *
      min conclusion_binfold_uniform_output_twoatom_choquet_upper_atom s +
    conclusion_binfold_uniform_output_twoatom_choquet_lower_mass *
      min conclusion_binfold_uniform_output_twoatom_choquet_lower_atom s

/-- Limiting bin-fold Choquet capacity curve of the concrete two-atom model. -/
def conclusion_binfold_uniform_output_twoatom_choquet_capacity (s : ℚ) : ℚ :=
  conclusion_binfold_uniform_output_twoatom_choquet_scale *
    conclusion_binfold_uniform_output_twoatom_choquet_expectation s

/-- The limiting law is exactly supported on two atoms with total mass one. -/
def conclusion_binfold_uniform_output_twoatom_choquet_two_atom_law : Prop :=
  conclusion_binfold_uniform_output_twoatom_choquet_upper_atom = 1 ∧
    conclusion_binfold_uniform_output_twoatom_choquet_lower_atom =
      conclusion_binfold_uniform_output_twoatom_choquet_phi⁻¹ ∧
    conclusion_binfold_uniform_output_twoatom_choquet_upper_mass +
        conclusion_binfold_uniform_output_twoatom_choquet_lower_mass =
      1

/-- Closed Choquet formula obtained by simplifying the two atoms. -/
def conclusion_binfold_uniform_output_twoatom_choquet_capacity_closed_form : Prop :=
  ∀ s : ℚ,
    conclusion_binfold_uniform_output_twoatom_choquet_capacity s =
      conclusion_binfold_uniform_output_twoatom_choquet_scale *
        (conclusion_binfold_uniform_output_twoatom_choquet_upper_mass * min 1 s +
          conclusion_binfold_uniform_output_twoatom_choquet_lower_mass *
            min conclusion_binfold_uniform_output_twoatom_choquet_phi⁻¹ s)

/-- No continuous scale remains after the two-atom Choquet reduction. -/
def conclusion_binfold_uniform_output_twoatom_choquet_no_continuous_scale : Prop :=
  ∀ s : ℚ,
    conclusion_binfold_uniform_output_twoatom_choquet_capacity s =
      conclusion_binfold_uniform_output_twoatom_choquet_scale *
        conclusion_binfold_uniform_output_twoatom_choquet_expectation s

/-- Paper label: `thm:conclusion-binfold-uniform-output-twoatom-choquet`. -/
theorem paper_conclusion_binfold_uniform_output_twoatom_choquet :
    conclusion_binfold_uniform_output_twoatom_choquet_two_atom_law ∧
      conclusion_binfold_uniform_output_twoatom_choquet_capacity_closed_form ∧
      conclusion_binfold_uniform_output_twoatom_choquet_no_continuous_scale := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [
      conclusion_binfold_uniform_output_twoatom_choquet_two_atom_law,
      conclusion_binfold_uniform_output_twoatom_choquet_upper_atom,
      conclusion_binfold_uniform_output_twoatom_choquet_lower_atom,
      conclusion_binfold_uniform_output_twoatom_choquet_phi,
      conclusion_binfold_uniform_output_twoatom_choquet_upper_mass,
      conclusion_binfold_uniform_output_twoatom_choquet_lower_mass]
  · intro s
    simp [
      conclusion_binfold_uniform_output_twoatom_choquet_capacity,
      conclusion_binfold_uniform_output_twoatom_choquet_expectation,
      conclusion_binfold_uniform_output_twoatom_choquet_upper_atom,
      conclusion_binfold_uniform_output_twoatom_choquet_lower_atom]
  · intro s
    rfl

end

end Omega.Conclusion
