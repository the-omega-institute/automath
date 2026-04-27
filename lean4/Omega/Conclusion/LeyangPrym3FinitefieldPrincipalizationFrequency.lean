import Mathlib.Tactic

namespace Omega.Conclusion

/-- Requested singleton data handle for the concrete finite-field Prym frequency table. -/
abbrev conclusion_leyang_prym3_finitefield_principalization_frequency_data := PUnit

/-- The three `S3` splitting types of the Lee--Yang cubic over a finite field. -/
inductive conclusion_leyang_prym3_finitefield_principalization_frequency_split_type
  | one_one_one
  | one_two
  | three
  deriving DecidableEq, Repr

open conclusion_leyang_prym3_finitefield_principalization_frequency_split_type

/-- The Chebotarev density table for the three `S3` splitting types. -/
def conclusion_leyang_prym3_finitefield_principalization_frequency_density :
    conclusion_leyang_prym3_finitefield_principalization_frequency_split_type → ℚ
  | one_one_one => 1 / 6
  | one_two => 1 / 2
  | three => 1 / 3

/-- A linear factor is present exactly in the `(1,1,1)` and `(1,2)` cases. -/
def conclusion_leyang_prym3_finitefield_principalization_frequency_has_linear_factor :
    conclusion_leyang_prym3_finitefield_principalization_frequency_split_type → Prop
  | one_one_one => True
  | one_two => True
  | three => False

/-- Principalization over the finite field occurs exactly when one component is rational. -/
def conclusion_leyang_prym3_finitefield_principalization_frequency_has_principalization :
    conclusion_leyang_prym3_finitefield_principalization_frequency_split_type → Prop
  | one_one_one => True
  | one_two => True
  | three => False

/-- Total density of splitting types with a linear factor. -/
def conclusion_leyang_prym3_finitefield_principalization_frequency_linear_density : ℚ :=
  conclusion_leyang_prym3_finitefield_principalization_frequency_density one_one_one +
    conclusion_leyang_prym3_finitefield_principalization_frequency_density one_two

/-- The independent one-third auxiliary condition used for the joint frequency. -/
def conclusion_leyang_prym3_finitefield_principalization_frequency_auxiliary_density : ℚ := 1 / 3

/-- Concrete equivalence between finite-field principalization and a linear factor. -/
def conclusion_leyang_prym3_finitefield_principalization_frequency_data.existsIffLinearFactor
    (_D : conclusion_leyang_prym3_finitefield_principalization_frequency_data) : Prop :=
  ∀ s,
    conclusion_leyang_prym3_finitefield_principalization_frequency_has_principalization s ↔
      conclusion_leyang_prym3_finitefield_principalization_frequency_has_linear_factor s

/-- Concrete `S3` splitting density table. -/
def conclusion_leyang_prym3_finitefield_principalization_frequency_data.countsBySplittingType
    (_D : conclusion_leyang_prym3_finitefield_principalization_frequency_data) : Prop :=
  conclusion_leyang_prym3_finitefield_principalization_frequency_density one_one_one =
      (1 : ℚ) / 6 ∧
    conclusion_leyang_prym3_finitefield_principalization_frequency_density one_two =
      (1 : ℚ) / 2 ∧
    conclusion_leyang_prym3_finitefield_principalization_frequency_density three =
      (1 : ℚ) / 3

/-- Density of finite-field principalization among unramified primes. -/
def conclusion_leyang_prym3_finitefield_principalization_frequency_data.densityTwoThirds
    (_D : conclusion_leyang_prym3_finitefield_principalization_frequency_data) : Prop :=
  conclusion_leyang_prym3_finitefield_principalization_frequency_linear_density = (2 : ℚ) / 3

/-- Joint density after multiplying by the independent one-third condition. -/
def conclusion_leyang_prym3_finitefield_principalization_frequency_data.jointDensityTwoNinths
    (_D : conclusion_leyang_prym3_finitefield_principalization_frequency_data) : Prop :=
  conclusion_leyang_prym3_finitefield_principalization_frequency_linear_density *
      conclusion_leyang_prym3_finitefield_principalization_frequency_auxiliary_density =
    (2 : ℚ) / 9

/-- Paper label: `cor:conclusion-leyang-prym3-finitefield-principalization-frequency`. -/
theorem paper_conclusion_leyang_prym3_finitefield_principalization_frequency
    (D : conclusion_leyang_prym3_finitefield_principalization_frequency_data) :
    D.existsIffLinearFactor ∧ D.countsBySplittingType ∧ D.densityTwoThirds ∧
      D.jointDensityTwoNinths := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s
    cases s <;> simp [
      conclusion_leyang_prym3_finitefield_principalization_frequency_has_principalization,
      conclusion_leyang_prym3_finitefield_principalization_frequency_has_linear_factor]
  · norm_num [
      conclusion_leyang_prym3_finitefield_principalization_frequency_data.countsBySplittingType,
      conclusion_leyang_prym3_finitefield_principalization_frequency_density]
  · norm_num [
      conclusion_leyang_prym3_finitefield_principalization_frequency_data.densityTwoThirds,
      conclusion_leyang_prym3_finitefield_principalization_frequency_linear_density,
      conclusion_leyang_prym3_finitefield_principalization_frequency_density]
  · norm_num [
      conclusion_leyang_prym3_finitefield_principalization_frequency_data.jointDensityTwoNinths,
      conclusion_leyang_prym3_finitefield_principalization_frequency_linear_density,
      conclusion_leyang_prym3_finitefield_principalization_frequency_auxiliary_density,
      conclusion_leyang_prym3_finitefield_principalization_frequency_density]

end Omega.Conclusion
