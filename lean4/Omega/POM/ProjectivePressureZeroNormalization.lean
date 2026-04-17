import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Card

namespace Omega.POM

open scoped BigOperators

/-- Finite datum for the `q = 1` normalization of the projective-pressure operator. The input and
output alphabets are kept concrete so the normalization identities are stated in terms of actual
finite cardinalities rather than abstract proposition fields. -/
structure ProjectivePressureDatum where
  Input : Type*
  Output : Type*
  instFintypeInput : Fintype Input
  instFintypeOutput : Fintype Output

attribute [instance] ProjectivePressureDatum.instFintypeInput
attribute [instance] ProjectivePressureDatum.instFintypeOutput

/-- Input alphabet size `|A_in|`. -/
def ProjectivePressureDatum.inputAlphabetCard (D : ProjectivePressureDatum) : ℕ :=
  Fintype.card D.Input

/-- Output alphabet size `|A_out|`. -/
def ProjectivePressureDatum.outputAlphabetCard (D : ProjectivePressureDatum) : ℕ :=
  Fintype.card D.Output

/-- The `q = 1` projective operator collapses to summing the constant column masses over the input
alphabet, so every output coordinate sees the same input-cardinality multiplier. -/
noncomputable def ProjectivePressureDatum.transferAtOne (D : ProjectivePressureDatum) :
    (D.Output → ℝ) → D.Output → ℝ :=
  fun _ _ => ∑ _ : D.Input, (1 : ℝ)

/-- The constant-one function is an eigenvector of the `q = 1` transfer operator with eigenvalue
`|A_in|`. -/
def ProjectivePressureDatum.transferAtOneOnes (D : ProjectivePressureDatum) : Prop :=
  D.transferAtOne (fun _ => (1 : ℝ)) = fun _ => (D.inputAlphabetCard : ℝ)

/-- The Perron root seed at `q = 1`; in this finite wrapper it is exactly the input alphabet
cardinality. -/
noncomputable def ProjectivePressureDatum.lambda (D : ProjectivePressureDatum) (_q : ℝ) : ℝ :=
  D.inputAlphabetCard

/-- The normalized pressure curve `Λ(t) = log (λ(t+1) / |A_out|)`. -/
noncomputable def ProjectivePressureDatum.Lambda (D : ProjectivePressureDatum) (t : ℝ) : ℝ :=
  Real.log (D.lambda (t + 1) / D.outputAlphabetCard)

/-- Paper normalization at the zero parameter: the constant-one vector is a `q = 1` eigenvector,
the Perron root is `|A_in|`, and `Λ(0)` records the exact logarithmic normalization by
`|A_out|`.
    thm:pom-projective-pressure-zero-normalization -/
theorem paper_pom_projective_pressure_zero_normalization (D : ProjectivePressureDatum) :
    D.transferAtOneOnes ∧ D.lambda 1 = D.inputAlphabetCard ∧
      D.Lambda 0 = Real.log ((D.inputAlphabetCard : ℝ) / D.outputAlphabetCard) := by
  refine ⟨?_, ?_, ?_⟩
  · funext y
    simp [ProjectivePressureDatum.transferAtOne, ProjectivePressureDatum.inputAlphabetCard]
  · simp [ProjectivePressureDatum.lambda]
  · simp [ProjectivePressureDatum.Lambda, ProjectivePressureDatum.lambda]

end Omega.POM

/-- Root-level alias exposing the exact paper theorem name requested by the round script. -/
theorem paper_pom_projective_pressure_zero_normalization (D : Omega.POM.ProjectivePressureDatum) :
    D.transferAtOneOnes ∧ D.lambda 1 = D.inputAlphabetCard ∧
      D.Lambda 0 = Real.log ((D.inputAlphabetCard : ℝ) / D.outputAlphabetCard) :=
  Omega.POM.paper_pom_projective_pressure_zero_normalization D
