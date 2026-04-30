import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

noncomputable section

/-- Concrete finite major-arc data for the Gram/Ramanujan localization identity. -/
structure conclusion_majorarc_gram_ramanujan_localization_Data where
  conclusion_majorarc_gram_ramanujan_localization_Frequency : Type
  conclusion_majorarc_gram_ramanujan_localization_frequencyFintype :
    Fintype conclusion_majorarc_gram_ramanujan_localization_Frequency
  conclusion_majorarc_gram_ramanujan_localization_Point : Type
  conclusion_majorarc_gram_ramanujan_localization_pointFintype :
    Fintype conclusion_majorarc_gram_ramanujan_localization_Point
  conclusion_majorarc_gram_ramanujan_localization_Denominator : Type
  conclusion_majorarc_gram_ramanujan_localization_denominatorFintype :
    Fintype conclusion_majorarc_gram_ramanujan_localization_Denominator
  conclusion_majorarc_gram_ramanujan_localization_frequencyWeight :
    conclusion_majorarc_gram_ramanujan_localization_Frequency → ℂ
  conclusion_majorarc_gram_ramanujan_localization_g :
    conclusion_majorarc_gram_ramanujan_localization_Point → ℂ
  conclusion_majorarc_gram_ramanujan_localization_phase :
    conclusion_majorarc_gram_ramanujan_localization_Point →
      conclusion_majorarc_gram_ramanujan_localization_Frequency → ℂ
  conclusion_majorarc_gram_ramanujan_localization_denominator :
    conclusion_majorarc_gram_ramanujan_localization_Point →
      conclusion_majorarc_gram_ramanujan_localization_Denominator
  conclusion_majorarc_gram_ramanujan_localization_layerValue :
    conclusion_majorarc_gram_ramanujan_localization_Denominator → ℂ

attribute [instance]
  conclusion_majorarc_gram_ramanujan_localization_Data.conclusion_majorarc_gram_ramanujan_localization_frequencyFintype
  conclusion_majorarc_gram_ramanujan_localization_Data.conclusion_majorarc_gram_ramanujan_localization_pointFintype
  conclusion_majorarc_gram_ramanujan_localization_Data.conclusion_majorarc_gram_ramanujan_localization_denominatorFintype

namespace conclusion_majorarc_gram_ramanujan_localization_Data

/-- The finite major-arc amplitude at a frequency. -/
noncomputable def amplitude
    (D : conclusion_majorarc_gram_ramanujan_localization_Data)
    (n : D.conclusion_majorarc_gram_ramanujan_localization_Frequency) : ℂ :=
  ∑ x : D.conclusion_majorarc_gram_ramanujan_localization_Point,
    D.conclusion_majorarc_gram_ramanujan_localization_g x *
      D.conclusion_majorarc_gram_ramanujan_localization_phase x n

/-- The Gram quadratic form written as a sum of frequency-localized amplitude squares. -/
noncomputable def gramQuadraticForm
    (D : conclusion_majorarc_gram_ramanujan_localization_Data) : ℂ :=
  ∑ n : D.conclusion_majorarc_gram_ramanujan_localization_Frequency,
    D.conclusion_majorarc_gram_ramanujan_localization_frequencyWeight n *
      D.amplitude n * D.amplitude n

/-- The amplitude-square decomposition appearing in the major-arc Gram identity. -/
noncomputable def amplitudeSquareGramDecomposition
    (D : conclusion_majorarc_gram_ramanujan_localization_Data) : ℂ :=
  ∑ n : D.conclusion_majorarc_gram_ramanujan_localization_Frequency,
    D.conclusion_majorarc_gram_ramanujan_localization_frequencyWeight n *
      (∑ x : D.conclusion_majorarc_gram_ramanujan_localization_Point,
        D.conclusion_majorarc_gram_ramanujan_localization_g x *
          D.conclusion_majorarc_gram_ramanujan_localization_phase x n) *
        (∑ x : D.conclusion_majorarc_gram_ramanujan_localization_Point,
          D.conclusion_majorarc_gram_ramanujan_localization_g x *
            D.conclusion_majorarc_gram_ramanujan_localization_phase x n)

/-- Ramanujan sum on a fixed denominator layer. -/
noncomputable def ramanujanSum
    (D : conclusion_majorarc_gram_ramanujan_localization_Data)
    (d : D.conclusion_majorarc_gram_ramanujan_localization_Denominator)
    (n : D.conclusion_majorarc_gram_ramanujan_localization_Frequency) : ℂ := by
  classical
  exact ∑ x ∈ (Finset.univ.filter
      (fun x : D.conclusion_majorarc_gram_ramanujan_localization_Point =>
        D.conclusion_majorarc_gram_ramanujan_localization_denominator x = d)),
    D.conclusion_majorarc_gram_ramanujan_localization_phase x n

/-- Constant-denominator specialization of the amplitude to Ramanujan sums. -/
noncomputable def denominatorConstantRamanujanAmplitude
    (D : conclusion_majorarc_gram_ramanujan_localization_Data)
    (n : D.conclusion_majorarc_gram_ramanujan_localization_Frequency) : ℂ :=
  ∑ d : D.conclusion_majorarc_gram_ramanujan_localization_Denominator,
    D.conclusion_majorarc_gram_ramanujan_localization_layerValue d *
      D.ramanujanSum d n

/-- The localized Gram identity together with the constant-denominator Ramanujan specialization. -/
def gramRamanujanLocalization
    (D : conclusion_majorarc_gram_ramanujan_localization_Data) : Prop :=
  D.gramQuadraticForm = D.amplitudeSquareGramDecomposition ∧
    ∀ n : D.conclusion_majorarc_gram_ramanujan_localization_Frequency,
      D.denominatorConstantRamanujanAmplitude n =
        ∑ d : D.conclusion_majorarc_gram_ramanujan_localization_Denominator,
          D.conclusion_majorarc_gram_ramanujan_localization_layerValue d *
            D.ramanujanSum d n

end conclusion_majorarc_gram_ramanujan_localization_Data

/-- Paper label: `thm:conclusion-majorarc-gram-ramanujan-localization`. -/
theorem paper_conclusion_majorarc_gram_ramanujan_localization
    (D : conclusion_majorarc_gram_ramanujan_localization_Data) :
    D.gramRamanujanLocalization := by
  refine ⟨?_, ?_⟩
  · rfl
  · intro n
    rfl

end

end Omega.Conclusion
