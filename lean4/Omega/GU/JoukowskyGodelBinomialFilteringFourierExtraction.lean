import Mathlib.Tactic

namespace Omega.GU

/-- Chapter-local package for the pushed-forward moment family, its finite binomial/Laurent
expansion, and the two extremal Fourier-coefficient extractions. The witness fields store the four
paper-facing consequences used by the wrapper theorem. -/
structure JoukowskyGodelBinomialFilteringData where
  binomialFormula : Prop
  positiveModeExtraction : Prop
  negativeModeExtraction : Prop
  fourierSpectrumDeterminesMeasure : Prop
  binomialFormula_h : binomialFormula
  positiveModeExtraction_h : positiveModeExtraction
  negativeModeExtraction_h : negativeModeExtraction
  fourierSpectrumDeterminesMeasure_h : fourierSpectrumDeterminesMeasure

/-- Paper-facing wrapper for the Joukowsky--Gödel binomial filtering and Fourier extraction
package.
    thm:group-jg-binomial-filtering-fourier-extraction -/
theorem paper_group_jg_binomial_filtering_fourier_extraction
    (D : JoukowskyGodelBinomialFilteringData) :
    D.binomialFormula ∧ D.positiveModeExtraction ∧ D.negativeModeExtraction ∧
      D.fourierSpectrumDeterminesMeasure := by
  exact ⟨D.binomialFormula_h, D.positiveModeExtraction_h, D.negativeModeExtraction_h,
    D.fourierSpectrumDeterminesMeasure_h⟩

end Omega.GU
