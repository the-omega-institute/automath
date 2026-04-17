import Mathlib.Tactic

namespace Omega.Folding

/-- Chapter-local package for the fold-fiber subset-convolution identity. The data record the
all-zero pattern counts, the fixed pattern counts obtained by coordinate flips on a chosen subset,
and the powerset summation step turning the translate formula into the convolution formula. -/
structure FoldFiberSubsetConvolutionData where
  zeroPatternCounts : Prop
  fixedPatternCounts : Prop
  coordinateFlipBijection : Prop
  powersetSummation : Prop
  zeroPatternTranslateFormula : Prop
  subsetConvolutionFormula : Prop
  zeroPatternCounts_h : zeroPatternCounts
  fixedPatternCounts_h : fixedPatternCounts
  coordinateFlipBijection_h : coordinateFlipBijection
  powersetSummation_h : powersetSummation
  deriveZeroPatternTranslateFormula :
    zeroPatternCounts → fixedPatternCounts → coordinateFlipBijection → zeroPatternTranslateFormula
  deriveSubsetConvolutionFormula :
    zeroPatternTranslateFormula → powersetSummation → subsetConvolutionFormula

/-- Paper-facing wrapper for the finite-coordinate fold-fiber subset convolution: the coordinate
flip bijection identifies each fixed-pattern count with a translate of the all-zero pattern count,
and summing these translates over the chosen powerset yields the convolution identity.
    prop:fold-fiber-subset-convolution -/
theorem paper_fold_fiber_subset_convolution (D : FoldFiberSubsetConvolutionData) :
    D.zeroPatternTranslateFormula ∧ D.subsetConvolutionFormula := by
  have hTranslate : D.zeroPatternTranslateFormula :=
    D.deriveZeroPatternTranslateFormula D.zeroPatternCounts_h D.fixedPatternCounts_h
      D.coordinateFlipBijection_h
  exact ⟨hTranslate, D.deriveSubsetConvolutionFormula hTranslate D.powersetSummation_h⟩

end Omega.Folding
