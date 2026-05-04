import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-minimal-stratified-lie-groupoid-lift`. -/
theorem paper_conclusion_minimal_stratified_lie_groupoid_lift
    (regularFreeTranslationLayer window6VariableStabilizerLayer comparisonMapsRetained
      homogeneousLieQuotientSufficient stratifiedLieGroupoidLiftRequired
      twoCategoricalFrameworkRequired : Prop)
    (hregular : regularFreeTranslationLayer)
    (hsingular : window6VariableStabilizerLayer)
    (hcompare : comparisonMapsRetained)
    (hnotHomogeneous :
      regularFreeTranslationLayer ->
        window6VariableStabilizerLayer ->
          comparisonMapsRetained -> ¬ homogeneousLieQuotientSufficient)
    (hlift :
      regularFreeTranslationLayer ->
        window6VariableStabilizerLayer -> stratifiedLieGroupoidLiftRequired)
    (htwo : comparisonMapsRetained -> twoCategoricalFrameworkRequired) :
    ¬ homogeneousLieQuotientSufficient ∧ stratifiedLieGroupoidLiftRequired ∧
      twoCategoricalFrameworkRequired := by
  exact ⟨hnotHomogeneous hregular hsingular hcompare, hlift hregular hsingular,
    htwo hcompare⟩

end Omega.Conclusion
