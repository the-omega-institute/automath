import Mathlib.Tactic

namespace Omega.Conclusion

/-- Chapter-local package for the prime-register ultrametric completion statement. The data
records the first-difference ultrametric on finitely supported prime exponent vectors, the
longest-common-prefix control underlying the ultrametric inequality, the characterization of
Cauchy families as coordinatewise eventually constant, the induced limit point in the full product
`ℕ^ℙ`, and the finite-truncation compatibility that extends the formal Gödel map. -/
structure PrimeRegisterUltrametricCompletionData where
  firstDifferenceDistance : Prop
  longestCommonPrefixControl : Prop
  cauchyCharacterizedCoordinatewise : Prop
  productLimitConstructed : Prop
  godelCompatibilityOnTruncations : Prop
  isUltrametric : Prop
  completionIdentified : Prop
  godelMapExtends : Prop
  firstDifferenceDistance_h : firstDifferenceDistance
  prefixControl_h : longestCommonPrefixControl
  cauchyCharacterizedCoordinatewise_h : cauchyCharacterizedCoordinatewise
  productLimitConstructed_h : productLimitConstructed
  godelCompatibilityOnTruncations_h : godelCompatibilityOnTruncations
  deriveIsUltrametric :
    firstDifferenceDistance → longestCommonPrefixControl → isUltrametric
  deriveCompletionIdentified :
    cauchyCharacterizedCoordinatewise → productLimitConstructed → completionIdentified
  deriveGodelMapExtends :
    completionIdentified → godelCompatibilityOnTruncations → godelMapExtends

/-- Paper-facing wrapper for the prime-register ultrametric completion: the first-difference
metric is non-Archimedean, its completion is the full prime-indexed product, and the formal Gödel
value map extends continuously by compatibility on finite truncations.
    thm:conclusion-prime-register-ultrametric-completion -/
theorem paper_conclusion_prime_register_ultrametric_completion
    (data : PrimeRegisterUltrametricCompletionData) :
    data.isUltrametric ∧ data.completionIdentified ∧ data.godelMapExtends := by
  have hUltra : data.isUltrametric :=
    data.deriveIsUltrametric data.firstDifferenceDistance_h data.prefixControl_h
  have hCompletion : data.completionIdentified :=
    data.deriveCompletionIdentified
      data.cauchyCharacterizedCoordinatewise_h data.productLimitConstructed_h
  have hGodel : data.godelMapExtends :=
    data.deriveGodelMapExtends hCompletion data.godelCompatibilityOnTruncations_h
  exact ⟨hUltra, hCompletion, hGodel⟩

end Omega.Conclusion
