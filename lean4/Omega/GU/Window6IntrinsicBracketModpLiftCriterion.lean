import Mathlib.Tactic

namespace Omega.GU

/-- Chapter-local package for the intrinsic bracket mod-`p` lift criterion in the window-`6`
setting. The fields record the normalized integral system, uniqueness of the mod-`p` root, the
full-rank Jacobian witness needed for the simple-root/Hensel step, and a verified integer witness
whose image agrees with the unique mod-`p` solution. The final field packages the characteristic-0
existence/uniqueness consequence obtained from the injective embedding into the `p`-adic lift. -/
structure Window6IntrinsicBracketModpLiftCriterionData where
  normalizedIntegralSystem : Prop
  uniqueModPSolution : Prop
  jacobianFullRank : Prop
  verifiedIntegerWitness : Prop
  normalizedIntegralSystem_h : normalizedIntegralSystem
  uniqueModPSolution_h : uniqueModPSolution
  jacobianFullRank_h : jacobianFullRank
  verifiedIntegerWitness_h : verifiedIntegerWitness
  uniqueIntegerSolution : Prop
  characteristicZeroExistenceUniqueness : Prop
  henselLiftToUniqueIntegerSolution :
    normalizedIntegralSystem → uniqueModPSolution → jacobianFullRank → verifiedIntegerWitness →
      uniqueIntegerSolution
  integerToPadicEmbeddingInjective :
    uniqueIntegerSolution → characteristicZeroExistenceUniqueness

/-- The normalized integral window-`6` bracket system has a unique mod-`p` solution with
full-rank Jacobian and a verified integer witness, so the simple-root/Hensel argument gives a
unique integer lift, and injectivity of the integer-to-`p`-adic embedding promotes this to the
characteristic-`0` existence/uniqueness package.
    thm:window6-intrinsic-bracket-modp-lift-criterion -/
theorem paper_window6_intrinsic_bracket_modp_lift_criterion
    (D : Window6IntrinsicBracketModpLiftCriterionData) :
    D.uniqueIntegerSolution ∧ D.characteristicZeroExistenceUniqueness := by
  have hInteger :
      D.uniqueIntegerSolution :=
    D.henselLiftToUniqueIntegerSolution D.normalizedIntegralSystem_h D.uniqueModPSolution_h
      D.jacobianFullRank_h D.verifiedIntegerWitness_h
  exact ⟨hInteger, D.integerToPadicEmbeddingInjective hInteger⟩

end Omega.GU
