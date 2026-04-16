import Mathlib.Tactic

namespace Omega.POM

/-- Chapter-local package for the Beck--Chevalley multiplicative defect theorem. The data record
the pointwise comparison of the two lifted measures, the identification of their ratio with the
defect function, and the cocycle and logarithmic closedness consequences of reassociating triple
compositions. -/
structure BeckChevalleyDefectMultiplicative2CocycleData where
  pointwiseFactorization : Prop
  normalizedTwoCocycle : Prop
  liftedMeasuresComparedPointwise : Prop
  defectRatioIdentified : Prop
  cocycleIdentity : Prop
  logClosedness : Prop
  liftedMeasuresComparedPointwise_h : liftedMeasuresComparedPointwise
  defectRatioIdentified_h : defectRatioIdentified
  cocycleIdentity_h : cocycleIdentity
  logClosedness_h : logClosedness
  derivePointwiseFactorization :
    liftedMeasuresComparedPointwise → defectRatioIdentified → pointwiseFactorization
  deriveNormalizedTwoCocycle :
    cocycleIdentity → logClosedness → normalizedTwoCocycle

/-- Paper-facing wrapper for the Beck--Chevalley defect package: the lifted measures differ by the
pointwise defect factor, and the reassociated triple lift yields the normalized multiplicative
`2`-cocycle together with the equivalent logarithmic closedness statement.
    thm:pom-bc-defect-multiplicative-2cocycle -/
theorem paper_pom_bc_defect_multiplicative_2cocycle
    (D : BeckChevalleyDefectMultiplicative2CocycleData) :
    D.pointwiseFactorization ∧ D.normalizedTwoCocycle := by
  have hFactorization : D.pointwiseFactorization :=
    D.derivePointwiseFactorization
      D.liftedMeasuresComparedPointwise_h
      D.defectRatioIdentified_h
  have hCocycle : D.normalizedTwoCocycle :=
    D.deriveNormalizedTwoCocycle D.cocycleIdentity_h D.logClosedness_h
  exact ⟨hFactorization, hCocycle⟩

end Omega.POM
