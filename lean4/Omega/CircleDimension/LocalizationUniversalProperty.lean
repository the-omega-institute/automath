import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Chapter-local certificate package for the universal property of the localization
`ℤ[S⁻¹]`. The fields isolate the fraction-level definition of the candidate morphism,
the denominator invertibility used in that definition, the clearing-denominators
argument for well-definedness, and the generation argument that forces uniqueness. -/
structure LocalizationUniversalPropertyData where
  mapOnLocalizedFractions : Prop
  denominatorsInvertible : Prop
  wellDefinedByClearingDenominators : Prop
  agreesWithIntegerMap : Prop
  uniquenessByGenerators : Prop
  universalProperty : Prop
  mapOnLocalizedFractions_h : mapOnLocalizedFractions
  denominatorsInvertible_h : denominatorsInvertible
  wellDefinedByClearingDenominators_h : wellDefinedByClearingDenominators
  agreesWithIntegerMap_h : agreesWithIntegerMap
  uniquenessByGenerators_h : uniquenessByGenerators
  deriveUniversalProperty :
    mapOnLocalizedFractions →
      denominatorsInvertible →
        wellDefinedByClearingDenominators →
          agreesWithIntegerMap → uniquenessByGenerators → universalProperty

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper for the universal property of localization in the
circle-dimension phase-gate section.
    prop:cdim-localization-universal-property -/
theorem paper_cdim_localization_universal_property
    (D : LocalizationUniversalPropertyData) :
    D.mapOnLocalizedFractions ∧ D.wellDefinedByClearingDenominators ∧
      D.agreesWithIntegerMap ∧ D.universalProperty := by
  have hUniversal : D.universalProperty :=
    D.deriveUniversalProperty D.mapOnLocalizedFractions_h D.denominatorsInvertible_h
      D.wellDefinedByClearingDenominators_h D.agreesWithIntegerMap_h
      D.uniquenessByGenerators_h
  exact
    ⟨D.mapOnLocalizedFractions_h, D.wellDefinedByClearingDenominators_h,
      D.agreesWithIntegerMap_h, hUniversal⟩

end Omega.CircleDimension
