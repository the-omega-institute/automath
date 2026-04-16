namespace Omega.Discussion

/-- Chapter-local package for the cubical discrete-Stokes elimination criterion. The three
conditions encode exactness of the closed `2`-cochain, vanishing of its Kronecker pairing on all
integral `2`-cycles, and vanishing of its cohomology class. The structure records exactly the
cohomological implications used in the paper proof. -/
structure CubicalStokesElimination2CycleData where
  exactnessCriterion : Prop
  pairingVanishesOnTwoCycles : Prop
  cohomologyClassVanishes : Prop
  universalCoefficientPackage : Prop
  universalCoefficientPackage_h : universalCoefficientPackage
  exactness_iff_cohomology :
    exactnessCriterion ↔ cohomologyClassVanishes
  cohomologyImpliesPairing :
    cohomologyClassVanishes → pairingVanishesOnTwoCycles
  pairingImpliesCohomology :
    pairingVanishesOnTwoCycles → universalCoefficientPackage → cohomologyClassVanishes

/-- Paper-facing wrapper for the cubical Stokes elimination criterion: exactness of a closed
`2`-cochain, vanishing of its pairing on every `2`-cycle, and vanishing of its cohomology class
are equivalent once the universal-coefficient/Ext-vanishing package is available.
    prop:discussion-cubical-stokes-elimination-2cycle -/
theorem paper_discussion_cubical_stokes_elimination_2cycle
    (D : CubicalStokesElimination2CycleData) :
    (D.exactnessCriterion ↔ D.cohomologyClassVanishes) ∧
      (D.pairingVanishesOnTwoCycles ↔ D.cohomologyClassVanishes) ∧
      (D.exactnessCriterion ↔ D.pairingVanishesOnTwoCycles) := by
  have hPairingIffCohomology :
      D.pairingVanishesOnTwoCycles ↔ D.cohomologyClassVanishes := by
    constructor
    · intro hPairing
      exact D.pairingImpliesCohomology hPairing D.universalCoefficientPackage_h
    · intro hCohomology
      exact D.cohomologyImpliesPairing hCohomology
  have hExactnessIffPairing :
      D.exactnessCriterion ↔ D.pairingVanishesOnTwoCycles := by
    constructor
    · intro hExact
      have hCohomology : D.cohomologyClassVanishes :=
        D.exactness_iff_cohomology.mp hExact
      exact hPairingIffCohomology.mpr hCohomology
    · intro hPairing
      have hCohomology : D.cohomologyClassVanishes :=
        hPairingIffCohomology.mp hPairing
      exact D.exactness_iff_cohomology.mpr hCohomology
  exact ⟨D.exactness_iff_cohomology, hPairingIffCohomology, hExactnessIffPairing⟩

end Omega.Discussion
