import Omega.Conclusion.CompleteStrictificationDualCriterion
import Omega.Conclusion.DerivedStrictificationPontryaginCompleteClassification
import Omega.Conclusion.TqftGenusTowerTrivializationCriterion

namespace Omega.Conclusion

/-- The finite BC-quotient model used for the derived strictification package at level `m`. -/
def derivedStrictificationPontryaginSeed (m : ℕ) : DerivedStrictificationPontryaginData where
  subgroupRank := m
  bcRank := 1
  modulus := m

/-- Zero residual profile used in the terminal strictification wrapper. -/
def derivedStrictificationZeroResidual (m : ℕ) : Fin m → ℕ :=
  fun _ => 0

/-- Zero visible anomaly profile used in the terminal strictification wrapper. -/
def derivedStrictificationZeroAnomaly (m : ℕ) : Fin m → ℕ :=
  fun _ => 0

/-- Constant-one multiplicity profile for the zero-curvature tower. -/
def derivedStrictificationMultiplicity (m : ℕ) : Fin (m + 1) → ℕ :=
  fun _ => 1

/-- The derived strictification equivalences are the finite BC-factorization criterion together
with the Pontryagin short exactness of the quotient package. -/
def derivedStrictificationEquivalences (m : ℕ) : Prop :=
  let D := derivedStrictificationPontryaginSeed m
  D.fiberwiseConstancyIffFactorsThroughBC ∧ D.pontryaginDualShortExact

/-- CP-visible terminality is the zero-anomaly specialization of the complete strictification
dual criterion. -/
def derivedStrictificationCpVisibleEquivalence (m : ℕ) : Prop :=
  (zeroSizebiasedResidual (derivedStrictificationZeroResidual m) ∧
      zeroVisibleAnomaly (derivedStrictificationZeroAnomaly m)) ↔
    (localSizeBiasRigidity (derivedStrictificationZeroResidual m) ∧
      terminalNormalFormCpVisibleRealization (derivedStrictificationZeroAnomaly m))

/-- The zero-curvature tower is unique: the all-ones multiplicity profile forces the genus tower to
stay constant. -/
def derivedStrictificationTowerUniqueness (m : ℕ) : Prop :=
  ∀ g, genusPartitionValue (derivedStrictificationMultiplicity m) g = m + 1

/-- Paper label: `thm:derived-strictification-terminality-fivefold`. -/
theorem paper_derived_strictification_terminality_fivefold (m : ℕ) :
    derivedStrictificationEquivalences m ∧ derivedStrictificationCpVisibleEquivalence m ∧
      derivedStrictificationTowerUniqueness m := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [derivedStrictificationEquivalences, derivedStrictificationPontryaginSeed] using
      paper_derived_strictification_pontryagin_complete_classification
        (derivedStrictificationPontryaginSeed m)
  · simpa [derivedStrictificationCpVisibleEquivalence, derivedStrictificationZeroResidual,
      derivedStrictificationZeroAnomaly] using
      (paper_conclusion_complete_strictification_dual_criterion
        (derivedStrictificationZeroResidual m) (derivedStrictificationZeroAnomaly m))
  · have hpack :=
      paper_conclusion_tqft_genus_tower_trivialization_criterion
        (derivedStrictificationMultiplicity m) (by
          intro x
          simp [derivedStrictificationMultiplicity])
    rcases hpack with ⟨_, _, _, hTower⟩
    exact hTower.mp (by
      intro x
      simp [derivedStrictificationMultiplicity])

end Omega.Conclusion
