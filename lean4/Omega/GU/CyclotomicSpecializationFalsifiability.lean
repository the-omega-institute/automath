import Omega.GU.CyclotomicGcdStability

namespace Omega.GU

universe u

/-- Chapter-local package for the finite-falsifiability corollary.  The exceptional cyclotomic
layers are those carrying the observed common slow mode after factoring out the rigid part; if
there were infinitely many of them, the residual family would exhibit an extra gcd on infinitely
many levels. -/
structure CyclotomicSpecializationFalsifiabilityData extends CyclotomicGcdStabilityData where
  Layer : Type u
  decEqLayer : DecidableEq Layer
  exceptionalLayer : Layer → Prop
  exceptionalLayersForceExtraGcdAtInfinitelyManyLevels :
    Set.Infinite {ℓ : Layer | exceptionalLayer ℓ} → extraGcdAtInfinitelyManyLevels

attribute [instance] CyclotomicSpecializationFalsifiabilityData.decEqLayer

/-- If the residual gcd is trivial, then the exceptional cyclotomic layers carrying the observed
common slow mode form a finite witness set, so the specialization claim is finitely falsifiable.
    cor:cyclotomic-specialization-falsifiability -/
theorem paper_gut_cyclotomic_specialization_falsifiability
    (D : CyclotomicSpecializationFalsifiabilityData) :
    D.residualGcdTrivial →
      ∃ witnessSet : Finset D.Layer, ∀ ℓ, D.exceptionalLayer ℓ → ℓ ∈ witnessSet := by
  intro hResidual
  have hnotInfinite : ¬ Set.Infinite {ℓ : D.Layer | D.exceptionalLayer ℓ} := by
    intro hInfinite
    exact (paper_gut_cyclotomic_gcd_stability D.toCyclotomicGcdStabilityData hResidual)
      (D.exceptionalLayersForceExtraGcdAtInfinitelyManyLevels hInfinite)
  have hfinite : Set.Finite {ℓ : D.Layer | D.exceptionalLayer ℓ} := Set.not_infinite.mp hnotInfinite
  refine ⟨hfinite.toFinset, ?_⟩
  intro ℓ hℓ
  exact hfinite.mem_toFinset.mpr hℓ

/-- Paper label: `cor:cyclotomic-specialization-falsifiability`. -/
theorem paper_cyclotomic_specialization_falsifiability
    (D : CyclotomicSpecializationFalsifiabilityData) :
    D.residualGcdTrivial →
      ∃ witnessSet : Finset D.Layer, ∀ l, D.exceptionalLayer l → l ∈ witnessSet := by
  exact paper_gut_cyclotomic_specialization_falsifiability D

end Omega.GU
