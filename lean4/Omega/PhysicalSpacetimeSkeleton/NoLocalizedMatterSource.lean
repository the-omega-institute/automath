import Mathlib.Tactic
import Omega.PhysicalSpacetimeSkeleton.EffectiveCosmologicalClosure
import Omega.PhysicalSpacetimeSkeleton.ResourceStressEnergyPureTrace
import Omega.PhysicalSpacetimeSkeleton.WeakFieldQuadraticHarmonicNormalForm

namespace Omega.PhysicalSpacetimeSkeleton

/-- Package the pure-trace stress reduction, effective cosmological closure, and weak-field
quadratic-harmonic normal form into the statement that no independent localized matter source
survives inside the admissible closure. -/
theorem paper_physical_spacetime_no_localized_matter_source_package
    (D : ResourceStressEnergyPureTraceData) (E : AdmissibleEinsteinClosure) (hAdm : E.admissible)
    (hMetric : E.metric = D.metric) (hResidual : E.residualLagrangian = D.residualLagrangian)
    (hStress : E.stressEnergy = D.stressEnergy)
    (Delta : (Fin 3 → Real) →ₗ[Real] Real) (phi q : Fin 3 → Real) (sigma L : Real)
    (hq : Delta q = sigma * L) (hphi : Delta phi = sigma * L) :
    D.tracelessPart = 0 ∧
      E.einsteinTensor +
          (E.cosmologicalConstant - E.couplingConstant * E.residualLagrangian) * E.metric =
        0 ∧
      ∃ h : Fin 3 → Real, phi = q + h ∧ Delta h = 0 := by
  have hPureD := paper_physical_spacetime_resource_stress_energy_pure_trace D
  rcases hPureD with ⟨hPureStress, hTraceZero⟩
  have hPureE : E.stressEnergy = E.residualLagrangian * E.metric := by
    rw [hStress, hPureStress, hResidual, hMetric]
  refine ⟨hTraceZero, paper_physical_spacetime_effective_cosmological_closure E hAdm hPureE, ?_⟩
  exact paper_physical_spacetime_weak_field_quadratic_harmonic_normal_form Delta phi q sigma L hq
    hphi

/-- Paper label wrapper for the no-localized-matter-source corollary.
    cor:physical-spacetime-no-localized-matter-source -/
def paper_physical_spacetime_no_localized_matter_source : Prop := by
  exact
    ∀ (D : ResourceStressEnergyPureTraceData) (E : AdmissibleEinsteinClosure)
      (_hAdm : E.admissible) (_hMetric : E.metric = D.metric)
      (_hResidual : E.residualLagrangian = D.residualLagrangian)
      (_hStress : E.stressEnergy = D.stressEnergy) (Delta : (Fin 3 → Real) →ₗ[Real] Real)
      (phi q : Fin 3 → Real) (sigma L : Real), Delta q = sigma * L →
        Delta phi = sigma * L →
        D.tracelessPart = 0 ∧
          E.einsteinTensor +
              (E.cosmologicalConstant - E.couplingConstant * E.residualLagrangian) * E.metric =
            0 ∧
          ∃ h : Fin 3 → Real, phi = q + h ∧ Delta h = 0

theorem paper_physical_spacetime_no_localized_matter_source_verified :
    paper_physical_spacetime_no_localized_matter_source := by
  intro D E hAdm hMetric hResidual hStress Delta phi q sigma L hq hphi
  exact
    paper_physical_spacetime_no_localized_matter_source_package D E hAdm hMetric hResidual
      hStress Delta phi q sigma L hq hphi

end Omega.PhysicalSpacetimeSkeleton
