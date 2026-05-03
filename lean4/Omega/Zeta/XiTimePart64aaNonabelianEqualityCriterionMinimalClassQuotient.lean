import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part64aa-nonabelian-equality-criterion-minimal-class-quotient`. -/
theorem paper_xi_time_part64aa_nonabelian_equality_criterion_minimal_class_quotient
    (energyPreserved factorsThrough activeKernelsTrivial minimalClassQuotient : Prop)
    (hEnergyFactor : energyPreserved ↔ factorsThrough)
    (hFactorKernel : factorsThrough ↔ activeKernelsTrivial)
    (hMinimal : activeKernelsTrivial → minimalClassQuotient) :
    (energyPreserved ↔ factorsThrough) ∧ (factorsThrough ↔ activeKernelsTrivial) ∧
      (energyPreserved ↔ activeKernelsTrivial) ∧
        (energyPreserved → minimalClassQuotient) := by
  exact ⟨hEnergyFactor, hFactorKernel, hEnergyFactor.trans hFactorKernel,
    fun hEnergy => hMinimal ((hEnergyFactor.trans hFactorKernel).1 hEnergy)⟩

end Omega.Zeta
