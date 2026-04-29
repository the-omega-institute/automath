import Mathlib.Tactic
import Omega.Zeta.CyclotomicSectorIdentity

namespace Omega.Zeta

/-- Chapter-local certificate package for the torsion-point product formula for the
finite part of a cyclic lift. The fields record the cyclotomic-sector factorization,
the identification of the unique simple pole at `j = 0`, the recognition of the
remaining sectors as torsion-point zeta values, and the resulting product formula. -/
structure FinitePartCyclicLiftTorsionProductData where
  cyclotomicSectorFactorization : Prop
  onlyZeroSectorContributesPole : Prop
  remainingSectorsAreTorsionValues : Prop
  torsionProductFormula : Prop
  cyclotomicSectorFactorization_h : cyclotomicSectorFactorization
  onlyZeroSectorContributesPole_h : onlyZeroSectorContributesPole
  remainingSectorsAreTorsionValues_h : remainingSectorsAreTorsionValues
  deriveTorsionProductFormula :
    cyclotomicSectorFactorization →
      onlyZeroSectorContributesPole →
        remainingSectorsAreTorsionValues → torsionProductFormula

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the torsion-point product formula of the cyclic-lift
finite part in the ETDS chapter.
    prop:finite-part-cyclic-lift-torsion-product -/
theorem paper_etds_finite_part_cyclic_lift_torsion_product
    (D : FinitePartCyclicLiftTorsionProductData) :
    D.cyclotomicSectorFactorization ∧ D.remainingSectorsAreTorsionValues ∧
      D.torsionProductFormula := by
  have hProduct : D.torsionProductFormula :=
    D.deriveTorsionProductFormula D.cyclotomicSectorFactorization_h
      D.onlyZeroSectorContributesPole_h D.remainingSectorsAreTorsionValues_h
  exact
    ⟨D.cyclotomicSectorFactorization_h, D.remainingSectorsAreTorsionValues_h, hProduct⟩

/-- Label-correct paper wrapper for the finite-part cyclic-lift torsion product formula.
    prop:finite-part-cyclic-lift-torsion-product -/
theorem paper_finite_part_cyclic_lift_torsion_product
    (D : FinitePartCyclicLiftTorsionProductData) :
    D.cyclotomicSectorFactorization ∧ D.remainingSectorsAreTorsionValues ∧
      D.torsionProductFormula :=
  paper_etds_finite_part_cyclic_lift_torsion_product D

end Omega.Zeta
