import Mathlib.Tactic
import Omega.Conclusion.TowerDefectExactTvDuality

namespace Omega.POM

/-- Paper label: `cor:conclusion-pom-curvature-and-tower-defect-same-kernel`. The exact
total-variation package identifies vanishing tower defect with constant inner fibers, and each
of the four curvature/tower predicates is assumed to name the same zero-TV kernel. -/
theorem paper_conclusion_pom_curvature_and_tower_defect_same_kernel
    (D : Omega.Conclusion.TowerDefectExactTvDualityData)
    (omegaKL allOmegaKL allTower locoscZero : Prop) (hD : D.exactTvDuality)
    (hKL : omegaKL ↔ D.totalVariation = 0) (hAllKL : allOmegaKL ↔ D.totalVariation = 0)
    (hTower : allTower ↔ D.totalVariation = 0)
    (hLocosc : locoscZero ↔ D.totalVariation = 0) :
    D.constantInnerFiber ↔ omegaKL ∧ allOmegaKL ∧ allTower ∧ locoscZero := by
  constructor
  · intro hconstant
    have htv : D.totalVariation = 0 := hD.2.mpr hconstant
    exact ⟨hKL.mpr htv, hAllKL.mpr htv, hTower.mpr htv, hLocosc.mpr htv⟩
  · rintro ⟨homega, _hallOmega, _hallTower, _hlocosc⟩
    exact hD.2.mp (hKL.mp homega)

end Omega.POM
