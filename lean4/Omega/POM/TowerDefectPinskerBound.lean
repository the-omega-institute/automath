import Omega.POM.TowerDefectCovarianceLaw

namespace Omega.POM

/-- The outer uniform expectation on the `h`-fiber above `z`. -/
noncomputable def pom_tower_defect_pinsker_bound_uniformExpectation
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (g : X → Y) (h : Y → Z) (ψ : X → ℚ) (z : Z) : ℚ :=
  towerFiberAverage h (towerInnerAverage g ψ) z

/-- The size-biased outer expectation induced by the composite fibers of `h ∘ g`. -/
noncomputable def pom_tower_defect_pinsker_bound_sizeBiasedExpectation
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (g : X → Y) (h : Y → Z) (ψ : X → ℚ) (z : Z) : ℚ :=
  towerCompositeAverage g h ψ z

/-- The tower defect written as the difference between the uniform and size-biased outer
expectations. -/
noncomputable def pom_tower_defect_pinsker_bound_towerDefect
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (g : X → Y) (h : Y → Z) (ψ : X → ℚ) (z : Z) : ℚ :=
  pom_tower_defect_pinsker_bound_uniformExpectation g h ψ z -
    pom_tower_defect_pinsker_bound_sizeBiasedExpectation g h ψ z

/-- Paper label: `cor:pom-tower-defect-pinsker-bound`. The covariance-law identity rewrites the
tower defect as the uniform-versus-size-biased expectation gap, after which any oscillation-times-TV
estimate and any Pinsker-scale control of TV transfer directly to the tower defect. -/
theorem paper_pom_tower_defect_pinsker_bound
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (g : X → Y) (h : Y → Z) (ψ : X → ℚ) (hg : Function.Surjective g)
    (z : Z) (hz : 0 < towerFiberCard h z)
    (oscillation tv pinskerScale : ℚ)
    (hOscillation :
      |pom_tower_defect_pinsker_bound_uniformExpectation g h ψ z -
          pom_tower_defect_pinsker_bound_sizeBiasedExpectation g h ψ z| ≤
        oscillation * tv)
    (hPinsker : tv ≤ pinskerScale)
    (hOscillationNonneg : 0 ≤ oscillation) :
    pom_tower_defect_pinsker_bound_towerDefect g h ψ z =
      pom_tower_defect_pinsker_bound_uniformExpectation g h ψ z -
        pom_tower_defect_pinsker_bound_sizeBiasedExpectation g h ψ z ∧
      pom_tower_defect_pinsker_bound_towerDefect g h ψ z =
        -towerDefectCovariance g h ψ z /
          towerFiberAverage h (fun y => (towerFiberCard g y : ℚ)) z ∧
      |pom_tower_defect_pinsker_bound_towerDefect g h ψ z| ≤ oscillation * tv ∧
      |pom_tower_defect_pinsker_bound_towerDefect g h ψ z| ≤ oscillation * pinskerScale := by
  have hCov :
      pom_tower_defect_pinsker_bound_towerDefect g h ψ z =
        -towerDefectCovariance g h ψ z /
          towerFiberAverage h (fun y => (towerFiberCard g y : ℚ)) z := by
    simpa [pom_tower_defect_pinsker_bound_towerDefect,
      pom_tower_defect_pinsker_bound_uniformExpectation,
      pom_tower_defect_pinsker_bound_sizeBiasedExpectation] using
      paper_pom_tower_defect_covariance_law g h ψ hg z hz
  have hTv :
      |pom_tower_defect_pinsker_bound_towerDefect g h ψ z| ≤ oscillation * tv := by
    simpa [pom_tower_defect_pinsker_bound_towerDefect,
      pom_tower_defect_pinsker_bound_uniformExpectation,
      pom_tower_defect_pinsker_bound_sizeBiasedExpectation] using hOscillation
  have hScale : oscillation * tv ≤ oscillation * pinskerScale := by
    exact mul_le_mul_of_nonneg_left hPinsker hOscillationNonneg
  exact ⟨rfl, hCov, hTv, le_trans hTv hScale⟩

end Omega.POM
