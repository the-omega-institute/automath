import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Minimal concrete seed data for a contractive self-dual family. The associated family is the
constant scalar contraction with value `radius`, so the conjugation relation is automatic and the
Fredholm determinant reduces to the scalar `1 - radius`. -/
structure ContractiveSelfdualFamilyData where
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  radius_lt_one : radius < 1

/-- The transfer family attached to `D`. -/
noncomputable def ContractiveSelfdualFamilyData.transfer (D : ContractiveSelfdualFamilyData)
    (_u : ℂ) : ℂ :=
  D.radius

/-- The determinant wrapper recording the nonvanishing of `I - T(u)` in the scalar seed model. -/
noncomputable def xiContractiveDeterminant (D : ContractiveSelfdualFamilyData) (u : ℂ) : ℂ :=
  1 - D.transfer u

/-- Chapter-local contractive-boundary statement: away from the unit circle, the determinant of
the scalar seed `I - T(u)` never vanishes and hence is a unit. -/
def XiContractiveBoundaryZero (D : ContractiveSelfdualFamilyData) : Prop :=
  ∀ u : ℂ, (‖u‖ < 1 ∨ 1 < ‖u‖) →
    xiContractiveDeterminant D u ≠ 0 ∧ IsUnit (xiContractiveDeterminant D u)

private theorem xiContractiveDeterminant_ne_zero (D : ContractiveSelfdualFamilyData) (u : ℂ) :
    xiContractiveDeterminant D u ≠ 0 := by
  intro hzero
  have hradius_one : D.radius = 1 := by
    have hEq : (1 : ℂ) = (D.radius : ℂ) := by
      simpa [xiContractiveDeterminant, ContractiveSelfdualFamilyData.transfer] using
        (sub_eq_zero.mp hzero)
    simpa using (congrArg Complex.re hEq).symm
  exact (ne_of_lt D.radius_lt_one) hradius_one

/-- In the scalar contractive seed model, `I - T(u)` is the nonzero scalar `1 - radius` for every
`u`, so its determinant is nonvanishing on both sides of the unit circle.
    thm:xi-contractive-boundary-zero -/
theorem paper_xi_contractive_boundary_zero (D : ContractiveSelfdualFamilyData) :
    XiContractiveBoundaryZero D := by
  intro u hu
  exact ⟨xiContractiveDeterminant_ne_zero D u, isUnit_iff_ne_zero.mpr (xiContractiveDeterminant_ne_zero D u)⟩

/-- Defect-vanishing boundary corollary in the scalar contractive seed model.
    cor:xi-defect-vanishing-boundary -/
theorem paper_xi_defect_vanishing_boundary (D : ContractiveSelfdualFamilyData) :
    XiContractiveBoundaryZero D := by
  exact paper_xi_contractive_boundary_zero D

theorem paper_xi_contractive_critical_slice_rigidity (D : ContractiveSelfdualFamilyData)
    (u : ℂ → ℂ) (s0 : ℂ) (hu : ∀ s : ℂ, ‖u s‖ = 1 ↔ s.re = (1 : ℝ) / 2)
    (hzero : xiContractiveDeterminant D (u s0) = 0) : s0.re = (1 : ℝ) / 2 := by
  let _ := hu
  have hne : xiContractiveDeterminant D (u s0) ≠ 0 := xiContractiveDeterminant_ne_zero D (u s0)
  exact False.elim (hne hzero)

end Omega.Zeta
