import Omega.POM.DiagonalRateScalarCollapse

namespace Omega.POM

noncomputable section

open scoped BigOperators
open Finset
open DiagonalRateScalarCollapseData

/-- Concrete statement for `cor:pom-diagonal-rate-scalar-collapse-rate`. The existing
scalar-collapse package gives the unique fixed point, the distortion bijection, the mass identity
`1 = A^2 + κ \sum_x u(x)^2`, and the algebraic recovery formula obtained by eliminating the
quadratic mass term after defining `δ := A^2 - (1 - A^2) / κ`. -/
def paper_pom_diagonal_rate_scalar_collapse_rate_statement
    (D : DiagonalRateScalarCollapseData) : Prop :=
  D.uniqueFixedPointPackage ∧
    D.kappaDistortionBijection ∧
    (1 = D.A ^ 2 + D.κ * ∑ x, (D.root D.A x) ^ 2) ∧
    let δ : ℝ := D.A ^ 2 - (1 - D.A ^ 2) / D.κ
    D.κ = (1 - D.A ^ 2) / (D.A ^ 2 - δ)

theorem pom_diagonal_rate_scalar_collapse_rate_mass_identity
    (D : DiagonalRateScalarCollapseData) :
    1 = D.A ^ 2 + D.κ * ∑ x, (D.root D.A x) ^ 2 := by
  have hMass : ∑ x, ∑ y, D.coupling x y = 1 := D.total_mass_eq_one
  have hRows :
      ∀ x, ∑ y, D.coupling x y = D.A * D.root D.A x + D.κ * (D.root D.A x) ^ 2 := by
    intro x
    calc
      ∑ y, D.coupling x y = D.w x := D.row_sum_eq_weight x
      _ = D.A * D.root D.A x + D.κ * (D.root D.A x) ^ 2 := by
        symm
        simpa [mul_comm] using D.root_quadratic_identity x
  have hRootSum : ∑ x, D.root D.A x = D.A := by
    simpa [fixedPointMap] using D.fixedPointMap_eq_sum_root
  calc
    1 = ∑ x, (D.A * D.root D.A x + D.κ * (D.root D.A x) ^ 2) := by
      simpa [hRows] using hMass.symm
    _ = ∑ x, D.A * D.root D.A x + ∑ x, D.κ * (D.root D.A x) ^ 2 := by
      rw [sum_add_distrib]
    _ = D.A * ∑ x, D.root D.A x + D.κ * ∑ x, (D.root D.A x) ^ 2 := by
      rw [mul_sum, mul_sum]
    _ = D.A * D.A + D.κ * ∑ x, (D.root D.A x) ^ 2 := by rw [hRootSum]
    _ = D.A ^ 2 + D.κ * ∑ x, (D.root D.A x) ^ 2 := by ring

theorem pom_diagonal_rate_scalar_collapse_rate_recover_kappa
    (D : DiagonalRateScalarCollapseData) :
    let δ : ℝ := D.A ^ 2 - (1 - D.A ^ 2) / D.κ
    D.κ = (1 - D.A ^ 2) / (D.A ^ 2 - δ) := by
  have hκ_ne : (D.κ : ℝ) ≠ 0 := by
    linarith [D.hκ]
  have hA_sq_lt_one : D.A ^ 2 < 1 := by
    nlinarith [D.hA_pos, D.hA_lt_one]
  have hOneSub_ne : (1 - D.A ^ 2 : ℝ) ≠ 0 := by
    linarith
  dsimp
  field_simp [hκ_ne, hOneSub_ne]
  ring

/-- Paper label: `cor:pom-diagonal-rate-scalar-collapse-rate`. The scalar-collapse package already
contains the unique fixed point and distortion bijection, while the summed row identities recover
the explicit one-parameter algebraic formula for `κ`. -/
theorem paper_pom_diagonal_rate_scalar_collapse_rate_holds
    (D : DiagonalRateScalarCollapseData) :
    paper_pom_diagonal_rate_scalar_collapse_rate_statement D := by
  rcases paper_pom_diagonal_rate_scalar_collapse D with ⟨hFixed, hBijection⟩
  exact ⟨hFixed, hBijection, pom_diagonal_rate_scalar_collapse_rate_mass_identity D,
    pom_diagonal_rate_scalar_collapse_rate_recover_kappa D⟩

/-- Exported paper-facing proposition for `cor:pom-diagonal-rate-scalar-collapse-rate`. -/
def paper_pom_diagonal_rate_scalar_collapse_rate
    (D : DiagonalRateScalarCollapseData) : Prop := by
  exact paper_pom_diagonal_rate_scalar_collapse_rate_statement D

end

end Omega.POM
