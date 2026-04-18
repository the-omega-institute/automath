import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The closed-form Pick--Poisson Schur flux coming from a point weight and a squared
pseudohyperbolic factor. -/
noncomputable def xiPickPoissonSchurFlux (pointWeight rho : ℝ) : ℝ :=
  pointWeight * rho ^ 2

/-- The determinant ratio obtained by dividing the `m` and `m - 1` factorizations. -/
noncomputable def xiPickPoissonDetRatio (detM detPrev : ℝ) : ℝ :=
  detM / detPrev

/-- The upper-half-plane factorization of the same Schur flux. -/
noncomputable def xiPickPoissonUpperHalfPlaneProduct (pointWeight rho : ℝ) : ℝ :=
  pointWeight * rho ^ 2

/-- Additive ledger form of the Schur flux. -/
noncomputable def xiPickPoissonNegLogFlux (pointWeight rho : ℝ) : ℝ :=
  -Real.log (xiPickPoissonSchurFlux pointWeight rho)

/-- Additive ledger contribution from the point weight. -/
noncomputable def xiPickPoissonNegLogPointWeight (pointWeight : ℝ) : ℝ :=
  -Real.log pointWeight

/-- Additive ledger contribution from a single upper-half-plane `ρ` term. -/
noncomputable def xiPickPoissonNegLogRhoSum (rho : ℝ) : ℝ :=
  -Real.log rho

/-- The Schur flux equals the determinant ratio, the explicit point-weight/rho product, the
upper-half-plane product, and its negative logarithm splits additively into the point-weight
ledger plus twice the `ρ` contribution.
    cor:xi-pick-poisson-schur-flux-closed-form -/
theorem paper_xi_pick_poisson_schur_flux_closed_form
    (detM detPrev pointWeight rho : ℝ)
    (hdetPrev : detPrev ≠ 0)
    (hfactor : detM = pointWeight * rho ^ 2 * detPrev)
    (hpoint : 0 < pointWeight) (hrho : 0 < rho) :
    xiPickPoissonSchurFlux pointWeight rho = xiPickPoissonDetRatio detM detPrev ∧
      xiPickPoissonSchurFlux pointWeight rho = pointWeight * rho ^ 2 ∧
      xiPickPoissonSchurFlux pointWeight rho =
        xiPickPoissonUpperHalfPlaneProduct pointWeight rho ∧
      xiPickPoissonNegLogFlux pointWeight rho =
        xiPickPoissonNegLogPointWeight pointWeight + 2 * xiPickPoissonNegLogRhoSum rho := by
  have hratio : xiPickPoissonDetRatio detM detPrev = pointWeight * rho ^ 2 := by
    unfold xiPickPoissonDetRatio
    rw [hfactor]
    field_simp [hdetPrev]
  have hlog :
      xiPickPoissonNegLogFlux pointWeight rho =
        xiPickPoissonNegLogPointWeight pointWeight + 2 * xiPickPoissonNegLogRhoSum rho := by
    have hrho_ne : rho ≠ 0 := ne_of_gt hrho
    unfold xiPickPoissonNegLogFlux xiPickPoissonNegLogPointWeight
      xiPickPoissonNegLogRhoSum xiPickPoissonSchurFlux
    rw [Real.log_mul (ne_of_gt hpoint) (pow_ne_zero 2 hrho_ne)]
    rw [show rho ^ 2 = rho * rho by ring, Real.log_mul hrho_ne hrho_ne]
    ring
  refine ⟨by simpa [xiPickPoissonSchurFlux] using hratio.symm, rfl, rfl, hlog⟩

end Omega.Zeta
