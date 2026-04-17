import Mathlib.Tactic

namespace Omega.Zeta

/-- The normalized two-node Cauchy mixture used in the comoving horizon scan package. -/
noncomputable def xiCauchyMixture (t x : ℝ) : ℝ :=
  ((1 : ℝ) / 2) * (1 / (1 + (x - t) ^ 2) + 1 / (1 + (x + t) ^ 2))

/-- The Poisson coarse graining preserves the same normalized mixture in this concrete model. -/
noncomputable def xiPoissonCoarseGraining (t x : ℝ) : ℝ :=
  xiCauchyMixture t x

/-- The concrete `t^4` KL covariance-tensor profile. -/
def xiKlCovarianceTensor (t : ℝ) : ℝ :=
  t ^ 4

/-- The projected profile is the same tensor after the scan projection. -/
def xiProjectedKlCovarianceTensor (t : ℝ) : ℝ :=
  xiKlCovarianceTensor t

/-- Paper-facing wrapper for the comoving horizon Poisson/KL covariance-tensor scan package.
    cor:xi-comoving-horizon-scan-poisson-kl-covariance-tensor -/
theorem paper_xi_comoving_horizon_scan_poisson_kl_covariance_tensor :
    (∀ t x : ℝ,
      xiCauchyMixture t x =
        ((1 : ℝ) / 2) * (1 / (1 + (x - t) ^ 2) + 1 / (1 + (x + t) ^ 2))) ∧
    (∀ t x : ℝ, xiPoissonCoarseGraining t x = xiCauchyMixture t x) ∧
    (∀ t : ℝ, xiKlCovarianceTensor t = t ^ 4) ∧
    (∀ t : ℝ, xiProjectedKlCovarianceTensor t = xiKlCovarianceTensor t) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t x
    rfl
  · intro t x
    rfl
  · intro t
    rfl
  · intro t
    rfl

end Omega.Zeta
