import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete three-cluster data for the Pick--Poisson coercive lower bound. The cross-cluster
interactions are already separated into the three unordered pairs. -/
structure PickPoissonClusteredQuadraticCoerciveData where
  kappa1 : ℝ
  kappa2 : ℝ
  kappa3 : ℝ
  rho0 : ℝ
  interaction12 : ℝ
  interaction13 : ℝ
  interaction23 : ℝ
  defectEntropy : ℝ
  hinteraction12 : rho0 * kappa1 * kappa2 ≤ interaction12
  hinteraction13 : rho0 * kappa1 * kappa3 ≤ interaction13
  hinteraction23 : rho0 * kappa2 * kappa3 ≤ interaction23
  hdefectEntropy :
    defectEntropy =
      (kappa1 ^ 2 + kappa2 ^ 2 + kappa3 ^ 2) +
        2 * (interaction12 + interaction13 + interaction23)

/-- Total defect count `κ`. -/
def clusteredTotalKappa (D : PickPoissonClusteredQuadraticCoerciveData) : ℝ :=
  D.kappa1 + D.kappa2 + D.kappa3

/-- Sum of the intra-cluster square terms. -/
def clusteredSumSquares (D : PickPoissonClusteredQuadraticCoerciveData) : ℝ :=
  D.kappa1 ^ 2 + D.kappa2 ^ 2 + D.kappa3 ^ 2

/-- Sum of the unordered cross-cluster products. -/
def clusteredPairMass (D : PickPoissonClusteredQuadraticCoerciveData) : ℝ :=
  D.kappa1 * D.kappa2 + D.kappa1 * D.kappa3 + D.kappa2 * D.kappa3

/-- Sum of the three cross-cluster interaction terms. -/
def clusteredInteractionSum (D : PickPoissonClusteredQuadraticCoerciveData) : ℝ :=
  D.interaction12 + D.interaction13 + D.interaction23

/-- Quadratic coercive lower bound obtained from the uniform `ρ₀` separation on the cross-cluster
terms. -/
def PickPoissonClusteredQuadraticCoerciveLowerBoundStatement
    (D : PickPoissonClusteredQuadraticCoerciveData) : Prop :=
  D.rho0 * (clusteredTotalKappa D) ^ 2 + (1 - D.rho0) * clusteredSumSquares D ≤ D.defectEntropy

lemma clustered_total_square_identity (D : PickPoissonClusteredQuadraticCoerciveData) :
    (clusteredTotalKappa D) ^ 2 = clusteredSumSquares D + 2 * clusteredPairMass D := by
  unfold clusteredTotalKappa clusteredSumSquares clusteredPairMass
  ring

/-- Paper label: `thm:derived-pick-poisson-clustered-quadratic-coercive-lower-bound`.
Expanding the defect entropy into intra-cluster and cross-cluster parts, bounding each cross term
by the uniform `ρ₀` separation estimate, and rewriting the pair sum as
`κ² - Σ κ_r²` yields the quadratic coercive lower bound. -/
theorem paper_derived_pick_poisson_clustered_quadratic_coercive_lower_bound
    (D : PickPoissonClusteredQuadraticCoerciveData) :
    PickPoissonClusteredQuadraticCoerciveLowerBoundStatement D := by
  unfold PickPoissonClusteredQuadraticCoerciveLowerBoundStatement
  have hpair :
      D.rho0 * clusteredPairMass D ≤ clusteredInteractionSum D := by
    unfold clusteredPairMass clusteredInteractionSum
    nlinarith [D.hinteraction12, D.hinteraction13, D.hinteraction23]
  calc
    D.rho0 * (clusteredTotalKappa D) ^ 2 + (1 - D.rho0) * clusteredSumSquares D
        = clusteredSumSquares D + 2 * (D.rho0 * clusteredPairMass D) := by
            rw [clustered_total_square_identity D]
            ring
    _ ≤ clusteredSumSquares D + 2 * clusteredInteractionSum D := by
          nlinarith [hpair]
    _ = D.defectEntropy := by
          simpa [clusteredSumSquares, clusteredInteractionSum] using D.hdefectEntropy.symm

end Omega.Zeta
