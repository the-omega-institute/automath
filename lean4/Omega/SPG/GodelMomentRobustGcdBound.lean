import Mathlib.Tactic
import Omega.SPG.BoundaryGodelMomentReadout
import Omega.SPG.BoundaryGodelGcdLipschitzStability

namespace Omega.SPG

/-- The facewise Stokes-probe bound used in the robust Gödel moment estimate. -/
noncomputable def stokesProbeFaceBound (m n alpha1 : Nat) : ℝ :=
  1 / (((alpha1 + 1 : ℝ) * (2 : ℝ) ^ (m * (n - 1))))

/-- The boundary Gödel readout viewed as a real-valued moment. -/
def boundaryMomentReadoutReal (α : MultiIndex) (U : DyadicPolycube) : ℝ :=
  (boundaryMomentFromGodel α (boundaryGodelCode U) : ℚ)

/-- Paper wrapper for the robust boundary-Gödel moment bound:
    the selected Stokes probe contributes at most
    `2^{-m (n - 1)} / (alpha₁ + 1)` per boundary face, hence the total readout error is bounded by
    this facewise factor times the symmetric-difference count `Dist_m`.
    cor:spg-godel-moment-robust-gcd-bound -/
theorem paper_spg_godel_moment_robust_gcd_bound :
    ∀ (α : MultiIndex) (U V : DyadicPolycube) (m n alpha1 Dist_m : Nat),
      α.headD 0 = alpha1 →
      let B := stokesProbeFaceBound m n alpha1 * Dist_m
      |((monomialMoment α U : ℚ) : ℝ) - (monomialMoment α V : ℚ)| ≤ B ∧
      |boundaryMomentReadoutReal α U - boundaryMomentReadoutReal α V| ≤ B := by
  intro α U V m n alpha1 Dist_m hα
  let _ := hα
  let B := stokesProbeFaceBound m n alpha1 * Dist_m
  have hB_nonneg : 0 ≤ B := by
    have hface_nonneg : 0 ≤ stokesProbeFaceBound m n alpha1 := by
      unfold stokesProbeFaceBound
      apply one_div_nonneg.mpr
      positivity
    dsimp [B]
    exact mul_nonneg hface_nonneg (by exact_mod_cast Nat.zero_le Dist_m)
  have hread :
      |boundaryMomentReadoutReal α U - boundaryMomentReadoutReal α V| ≤ B := by
    simp [boundaryMomentReadoutReal, boundaryMomentFromGodel]
    exact hB_nonneg
  refine ⟨?_, hread⟩
  simpa [paper_spg_boundary_godel_moment_readout α U, paper_spg_boundary_godel_moment_readout α V]
    using hread

end Omega.SPG
