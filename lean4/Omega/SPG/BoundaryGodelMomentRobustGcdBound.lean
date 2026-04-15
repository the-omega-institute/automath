import Omega.SPG.BoundaryGodelMomentReadout
import Omega.SPG.BoundaryGodelGcdLipschitzStability
import Mathlib.Tactic

namespace Omega.SPG

/-- Paper-facing robust moment bound: rewrite bulk monomial moments through the boundary Gödel
    readout and apply the boundary `gcd`-Lipschitz wrapper with the explicit face area
    `2^{-m(n-1)} / (α₁ + 1)`.
    cor:spg-godel-moment-robust-gcd-bound -/
theorem paper_spg_godel_moment_robust_gcd_bound
    (α : MultiIndex) (Dist_m : DyadicPolycube → DyadicPolycube → ℕ) (α1 m n : ℕ)
    (hDist : ∀ A B,
      Dist_m A B =
        (Finset.card ((boundaryGodelCode A) \ (boundaryGodelCode B)) +
          Finset.card ((boundaryGodelCode B) \ (boundaryGodelCode A))))
    (hStokes :
      ∀ A B,
        abs ((((boundaryMomentFromGodel α (boundaryGodelCode A) : ℚ) : ℝ) -
          (((boundaryMomentFromGodel α (boundaryGodelCode B) : ℚ) : ℝ)))) ≤
          (((2 : ℝ) ^ (m * (n - 1)))⁻¹ / ((α1 : ℝ) + 1)) * Dist_m A B) :
    ∀ U V,
      abs ((((monomialMoment α U : ℚ) : ℝ) - (((monomialMoment α V : ℚ) : ℝ)))) ≤
        (((2 : ℝ) ^ (m * (n - 1)))⁻¹ / ((α1 : ℝ) + 1)) * Dist_m U V := by
  intro U V
  let faceArea : ℝ := ((2 : ℝ) ^ (m * (n - 1)))⁻¹ / ((α1 : ℝ) + 1)
  have hLipPackage :=
    paper_spg_godel_boundary_gcd_lipschitz_stability
      (boundary := boundaryGodelCode)
      (Dist_m := Dist_m)
      (boundaryArea := fun A B => faceArea * Dist_m A B)
      (vol := fun A => (((boundaryMomentFromGodel α (boundaryGodelCode A) : ℚ) : ℝ)))
      (faceArea := faceArea)
      hDist
      (fun _ _ => rfl)
      hStokes
  rcases hLipPackage with ⟨_, hLip⟩
  cases U
  cases V
  simpa [faceArea] using hLip () ()

end Omega.SPG
