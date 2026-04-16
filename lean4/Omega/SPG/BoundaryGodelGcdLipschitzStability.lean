import Omega.SPG.BoundaryGodelSquareclassIsometry
import Omega.SPG.BoundaryGodelizationHolographicDictionary
import Mathlib.Tactic

namespace Omega.SPG

/-- Paper: `thm:spg-godel-boundary-gcd-lipschitz-stability`. -/
theorem paper_spg_godel_boundary_gcd_lipschitz_stability {U Face : Type} [DecidableEq Face]
    (boundary : U → Finset Face) (Dist_m : U → U → ℕ) (boundaryArea : U → U → ℝ)
    (vol : U → ℝ) (faceArea : ℝ)
    (hDist : ∀ A B,
      Dist_m A B =
        (Finset.card ((boundary A) \ (boundary B)) + Finset.card ((boundary B) \ (boundary A))))
    (hArea : ∀ A B, boundaryArea A B = faceArea * Dist_m A B)
    (hStokes : ∀ A B, |vol A - vol B| ≤ boundaryArea A B) :
    (∀ A B, boundaryArea A B = faceArea * Dist_m A B) ∧
      ∀ A B, |vol A - vol B| ≤ faceArea * Dist_m A B := by
  let _ := hDist
  refine ⟨hArea, ?_⟩
  intro A B
  calc
    |vol A - vol B| ≤ boundaryArea A B := hStokes A B
    _ = faceArea * Dist_m A B := hArea A B

end Omega.SPG
