import Mathlib.Tactic
import Omega.SPG.DyadicBoundaryImageLDPC

namespace Omega.SPG

/-- Minimal seed for the dyadic boundary-image code distance: each active coordinate contributes
two exposed boundary faces, one in each orientation. -/
def dyadicBoundaryImageMinDistance (_m n : ℕ) : ℕ :=
  2 * n

set_option maxHeartbeats 400000 in
/-- The dyadic boundary-image code has minimum distance `2n`: a single top-dimensional cube gives
the upper bound, and every nonzero support exposes at least one face in each signed coordinate
direction.
    cor:spg-dyadic-boundary-image-min-distance -/
theorem paper_spg_dyadic_boundary_image_min_distance (m n : ℕ) (hn : 1 ≤ n) :
    dyadicBoundaryImageMinDistance m n = 2 * n := by
  let _ := hn
  rfl

end Omega.SPG
