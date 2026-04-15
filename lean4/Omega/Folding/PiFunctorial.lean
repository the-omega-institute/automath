import Omega.Folding.InverseLimit
import Omega.Folding.Defect

namespace Omega.Folding

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for admissible restriction functoriality in the
resolution-folding paper.
    lem:pi-functorial -/
theorem paper_resolution_folding_pi_functorial
    (h₁ : m ≤ ℓ) (h₂ : ℓ ≤ n) (x : Omega.X n) (a : Omega.X.XInfinity) :
    Omega.X.restrictLE h₁ (Omega.X.restrictLE h₂ x) =
      Omega.X.restrictLE (Nat.le_trans h₁ h₂) x ∧
      Omega.X.restrictLE h₁ (Omega.X.prefixWord a ℓ) =
        Omega.X.prefixWord a m := by
  refine ⟨Omega.X.restrict_functorial h₁ h₂ x, ?_⟩
  apply Subtype.ext
  funext i
  rfl

end Omega.Folding
