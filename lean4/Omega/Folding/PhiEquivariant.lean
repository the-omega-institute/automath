import Omega.Folding.Fold
import Omega.Folding.PhiSlidingBlockCode

namespace Omega.Folding.PhiEquivariant

open Omega

/-- The sliding block code induced by `Fold` commutes with the shift. -/
theorem paper_fold_phi_equivariant_seeds (m : ℕ) (s : ℤ → Bool) :
    Folding.slideBlockCode m (Fold (m := m)) (Folding.shiftSeq s) =
      Folding.shiftSeq (Folding.slideBlockCode m (Fold (m := m)) s) :=
  Folding.slideBlockCode_shift_equivariant m (Fold (m := m)) s

/-- Wrapper theorem matching the paper-facing package name. -/
theorem paper_fold_phi_equivariant_package (m : ℕ) (s : ℤ → Bool) :
    Folding.slideBlockCode m (Fold (m := m)) (Folding.shiftSeq s) =
      Folding.shiftSeq (Folding.slideBlockCode m (Fold (m := m)) s) :=
  paper_fold_phi_equivariant_seeds m s

end Omega.Folding.PhiEquivariant
