import Omega.Folding.InverseLimit

namespace Omega.Folding.NaivePrefixLift

open Omega

/-- A compatible family in the restriction inverse system determines an inverse-limit point whose
finite prefixes recover the family. -/
theorem paper_fold_naive_prefix_lift_seeds
    (x : ∀ m : ℕ, X m)
    (h : ∀ m, X.restrict (x (m + 1)) = x m) :
    ∃ xInf : X.XInfinity, ∀ m, X.prefixWord xInf m = x m := by
  let F : X.CompatibleFamily := ⟨x, h⟩
  refine ⟨X.ofFamily F, ?_⟩
  intro m
  simpa [F, X.toFamily] using X.toFamily_ofFamily_seq F m

/-- Wrapper theorem matching the paper-facing package name. -/
theorem paper_fold_naive_prefix_lift_package
    (x : ∀ m : ℕ, X m)
    (h : ∀ m, X.restrict (x (m + 1)) = x m) :
    ∃ xInf : X.XInfinity, ∀ m, X.prefixWord xInf m = x m :=
  paper_fold_naive_prefix_lift_seeds x h

end Omega.Folding.NaivePrefixLift
