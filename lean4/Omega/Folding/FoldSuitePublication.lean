import Omega.Folding.FiberArithmetic

namespace Omega

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the basic properties of `Fold_m` in
    `submitted_2026_fibonacci_stabilization_sharp_threshold_conjugacy_nonlinearity`.
    thm:fold-suite -/
theorem paper_fibonacci_stabilization_fold_suite (m : Nat) :
    (∃ f : Word m → X m, ∀ x : X m, f x.1 = x) ∧
      Function.Surjective (Fold (m := m)) ∧
      (∑ x : X m, X.fiberMultiplicity x = 2 ^ m) := by
  refine ⟨⟨Fold, ?_⟩, Fold_surjective m, X.fiberMultiplicity_sum_eq_pow m⟩
  intro x
  simp

/-- Paper-label wrapper for `thm:fold-suite`. -/
theorem paper_fold_suite (m : Nat) :
    (∃ f : Word m → X m, ∀ x : X m, f x.1 = x) ∧
      Function.Surjective (Fold (m := m)) ∧
      (∑ x : X m, X.fiberMultiplicity x = 2 ^ m) := by
  refine ⟨⟨Fold, ?_⟩, Fold_surjective m, X.fiberMultiplicity_sum_eq_pow m⟩
  intro x
  simp

end Omega
