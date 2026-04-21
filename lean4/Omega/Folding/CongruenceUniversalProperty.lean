import Omega.Folding.MaxFiberTwoStep

namespace Omega

/-- Paper label: `thm:fold-congruence-universal-property`. -/
theorem paper_fold_congruence_universal_property {m : Nat} (Φ : Word m → X m) :
    ((∀ w, stableValue (Φ w) % Nat.fib (m + 2) = weight w % Nat.fib (m + 2)) →
      ∀ w, Φ w = Fold w) ∧
      ((∀ x : X m, Φ x.1 = x) →
        (∀ w, stableValue (Φ w) % Nat.fib (m + 2) = weight w % Nat.fib (m + 2)) →
          ∀ w, Φ w = Fold w) := by
  refine ⟨?_, ?_⟩
  · intro hCongr
    exact Fold_unique_of_weight_congr Φ hCongr
  · intro hRetract hCongr
    exact Fold_unique_of_retraction Φ hRetract hCongr

end Omega
