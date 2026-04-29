import Omega.Folding.FiberArithmeticProperties

namespace Omega

/-- Paper wrapper for the modular Zeckendorf decomposition uniqueness of `Fold`.
    thm:fold-zeckendorf-mod-decomposition-unique -/
theorem paper_fold_zeckendorf_mod_decomposition_unique (m : Nat) (w : Word m) :
    ∃! x : X m, stableValue x = weight w % Nat.fib (m + 2) := by
  refine ⟨Fold w, stableValue_Fold_mod w, ?_⟩
  intro x hx
  exact X.eq_of_stableValue_eq (hx.trans (stableValue_Fold_mod w).symm)

end Omega
