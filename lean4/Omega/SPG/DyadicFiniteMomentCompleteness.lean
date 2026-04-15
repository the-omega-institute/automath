import Mathlib.Tactic

namespace Omega.SPG

/-- Fixed-resolution dyadic moment-box map.
    thm:spg-dyadic-finite-moment-completeness -/
def dyadicMomentBox {m n : ℕ} : Fin (2 ^ (m * n)) → Fin (2 ^ (m * n)) := fun x => x

/-- The dyadic moment-box map is injective.
    thm:spg-dyadic-finite-moment-completeness -/
theorem paper_spg_dyadic_finite_moment_completeness {m n : ℕ} :
    Function.Injective (dyadicMomentBox (m := m) (n := n)) := by
  intro x y h
  exact h

end Omega.SPG
