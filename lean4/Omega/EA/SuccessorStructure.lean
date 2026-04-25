import Omega.Folding.FiberArithmeticProperties

namespace Omega.EA

open Omega

/-- Paper label: `thm:successor-structure`. Package the finite-resolution successor facts as the
paper-facing EA theorem. -/
theorem paper_successor_structure {m : ℕ} (hm : 1 ≤ m) :
    Omega.stableValue (Omega.X.stableZero (m := m)) = 0 ∧
      (∀ x : Omega.X m,
        Omega.stableValue (Omega.X.stableSucc x) = (Omega.stableValue x + 1) % Nat.fib (m + 2)) ∧
      Function.Bijective (Omega.X.stableSucc (m := m)) := by
  refine ⟨Omega.X.stableValue_stableZero, ?_, Omega.X.stableSucc_bijective m⟩
  intro x
  exact Omega.X.stableValue_stableSucc x hm

end Omega.EA
