import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

/-- Paper label: `cor:gm-adjustable-moment-mean-square`.  The uniform gap threshold itself
serves as the admissible epsilon window, and the selector supplies the moment order. -/
theorem paper_gm_adjustable_moment_mean_square
    (opBound : Nat → Real → Prop) (epsilon0 : Real) (heps0 : 0 < epsilon0)
    (chooseMoment : ∀ ε : Real, 0 < ε → ε < epsilon0 → ∃ k : Nat, opBound k ε) :
    ∃ ε0 : Real, 0 < ε0 ∧ ∀ ε : Real, 0 < ε → ε < ε0 → ∃ k : Nat, opBound k ε := by
  exact ⟨epsilon0, heps0, chooseMoment⟩

end Omega.SyncKernelRealInput
