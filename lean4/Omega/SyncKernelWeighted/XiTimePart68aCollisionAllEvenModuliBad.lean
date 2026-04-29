import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- Paper label: `thm:xi-time-part68a-collision-all-even-moduli-bad`. -/
theorem paper_xi_time_part68a_collision_all_even_moduli_bad
    (rhoW : Int → Real) (phi : Real) (hminus : phi < rhoW (-1)) :
    ∀ m : Nat, 2 ≤ m → Even m → ∃ j : Nat, 1 ≤ j ∧ j ≤ m - 1 ∧ phi < rhoW (-1) := by
  intro m hm hEven
  rcases hEven with ⟨j, hj⟩
  subst m
  refine ⟨j, ?_, ?_, hminus⟩
  · omega
  · omega

end Omega.SyncKernelWeighted
