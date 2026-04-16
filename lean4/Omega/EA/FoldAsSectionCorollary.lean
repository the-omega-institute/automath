import Omega.Folding.Fiber

namespace Omega.EA

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: every finite Zeckendorf value class has a unique admissible representative,
    giving the finite-level section promised by the fold map.
    cor:fold-as-section -/
theorem paper_zeckendorf_fold_as_section_seeds (m : Nat) :
    ∀ n : Fin (Nat.fib (m + 2)), ∃! x : Omega.X m, Omega.X.stableValueFin x = n := by
  intro n
  rcases (Omega.X.paper_monoid_quotient_is_N m).2 n with ⟨x, hx⟩
  refine ⟨x, hx, ?_⟩
  intro y hy
  exact (Omega.X.paper_monoid_quotient_is_N m).1 (hy.trans hx.symm)

end Omega.EA
