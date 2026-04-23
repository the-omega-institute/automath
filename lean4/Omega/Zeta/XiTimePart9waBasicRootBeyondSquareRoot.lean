import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part9wa-basic-root-beyond-square-root`. -/
theorem paper_xi_time_part9wa_basic_root_beyond_square_root (theta : Nat → Real)
    (hlim : ∀ eps > 0, ∃ m0, ∀ m ≥ m0, abs (theta m - 1) < eps) :
    ∃ m0, ∀ m ≥ m0, (1 : Real) / 2 < theta m := by
  rcases hlim ((1 : Real) / 2) (by norm_num) with ⟨m0, hm0⟩
  refine ⟨m0, ?_⟩
  intro m hm
  have hhalf : abs (theta m - 1) < (1 : Real) / 2 := hm0 m hm
  have hleft : -((1 : Real) / 2) < theta m - 1 := (abs_lt.mp hhalf).1
  linarith

end Omega.Zeta
