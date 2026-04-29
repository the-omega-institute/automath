import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part9xg-quadratic-sign-pair-cannot-recover-full-s3-type`. -/
theorem paper_xi_time_part9xg_quadratic_sign_pair_cannot_recover_full_s3_type {Split : Type}
    (split irreducible : Split) (condDensity : Split -> Bool -> Rat)
    (hsplit : ∀ eps, condDensity split eps = (1 : Rat) / 3)
    (hirred : ∀ eps, condDensity irreducible eps = (2 : Rat) / 3) :
    ∀ eps, condDensity split eps = (1 : Rat) / 3 ∧
      condDensity irreducible eps = (2 : Rat) / 3 := by
  intro eps
  exact ⟨hsplit eps, hirred eps⟩

end Omega.Zeta
