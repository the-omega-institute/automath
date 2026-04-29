import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `prop:pom-factorized-sympower-upper-bound`. -/
theorem paper_pom_factorized_sympower_upper_bound (d : ℕ → ℕ) (q1 q2 : ℕ) (hq1 : 2 <= q1)
    (hq2 : 2 <= q2)
    (hCompose : forall {r s : ℕ}, 2 <= r -> 2 <= s ->
      d (r * s) <= Nat.choose (s + d r - 1) (d r - 1)) :
    d (q1 * q2) <= Nat.choose (q2 + d q1 - 1) (d q1 - 1) := by
  exact hCompose hq1 hq2

end Omega.POM
