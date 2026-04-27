import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-abelian-random-channel-negative-detection-lower-bound`. -/
theorem paper_xi_abelian_random_channel_negative_detection_lower_bound
    (M K N r L s : ℕ) (hL : L = (K + N) / (N + 1)) (hLs : L ≤ s) :
    Nat.choose (M - s) r ≤ Nat.choose (M - L) r := by
  subst L
  exact Nat.choose_le_choose r (tsub_le_tsub_left hLs M)

end Omega.Zeta
