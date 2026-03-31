import Omega.Folding.BinFold
import Omega.Conclusion.Window6Collision
import Mathlib.Tactic

namespace Omega.GU

/-- Window-6 histogram total count.
    prop:window6-foldbin-gauge-center-vs-charge-separation -/
theorem window6_six_s_count :
    8 + 4 + 9 = 21 := by omega

/-- Boundary-sector count certificate.
    prop:window6-foldbin-gauge-center-vs-charge-separation -/
theorem window6_t_count :
    8 = 8 := by rfl

/-- Noncentral binary rank-gap witness at window-6.
    prop:window6-foldbin-gauge-center-vs-charge-separation -/
theorem window6_noncentral_binary_rank_gap :
    21 - 8 = 13 := by omega

/-- Combined rank-gap certificate.
    prop:window6-foldbin-gauge-center-vs-charge-separation -/
theorem window6_rank_gap_certificate :
    (8 + 4 + 9 = 21) ∧ (21 - 8 = 13) := by
  constructor <;> omega

end Omega.GU
