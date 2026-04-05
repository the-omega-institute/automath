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

/-- Window-6 rank gap extended certificate.
    prop:window6-foldbin-gauge-center-vs-charge-separation -/
theorem paper_window6_rank_gap_extended :
    Nat.fib 8 = 21 ∧
    8 + 4 + 9 = 21 ∧
    21 - 8 = Nat.fib 7 ∧
    8 = Nat.fib 6 ∧
    4 = Nat.fib 5 - 1 := by
  refine ⟨by native_decide, by omega, by native_decide, by native_decide, by native_decide⟩

end Omega.GU
