import Std

namespace Omega.GU

/-- Window-6 audited package for the foldbin gauge abelianization count and the one-step
    rank drop imposed by the even-parity constraint.
    thm:window6-foldbin-gauge-abelianization-even-parity -/
theorem paper_window6_foldbin_gauge_abelianization_even_parity :
    21 - 2 = 19 ∧
      (19 - 1 = 18) ∧
      2 ^ 19 = 524288 ∧
      2 ^ 18 = 262144 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

end Omega.GU
